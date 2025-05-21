/**
 *
 * Reference ISO-C11 Implementation of CROSS.
 *
 * @version 2.0 (February 2025)
 *
 * Authors listed in alphabetical order:
 *
 * @author: Alessandro Barenghi <alessandro.barenghi@polimi.it>
 * @author: Marco Gianvecchio <marco.gianvecchio@mail.polimi.it>
 * @author: Patrick Karl <patrick.karl@tum.de>
 * @author: Gerardo Pelosi <gerardo.pelosi@polimi.it>
 * @author: Jonas Schupp <jonas.schupp@tum.de>
 *
 *
 * This code is hereby placed in the public domain.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS ''AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHORS OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 **/

#pragma once

#ifndef CSPRNG_HASH_H
#define CSPRNG_HASH_H

#include "parameters.h"
#include "sha3.h"

/************************* CSPRNG ********************************/

#define CSPRNG_STATE_T SHAKE_STATE_STRUCT
/* initializes a CSPRNG, given the seed and a state pointer */
static inline void csprng_initialize(CSPRNG_STATE_T *const csprng_state,
                                     const unsigned char *const seed,
                                     const uint32_t seed_len_bytes,
                                     const uint16_t dsc) {
  // the second parameter is the security level of the SHAKE instance
  xof_shake_init(csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update(csprng_state, seed, seed_len_bytes);
  uint8_t dsc_ordered[2];
  dsc_ordered[0] = dsc & 0xff;
  dsc_ordered[1] = (dsc >> 8) & 0xff;
  xof_shake_update(csprng_state, dsc_ordered, 2);
  xof_shake_final(csprng_state);
} /* end initialize_csprng */

/* extracts xlen bytes from the CSPRNG, given the state */
static inline void csprng_randombytes(unsigned char *const x,
                                      unsigned long long xlen,
                                      CSPRNG_STATE_T *const csprng_state) {
  xof_shake_extract(csprng_state, x, xlen);
}

/******************************************************************************/

/* global csprng state employed to have deterministic randombytes for testing */
extern CSPRNG_STATE_T platform_csprng_state;
/* extracts xlen bytes from the global CSPRNG */
static inline void randombytes(unsigned char *x, unsigned long long xlen) {
  csprng_randombytes(x, xlen, &platform_csprng_state);
}

/************************* HASH functions ********************************/

/* Opaque algorithm agnostic hash call */
static inline void hash(uint8_t digest[HASH_DIGEST_LENGTH],
                        const unsigned char *const m, const uint64_t mlen,
                        const uint16_t dsc) {
  /* SHAKE with a 2*lambda bit digest is employed also for hashing */
  CSPRNG_STATE_T csprng_state;
  xof_shake_init(&csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update(&csprng_state, m, mlen);
  uint8_t dsc_ordered[2];
  dsc_ordered[0] = dsc & 0xff;
  dsc_ordered[1] = (dsc >> 8) & 0xff;
  xof_shake_update(&csprng_state, dsc_ordered, 2);
  xof_shake_final(&csprng_state);
  xof_shake_extract(&csprng_state, digest, HASH_DIGEST_LENGTH);
}

/***************** Specialized CSPRNGs for non binary domains *****************/

/* CSPRNG sampling fixed weight strings */
void expand_digest_to_fixed_weight(uint8_t fixed_weight_string[T],
                                   const uint8_t digest[HASH_DIGEST_LENGTH]);

#define BITS_FOR_P BITS_TO_REPRESENT(P - 1)
#define BITS_FOR_Z BITS_TO_REPRESENT(Z - 1)

static inline void csprng_fp_vec(FP_ELEM res[N],
                                 CSPRNG_STATE_T *const csprng_state) {
  const FP_ELEM mask = ((FP_ELEM)1 << BITS_FOR_P) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_N_FP_CT_RNG, 8) / 8];
  /* To facilitate hardware implementations, the uint64_t
   * sub-buffer is consumed starting from the least significant byte
   * i.e., from the first being output by SHAKE. Bits in the byte are
   * discarded shifting them out to the right, shifting fresh ones
   * in from the left end */
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), csprng_state);
  int placed = 0;
  uint64_t sub_buffer = 0;
  for (int i = 0; i < 8; i++) {
    sub_buffer |= ((uint64_t)CSPRNG_buffer[i]) << 8 * i;
  }
  /* position of the next fresh byte in CSPRNG_buffer*/
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  int pos_remaining = sizeof(CSPRNG_buffer) - pos_in_buf;
  while (placed < N) {
    if (bits_in_sub_buf <= 32 && pos_remaining > 0) {
      /* get at most 4 bytes from buffer */
      int refresh_amount = (pos_remaining >= 4) ? 4 : pos_remaining;
      uint32_t refresh_buf = 0;
      for (int i = 0; i < refresh_amount; i++) {
        refresh_buf |= ((uint32_t)CSPRNG_buffer[pos_in_buf + i]) << 8 * i;
      }
      pos_in_buf += refresh_amount;
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      bits_in_sub_buf += 8 * refresh_amount;
      pos_remaining -= refresh_amount;
    }
    res[placed] = sub_buffer & mask;
    if (res[placed] < P) {
      placed++;
    }
    sub_buffer = sub_buffer >> BITS_FOR_P;
    bits_in_sub_buf -= BITS_FOR_P;
  }
}

#define BITS_FOR_P_M_ONE BITS_TO_REPRESENT(P - 2)

static inline void csprng_fp_vec_chall_1(FP_ELEM res[T],
                                         CSPRNG_STATE_T *const csprng_state) {
  const FP_ELEM mask = ((FP_ELEM)1 << BITS_FOR_P_M_ONE) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_CHALL_1_FPSTAR_CT_RNG, 8) / 8];
  /* To facilitate hardware implementations, the uint64_t
   * sub-buffer is consumed starting from the least significant byte
   * i.e., from the first being output by SHAKE. Bits in the byte are
   * discarded shifting them out to the right , shifting fresh ones
   * in from the left end */
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), csprng_state);
  int placed = 0;
  uint64_t sub_buffer = 0;
  for (int i = 0; i < 8; i++) {
    sub_buffer |= ((uint64_t)CSPRNG_buffer[i]) << 8 * i;
  }
  /* position of the next fresh byte in CSPRNG_buffer*/
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  int pos_remaining = sizeof(CSPRNG_buffer) - pos_in_buf;
  while (placed < T) {
    if (bits_in_sub_buf <= 32 && pos_remaining > 0) {
      /* get at most 4 bytes from buffer */
      int refresh_amount = (pos_remaining >= 4) ? 4 : pos_remaining;
      uint32_t refresh_buf = 0;
      for (int i = 0; i < refresh_amount; i++) {
        refresh_buf |= ((uint32_t)CSPRNG_buffer[pos_in_buf + i]) << 8 * i;
      }
      pos_in_buf += refresh_amount;
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      bits_in_sub_buf += 8 * refresh_amount;
      pos_remaining -= refresh_amount;
    }
    /* draw from 0 ... P-2, then add 1*/
    res[placed] = (sub_buffer & mask) + 1;
    if (res[placed] < P) {
      placed++;
    }
    sub_buffer = sub_buffer >> BITS_FOR_P_M_ONE;
    bits_in_sub_buf -= BITS_FOR_P_M_ONE;
  }
}

/*
 * CSPRNG-F_p^{(n-k) x k}
 * The same rejection sampling approach employed to generate multiple elements
 * of F_z is also employed to generate multiple elements of F_p, with the only
 * difference being that the sequence of bits extracted from SHAKE at every
 * attempt to generate an element of F_p is ceil(log_2(p)) bits long.
 *
 * Used for:
 * - Expanding the public key from seed
 */
#if defined(OPT_DSP)
// Column major for DSP
static inline void csprng_fp_mat(FP_ELEM res[N - K][K],
                                 CSPRNG_STATE_T *const csprng_state) {
#else
static inline void csprng_fp_mat(FP_ELEM res[K][N - K],
                                 CSPRNG_STATE_T *const csprng_state) {
#endif
  const FP_ELEM mask = ((FP_ELEM)1 << BITS_TO_REPRESENT(P - 1)) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_V_CT_RNG, 8) / 8];
  /* To facilitate hardware implementations, the uint64_t
   * sub-buffer is consumed starting from the least significant byte
   * i.e., from the first being output by SHAKE. Bits in the byte are
   * discarded shifting them out to the right , shifting fresh ones
   * in from the left end */
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), csprng_state);
#if !defined(OPT_DSP)
  int placed = 0;
#endif
  // Our "window" into the random buffer, 8 bytes at a time
  uint64_t sub_buffer = 0;
  for (int i = 0; i < 8; i++) {
    sub_buffer |= ((uint64_t)CSPRNG_buffer[i]) << 8 * i;
  }
  /* position of the next fresh byte in CSPRNG_buffer*/
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  // Remaining bits of randomness left
  int pos_remaining = sizeof(CSPRNG_buffer) - pos_in_buf;
// Size of the matrix
#if defined(OPT_DSP)
  for (int r = 0; r < K; r++) {
    for (int c = 0; c < N - K; c++) {
#else
  while (placed < K * (N - K)) {
#endif
      // If we have less than half left in window and
      // some remaining in random buffer
      if (bits_in_sub_buf <= 32 && pos_remaining > 0) {
        /* get at most 4 bytes from buffer */
        int refresh_amount = (pos_remaining >= 4) ? 4 : pos_remaining;
        // Make refresh window
        uint32_t refresh_buf = 0;
        for (int i = 0; i < refresh_amount; i++) {
          refresh_buf |= ((uint32_t)CSPRNG_buffer[pos_in_buf + i]) << 8 * i;
        }
        // Increment random buffer counter
        pos_in_buf += refresh_amount;
        // Put refresh bits into main window
        sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
        // Add amount of bits refreshed
        bits_in_sub_buf += 8 * refresh_amount;
        // Decrement remaining counter for random buffer
        pos_remaining -= refresh_amount;
      }
      // Temporarily place value (may be overwritten)
#if defined(OPT_DSP)
      res[c][r] = sub_buffer & mask;
#else
    *((FP_ELEM *)res + placed) = sub_buffer & mask;
#endif
      // Check if the value is in the field
#if defined(OPT_DSP)
      if (res[c][r] >= P) {
        // If it isn't, go back one
        c -= 1;
      }
#else
    if (*((FP_ELEM *)res + placed) < P) {
      // If it is, keep it
      placed++;
    }
#endif
      // Shift window to the right
      sub_buffer = sub_buffer >> BITS_FOR_P;
      // Keep track of how many bits left in window
      bits_in_sub_buf -= BITS_FOR_P;
    }
#if defined(OPT_DSP)
  }
#endif
}

static inline void csprng_fp_mat_check(FP_ELEM res[K][N - K],
                                       CSPRNG_STATE_T *const csprng_state) {
  const FP_ELEM mask = ((FP_ELEM)1 << BITS_TO_REPRESENT(P - 1)) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_V_CT_RNG, 8) / 8];
  /* To facilitate hardware implementations, the uint64_t
   * sub-buffer is consumed starting from the least significant byte
   * i.e., from the first being output by SHAKE. Bits in the byte are
   * discarded shifting them out to the right , shifting fresh ones
   * in from the left end */
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), csprng_state);
  int placed = 0;
  // Our "window" into the random buffer, 8 bytes at a time
  uint64_t sub_buffer = 0;
  for (int i = 0; i < 8; i++) {
    sub_buffer |= ((uint64_t)CSPRNG_buffer[i]) << 8 * i;
  }
  /* position of the next fresh byte in CSPRNG_buffer*/
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  // Remaining bits of randomness left
  int pos_remaining = sizeof(CSPRNG_buffer) - pos_in_buf;
  // Size of the matrix
  while (placed < K * (N - K)) {
    // If we have less than half left in window and
    // some remaining in random buffer
    if (bits_in_sub_buf <= 32 && pos_remaining > 0) {
      /* get at most 4 bytes from buffer */
      int refresh_amount = (pos_remaining >= 4) ? 4 : pos_remaining;
      // Make refresh window
      uint32_t refresh_buf = 0;
      for (int i = 0; i < refresh_amount; i++) {
        refresh_buf |= ((uint32_t)CSPRNG_buffer[pos_in_buf + i]) << 8 * i;
      }
      // Increment random buffer counter
      pos_in_buf += refresh_amount;
      // Put refresh bits into main window
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      // Add amount of bits refreshed
      bits_in_sub_buf += 8 * refresh_amount;
      // Decrement remaining counter for random buffer
      pos_remaining -= refresh_amount;
    }
    // Temporarily place value (may be overwritten)
    *((FP_ELEM *)res + placed) = sub_buffer & mask;
    // Check if the value is in the field
    if (*((FP_ELEM *)res + placed) < P) {
      // If it is, keep it
      placed++;
    }
    // Shift window to the right
    sub_buffer = sub_buffer >> BITS_FOR_P;
    // Keep track of how many bits left in window
    bits_in_sub_buf -= BITS_FOR_P;
  }
}

#if defined(RSDP)
static inline void csprng_fz_vec(FZ_ELEM res[N],
                                 CSPRNG_STATE_T *const csprng_state) {
  const FZ_ELEM mask = ((FZ_ELEM)1 << BITS_TO_REPRESENT(Z - 1)) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_N_FZ_CT_RNG, 8) / 8];
  /* To facilitate hardware implementations, the uint64_t
   * sub-buffer is consumed starting from the least significant byte
   * i.e., from the first being output by SHAKE. Bits in the byte are
   * discarded shifting them out to the right , shifting fresh ones
   * in from the left end */
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), csprng_state);
  int placed = 0;
  uint64_t sub_buffer = 0;
  for (int i = 0; i < 8; i++) {
    sub_buffer |= ((uint64_t)CSPRNG_buffer[i]) << 8 * i;
  }
  /* position of the next fresh byte in CSPRNG_buffer*/
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  int pos_remaining = sizeof(CSPRNG_buffer) - pos_in_buf;
  while (placed < N) {
    if (bits_in_sub_buf <= 32 && pos_remaining > 0) {
      /* get at most 4 bytes from buffer */
      int refresh_amount = (pos_remaining >= 4) ? 4 : pos_remaining;
      uint32_t refresh_buf = 0;
      for (int i = 0; i < refresh_amount; i++) {
        refresh_buf |= ((uint32_t)CSPRNG_buffer[pos_in_buf + i]) << 8 * i;
      }
      pos_in_buf += refresh_amount;
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      bits_in_sub_buf += 8 * refresh_amount;
      pos_remaining -= refresh_amount;
    }
    res[placed] = sub_buffer & mask;
    if (res[placed] < Z) {
      placed++;
    }
    sub_buffer = sub_buffer >> BITS_FOR_Z;
    bits_in_sub_buf -= BITS_FOR_Z;
  }
}
#elif defined(RSDPG)
static inline void csprng_fz_inf_w(FZ_ELEM res[RSDPG_M],
                                   CSPRNG_STATE_T *const csprng_state) {
  const FZ_ELEM mask = ((FZ_ELEM)1 << BITS_TO_REPRESENT(Z - 1)) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_M_FZ_CT_RNG, 8) / 8];
  /* To facilitate hardware implementations, the uint64_t
   * sub-buffer is consumed starting from the least significant byte
   * i.e., from the first being output by SHAKE. Bits in the byte are
   * discarded shifting them out to the right , shifting fresh ones
   * in from the left end */
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), csprng_state);
  int placed = 0;
  uint64_t sub_buffer = 0;
  for (int i = 0; i < 8; i++) {
    sub_buffer |= ((uint64_t)CSPRNG_buffer[i]) << 8 * i;
  }
  /* position of the next fresh byte in CSPRNG_buffer*/
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  int pos_remaining = sizeof(CSPRNG_buffer) - pos_in_buf;
  while (placed < RSDPG_M) {
    if (bits_in_sub_buf <= 32 && pos_remaining > 0) {
      /* get at most 4 bytes from buffer */
      int refresh_amount = (pos_remaining >= 4) ? 4 : pos_remaining;
      uint32_t refresh_buf = 0;
      for (int i = 0; i < refresh_amount; i++) {
        refresh_buf |= ((uint32_t)CSPRNG_buffer[pos_in_buf + i]) << 8 * i;
      }
      pos_in_buf += refresh_amount;
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      bits_in_sub_buf += 8 * refresh_amount;
      pos_remaining -= refresh_amount;
    }
    res[placed] = sub_buffer & mask;
    if (res[placed] < Z) {
      placed++;
    }
    sub_buffer = sub_buffer >> BITS_FOR_Z;
    bits_in_sub_buf -= BITS_FOR_Z;
  }
}

static inline void csprng_fz_mat(FZ_ELEM res[RSDPG_M][N - RSDPG_M],
                                 CSPRNG_STATE_T *const csprng_state) {
  const FZ_ELEM mask = ((FZ_ELEM)1 << BITS_TO_REPRESENT(Z - 1)) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_W_CT_RNG, 8) / 8];
  /* To facilitate hardware implementations, the uint64_t
   * sub-buffer is consumed starting from the least significant byte
   * i.e., from the first being output by SHAKE. Bits in the byte are
   * discarded shifting them out to the right , shifting fresh ones
   * in from the left end */
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), csprng_state);

  int placed = 0;
  uint64_t sub_buffer = 0;
  for (int i = 0; i < 8; i++) {
    sub_buffer |= ((uint64_t)CSPRNG_buffer[i]) << 8 * i;
  }
  /* position of the next fresh byte in CSPRNG_buffer*/
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  int pos_remaining = sizeof(CSPRNG_buffer) - pos_in_buf;
  while (placed < RSDPG_M * (N - RSDPG_M)) {
    if (bits_in_sub_buf <= 32 && pos_remaining > 0) {
      /* get at most 4 bytes from buffer */
      int refresh_amount = (pos_remaining >= 4) ? 4 : pos_remaining;
      uint32_t refresh_buf = 0;
      for (int i = 0; i < refresh_amount; i++) {
        refresh_buf |= ((uint32_t)CSPRNG_buffer[pos_in_buf + i]) << 8 * i;
      }
      pos_in_buf += refresh_amount;
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      bits_in_sub_buf += 8 * refresh_amount;
      pos_remaining -= refresh_amount;
    }
    *((FZ_ELEM *)res + placed) = sub_buffer & mask;
    if (*((FZ_ELEM *)res + placed) < Z) {
      placed++;
    }
    sub_buffer = sub_buffer >> BITS_FOR_Z;
    bits_in_sub_buf -= BITS_FOR_Z;
  }
}
#endif

#endif // CSPRNG_HASH_H
