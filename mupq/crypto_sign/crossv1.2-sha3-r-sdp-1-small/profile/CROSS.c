/**
 *
 * Reference ISO-C11 Implementation of CROSS.
 *
 * @version 1.1 (March 2023)
 *
 * @author Alessandro Barenghi <alessandro.barenghi@polimi.it>
 * @author Gerardo Pelosi <gerardo.pelosi@polimi.it>
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
#include "CROSS.h"
#include "csprng_hash.h"
#include "fq_arith.h"
#include "merkle_tree.h"
#include "pack_unpack.h"
#include "parameters.h"
#include "seedtree.h"
#include "sha3.h"
#include <assert.h>
#include <stdalign.h>

// Profiling
#include "hal.h"
#include "sendfn.h"
// #define NO_TREES

#define LEAVES_FULL_TREE(L) ((1UL << LOG2(L)))
#define LEAVES_HALF_TREE(L) ((LEAVES_FULL_TREE(L) >> 1))

#define PARENT(i) (((i) % 2) ? (((i) - 1) / 2) : (((i) - 2) / 2))
#define RIGHT_CHILD(i) ((2 * (i) + 2))
#define LEFT_CHILD(i) ((2 * (i) + 1))
#define SIBLING(i) (((i) % 2) ? i + 1 : i - 1)

#define RL(i) (i == 1 ? r_node : l_node)
#define OFFSET(i) ((i) * HASH_DIGEST_LENGTH)

#define CHALLENGE_PROOF_VALUE 0
#define INVALID_MERKLE_NODE 0
#define VALID_MERKLE_NODE 1

#define NOT_COMPUTED 0
#define COMPUTED 1

#include "fips202.h"
#include "keccakf1600.h"

#define NROUNDS 24
#define ROL(a, offset) (((a) << (offset)) ^ ((a) >> (64 - (offset))))

#define TO_PUBLISH 1
#define NOT_TO_PUBLISH 0

#include "merkle.h"

#define LEAVES_FULL_TREE(L) ((1UL << LOG2(L)))
#define LEAVES_HALF_TREE(L) ((LEAVES_FULL_TREE(L) >> 1))

/*
 * setup_tree()
 *
 * uint16_t layer_offset[LOG2(T)+1]    :   Stores one offset per layer for layer
 * change. Required for the computation of PARENT and CHILD nodes. uint16_t
 * nodes_per_layer[LOG2(T)+1] :   Stores the numbers of nodes used in the
 * truncated Merkle tree.
 */
static void setup_tree(uint16_t layer_offsets[LOG2(T) + 1],
                       uint16_t nodes_per_layer[LOG2(T) + 1]) {
  unsigned int depth, layer;
  int r_leaves;
  int subtree_found;

  /* Initialize array with full node counts */
  for (size_t i = 0; i < LOG2(T) + 1; i++) {
    layer_offsets[i] = (1UL << i);
  }

  /* Count root node */
  layer = 0;
  layer_offsets[layer] -= 1;

  /* Count left tree nodes (always full) */
  for (size_t i = 1; i < LOG2(T) + 1; i++) {
    layer_offsets[i] -= (1UL << (i - 1));
  }

  /* Check every full subtree on right side and subtract missing nodes */
  r_leaves = T - (1UL << (LOG2(T) - 1));
  layer = 1;
  while (r_leaves > 0) {
    depth = 0;
    subtree_found = 0;
    while (!subtree_found) {
      if (r_leaves <= (1UL << depth)) {
        for (int i = depth; i > 0; i--) {
          layer_offsets[layer + i] -= (1UL << (i - 1));
        }
        r_leaves -= LEAVES_HALF_TREE(r_leaves);
        layer_offsets[layer] -= 1;
        layer++;
        subtree_found = 1;
      } else {
        depth++;
      }
    }
  }

  /* For the offset, subtract all missing nodes from previous layers from
   * current layer */
  for (int i = LOG2(T); i >= 0; i--) {
    nodes_per_layer[i] = (1UL << i) - layer_offsets[i];
    for (int j = i - 1; j >= 0; j--) {
      layer_offsets[i] -= layer_offsets[j];
    }
    layer_offsets[i] >>= 1;
  }
}

/*
 * get_leaf_indices() is quite similar to setup_tree(), however requires the
 * offset values to compute the correct indices.
 *
 * uint16_t merkle_leaf_indices[T]  : Stores the indices in the truncated tree
 * where the leaves are placed.
 * uint16_t layer_offsets[LOG2(T)+1]   : Same as above.
 */
static void get_leaf_indices(uint16_t merkle_leaf_indices[T],
                             const uint16_t layer_offsets[LOG2(T) + 1]) {
  unsigned int r_leaves;
  unsigned int idx_ctr = 0;

  /* r_node: current root node of next subtree, will always be right-child of
   * previous root */
  /* l_node: traverses from current root node to left-childs until depth of
   * subtree is found */
  unsigned int r_node, l_node;
  unsigned int layer, depth, subtree_found;

  /* If tree is already balanced, simply copy leaves to corresponding position
   */
  if (T == (1UL << LOG2(T))) {
    for (size_t i = 0; i < T; i++) {
      merkle_leaf_indices[i] = T - 1 + i;
    }
    return;
  }

  /* Create (un-) balanced Merkle tree */
  r_leaves = T;
  depth = 0;
  layer = 0;
  r_node = 0;
  l_node = LEFT_CHILD(r_node) - 2 * layer_offsets[layer + depth];
  while (r_leaves > 0) {
    depth = 1;
    subtree_found = 0;
    /* Start from the current root node r_node until the size of a full
     * left-subtree is found. */
    /* If only one leaf is remaining, put it to current root-node, macro RL() is
     * used to decide that. */
    while (!subtree_found) {
      if (r_leaves <= (1UL << depth)) {
        for (size_t j = 0; j < LEAVES_HALF_TREE(r_leaves); j++) {
          merkle_leaf_indices[idx_ctr++] = RL(r_leaves) + j;
        }
        r_node = RIGHT_CHILD(r_node) - 2 * layer_offsets[layer];
        l_node = LEFT_CHILD(r_node) - 2 * layer_offsets[layer];
        layer++;
        r_leaves -= LEAVES_HALF_TREE(r_leaves);
        subtree_found = 1;
      } else {
        l_node = LEFT_CHILD(l_node) - 2 * layer_offsets[layer + depth];
        depth++;
      }
    }
  }
}
#if defined(RSDP)
static void
expand_public_seed(FQ_ELEM V_tr[K][N - K],
                   const uint8_t seed_pub[KEYPAIR_SEED_LENGTH_BYTES]) {
  CSPRNG_STATE_T CSPRNG_state_mat;
  initialize_csprng(&CSPRNG_state_mat, seed_pub, KEYPAIR_SEED_LENGTH_BYTES);
  CSPRNG_fq_mat(V_tr, &CSPRNG_state_mat);
}
#elif defined(RSDPG)
static void
expand_public_seed(FQ_ELEM V_tr[K][N - K], FZ_ELEM W_mat[M][N - M],
                   const uint8_t seed_pub[KEYPAIR_SEED_LENGTH_BYTES]) {
  CSPRNG_STATE_T CSPRNG_state_mat;
  initialize_csprng(&CSPRNG_state_mat, seed_pub, KEYPAIR_SEED_LENGTH_BYTES);

  CSPRNG_fq_mat(V_tr, &CSPRNG_state_mat);
  CSPRNG_fz_mat(W_mat, &CSPRNG_state_mat);
}
#endif
#ifdef PROFILE_HASHING
#include "hal.h"
extern unsigned long long hash_cycles;
#endif
// #if defined(NO_TREES)
// #else
#define NUM_LEAVES_STENCIL_SEED_TREE (1UL << LOG2(T))
#define NUM_INNER_NODES_STENCIL_SEED_TREE (NUM_LEAVES_STENCIL_SEED_TREE - 1)
#define NUM_NODES_STENCIL_SEED_TREE (2 * NUM_LEAVES_STENCIL_SEED_TREE - 1)
static void compute_seeds_to_publish_new(
    /* linearized binary tree of boolean nodes containing
     * flags for each node 1-filled nodes are not to be
     * released */
    unsigned char flags_tree_to_publish[NUM_NODES_STENCIL_SEED_TREE],
    /* Boolean Array indicating which of the T seeds must be
     * released convention as per the above defines */
    const unsigned char indices_to_publish[T]) {
  /* the indices to publish may be less than the full leaves, copy them
   * into the linearized tree leaves */
  memcpy(flags_tree_to_publish + NUM_INNER_NODES_STENCIL_SEED_TREE,
         indices_to_publish, T);
  memset(flags_tree_to_publish, NOT_TO_PUBLISH,
         NUM_INNER_NODES_STENCIL_SEED_TREE * sizeof(unsigned char));
  /* compute the value for the internal nodes of the tree starting from the
   * fathers of the leaves, right to left */
  for (int i = NUM_LEAVES_STENCIL_SEED_TREE - 2; i >= 0; i--) {
    if ((flags_tree_to_publish[LEFT_CHILD(i)] == TO_PUBLISH) &&
        (flags_tree_to_publish[RIGHT_CHILD(i)] == TO_PUBLISH)) {
      flags_tree_to_publish[i] = TO_PUBLISH;
    }
  }
} /* end compute_seeds_to_publish */
// #endif
#if defined(SHA_3_LIBKECCAK)
#include <libkeccak.a.headers/KeccakHash.h>

/* LibKeccak SHAKE Wrappers */

#define SHAKE_STATE_STRUCT Keccak_HashInstance
static inline void xof_shake_init_new(SHAKE_STATE_STRUCT *state, int val) {
  if (val == 128)
    /* will result in a zero-length output for Keccak_HashFinal */
    Keccak_HashInitialize_SHAKE128(state);
  else
    /* will result in a zero-length output for Keccak_HashFinal */
    Keccak_HashInitialize_SHAKE256(state);
}

static inline void xof_shake_update_new(SHAKE_STATE_STRUCT *state,
                                        const unsigned char *input,
                                        unsigned int inputByteLen) {
  Keccak_HashUpdate(state, (const BitSequence *)input,
                    (BitLength)inputByteLen * 8);
}

static inline void xof_shake_final_new(SHAKE_STATE_STRUCT *state) {
  Keccak_HashFinal(state, NULL);
}

static inline void xof_shake_extract_new(SHAKE_STATE_STRUCT *state,
                                         unsigned char *output,
                                         unsigned int outputByteLen) {
  Keccak_HashSqueeze(state, (BitSequence *)output,
                     (BitLength)outputByteLen * 8);
}

#else
#include "fips202.h"
/* standalone FIPS-202 implementation has
 * different states for SHAKE depending on security level*/
#if defined(CATEGORY_1)
#define SHAKE_STATE_STRUCT shake128incctx
#else
#define SHAKE_STATE_STRUCT shake256incctx
#endif
// %%%%%%%%%%%%%%%%%% Self-contained SHAKE Wrappers %%%%%%%%%%%%%%%%%%%%%%%%%%%%

static inline void xof_shake_init_new(SHAKE_STATE_STRUCT *state, int val) {
#if defined(CATEGORY_1)
  shake128_inc_init(state);
#else
  shake256_inc_init(state);
#endif
}
#define NROUNDS 24
#define ROL(a, offset) ((a << offset) ^ (a >> (64 - offset)))

static const uint64_t KeccakF_RoundConstants[NROUNDS] = {
    (uint64_t)0x0000000000000001ULL, (uint64_t)0x0000000000008082ULL,
    (uint64_t)0x800000000000808aULL, (uint64_t)0x8000000080008000ULL,
    (uint64_t)0x000000000000808bULL, (uint64_t)0x0000000080000001ULL,
    (uint64_t)0x8000000080008081ULL, (uint64_t)0x8000000000008009ULL,
    (uint64_t)0x000000000000008aULL, (uint64_t)0x0000000000000088ULL,
    (uint64_t)0x0000000080008009ULL, (uint64_t)0x000000008000000aULL,
    (uint64_t)0x000000008000808bULL, (uint64_t)0x800000000000008bULL,
    (uint64_t)0x8000000000008089ULL, (uint64_t)0x8000000000008003ULL,
    (uint64_t)0x8000000000008002ULL, (uint64_t)0x8000000000000080ULL,
    (uint64_t)0x000000000000800aULL, (uint64_t)0x800000008000000aULL,
    (uint64_t)0x8000000080008081ULL, (uint64_t)0x8000000000008080ULL,
    (uint64_t)0x0000000080000001ULL, (uint64_t)0x8000000080008008ULL};

static void keccak_inc_absorb_new(uint64_t *s_inc, uint32_t r, uint8_t *m,
                                  size_t *mlen, uint8_t *buf, int offset) {
  /* Recall that s_inc[25] is the non-absorbed bytes xored into the state */
  while (*mlen + s_inc[25] >= r) {

    KeccakF1600_StateXORBytes(s_inc, m, s_inc[25], r - s_inc[25]);
    *mlen -= (size_t)(r - s_inc[25]);
    m += r - s_inc[25];
    s_inc[25] = 0;

    KeccakF1600_StatePermute(s_inc);
  }
  if (offset == 0) {
    memcpy(buf, m, *mlen);
  }

  else {
    KeccakF1600_StateXORBytes(s_inc, m, s_inc[25], *mlen);
    s_inc[25] += *mlen;
  }
}
void shake128_inc_absorb_new(shake128incctx *state, uint8_t *input,
                             size_t *inlen, uint8_t *buf, int offset) {
#ifdef PROFILE_HASHING
  uint64_t t0 = hal_get_time();
#endif
  keccak_inc_absorb_new(state->ctx, SHAKE128_RATE, input, inlen, buf, offset);
#ifdef PROFILE_HASHING
  uint64_t t1 = hal_get_time();
  hash_cycles += (t1 - t0);
#endif
}
void shake256_inc_absorb_new(shake256incctx *state, uint8_t *input,
                             size_t *inlen, uint8_t *buf, int offset) {
#ifdef PROFILE_HASHING
  uint64_t t0 = hal_get_time();
#endif
  keccak_inc_absorb_new(state->ctx, SHAKE256_RATE, input, inlen, buf, offset);
#ifdef PROFILE_HASHING
  uint64_t t1 = hal_get_time();
  hash_cycles += (t1 - t0);
#endif
}

static inline void xof_shake_update_new(SHAKE_STATE_STRUCT *state,
                                        const unsigned char *input,
                                        unsigned int *inputByteLen,
                                        unsigned char *buf, int offset) {
#if defined(CATEGORY_1)
  shake128_inc_absorb_new(state, (const uint8_t *)input, inputByteLen,
                          (uint8_t *)buf, offset);
#else
  shake256_inc_absorb_new(state, (const uint8_t *)input, inputByteLen,
                          (uint8_t *)buf, offset);
#endif
}

static inline void xof_shake_final_new(SHAKE_STATE_STRUCT *state) {
#if defined(CATEGORY_1)
  shake128_inc_finalize(state);
#else
  shake256_inc_finalize(state);
#endif
}

static inline void xof_shake_extract_new(SHAKE_STATE_STRUCT *state,
                                         unsigned char *output,
                                         unsigned int outputByteLen) {
#if defined(CATEGORY_1)
  shake128_inc_squeeze(output, outputByteLen, state);
#else
  shake256_inc_squeeze(output, outputByteLen, state);
#endif
}
#endif

#if defined(RSDP)
static void expand_private_seed(FZ_ELEM eta[N], FQ_ELEM V_tr[K][N - K],
                                const uint8_t seed[KEYPAIR_SEED_LENGTH_BYTES]) {
  uint8_t seede_seed_pub[2][KEYPAIR_SEED_LENGTH_BYTES];
  CSPRNG_STATE_T CSPRNG_state;
  initialize_csprng(&CSPRNG_state, seed, KEYPAIR_SEED_LENGTH_BYTES);
  csprng_randombytes((uint8_t *)seede_seed_pub, 2 * KEYPAIR_SEED_LENGTH_BYTES,
                     &CSPRNG_state);

  expand_public_seed(V_tr, seede_seed_pub[1]);

  CSPRNG_STATE_T CSPRNG_state_eta;
  initialize_csprng(&CSPRNG_state_eta, seede_seed_pub[0],
                    KEYPAIR_SEED_LENGTH_BYTES);
  CSPRNG_zz_vec(eta, &CSPRNG_state_eta);
}
#elif defined(RSDPG)
static void expand_private_seed(FZ_ELEM eta[N], FZ_ELEM zeta[M],
                                FQ_ELEM V_tr[K][N - K], FZ_ELEM W_mat[M][N - M],
                                const uint8_t seed[KEYPAIR_SEED_LENGTH_BYTES]) {
  uint8_t seede_seed_pub[2][KEYPAIR_SEED_LENGTH_BYTES];
  CSPRNG_STATE_T CSPRNG_state;
  initialize_csprng(&CSPRNG_state, seed, KEYPAIR_SEED_LENGTH_BYTES);
  csprng_randombytes((uint8_t *)seede_seed_pub, 2 * KEYPAIR_SEED_LENGTH_BYTES,
                     &CSPRNG_state);

  expand_public_seed(V_tr, W_mat, seede_seed_pub[1]);

  CSPRNG_STATE_T CSPRNG_state_eta;
  initialize_csprng(&CSPRNG_state_eta, seede_seed_pub[0],
                    KEYPAIR_SEED_LENGTH_BYTES);
  CSPRNG_zz_inf_w(zeta, &CSPRNG_state_eta);
  fz_inf_w_by_fz_matrix(eta, zeta, W_mat);
  fz_dz_norm_sigma(eta);
}
#endif
void CROSS_keygen(prikey_t *SK, pubkey_t *PK) {
  send_unsigned("start keygen: ", hal_checkstack());
  /* generation of random material for public and private key */
  randombytes(SK->seed, KEYPAIR_SEED_LENGTH_BYTES);
  uint8_t seede_seed_pub[2][KEYPAIR_SEED_LENGTH_BYTES];

  //   CSPRNG_STATE_T CSPRNG_state;
  //   initialize_csprng(&CSPRNG_state,SK->seed,KEYPAIR_SEED_LENGTH_BYTES);
  //   csprng_randombytes((uint8_t *)seede_seed_pub,
  //                      2*KEYPAIR_SEED_LENGTH_BYTES,
  //                      &CSPRNG_state);

  send_unsigned("init csprng: ", hal_checkstack());
  CSPRNG_STATE_T CSPRNG_state_eta;
  initialize_csprng(&CSPRNG_state_eta, SK->seed, KEYPAIR_SEED_LENGTH_BYTES);
  csprng_randombytes((uint8_t *)seede_seed_pub, 2 * KEYPAIR_SEED_LENGTH_BYTES,
                     &CSPRNG_state_eta);

  memcpy(PK->seed_pub, seede_seed_pub[1], KEYPAIR_SEED_LENGTH_BYTES);

  FZ_ELEM eta[N];
  // CSPRNG_STATE_T CSPRNG_state_eta;
  initialize_csprng(&CSPRNG_state_eta, seede_seed_pub[0],
                    KEYPAIR_SEED_LENGTH_BYTES);
  /* expansion of matrix/matrices */
  // FQ_ELEM V_tr[K][N-K];

  int i;
#if defined(RSDP)
  send_unsigned("calculate eta: ", hal_checkstack());
  // FQ_ELEM V_tr_new[K][N-K];
  // FQ_ELEM V_tr_new1[1][1];
  // FQ_ELEM V_tr_new2;
  FQ_ELEM pub_syn_new[N - K];
  CSPRNG_zz_vec(eta, &CSPRNG_state_eta);
  for (i = K; i < N; i++) {
    pub_syn_new[i - K] = RESTR_TO_VAL(eta[i]);
  }

  send_unsigned("expand seeds: ", hal_checkstack());
  // expand_public_seed(V_tr,PK->seed_pub);
  CSPRNG_STATE_T CSPRNG_state_mat;
  initialize_csprng(&CSPRNG_state_mat, PK->seed_pub, KEYPAIR_SEED_LENGTH_BYTES);

  // CSPRNG_fq_mat(V_tr_new,&CSPRNG_state_mat);

  send_unsigned("compute syndrome: ", hal_checkstack());
  const FQ_ELEM mask = ((FQ_ELEM)1 << BITS_TO_REPRESENT(Q - 1)) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_V_CT_RNG, 8) / 8];
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), &CSPRNG_state_mat);
  int placed = 0;
  uint64_t sub_buffer = *(uint64_t *)CSPRNG_buffer;
  int bits_in_sub_buf = 64;
  int pos_in_buf = 8;
  int i1 = 0, j1 = 0;
  while (placed < K * (N - K)) {
    if (bits_in_sub_buf <= 32) {
      /* get 32 fresh bits from main buffer with a single load */
      uint32_t refresh_buf = *(uint32_t *)(CSPRNG_buffer + pos_in_buf);
      pos_in_buf += 4;
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      bits_in_sub_buf += 32;
    }
    //*((FQ_ELEM*)V_tr_new1) = sub_buffer & mask;
    // V_tr_new2 =(FQ_ELEM)(sub_buffer & mask);
    if ((FQ_ELEM)(sub_buffer & mask) < Q) {
      /*int tem=0;
      if(V_tr_new2 == V_tr_new[i1][j1]){
         tem =1;
      }
      assert(tem==0);*/
      pub_syn_new[j1] =
          FQRED_DOUBLE((FQ_DOUBLEPREC)pub_syn_new[j1] +
                       (FQ_DOUBLEPREC)RESTR_TO_VAL(eta[i1]) *
                           (FQ_DOUBLEPREC)((FQ_ELEM)(sub_buffer & mask)));
      j1++;
      if (j1 == N - K) {
        i1++;
        j1 = 0;
      }
      placed++;
      sub_buffer = sub_buffer >> BITS_FOR_Q;
      bits_in_sub_buf -= BITS_FOR_Q;
    } else {
      sub_buffer = sub_buffer >> 1;
      bits_in_sub_buf -= 1;
    }
  }
  fq_dz_norm_synd(pub_syn_new);
  pack_fq_syn(PK->s, pub_syn_new);
#elif defined(RSDPG)
  // FQ_ELEM V_tr[K][N-K];
  // FQ_ELEM V_tr_new;
  // FZ_ELEM W_mat[M][N-M];
  // FZ_ELEM W_mat_new;
  // expand_public_seed(V_tr,W_mat,PK->seed_pub);

  CSPRNG_STATE_T CSPRNG_state_mat;
  initialize_csprng(&CSPRNG_state_mat, PK->seed_pub, KEYPAIR_SEED_LENGTH_BYTES);

  // CSPRNG_fq_mat(V_tr,&CSPRNG_state_mat);

  const FQ_ELEM mask = ((FQ_ELEM)1 << BITS_TO_REPRESENT(Q - 1)) - 1;
  uint8_t CSPRNG_buffer[ROUND_UP(BITS_V_CT_RNG, 8) / 8];
  csprng_randombytes(CSPRNG_buffer, sizeof(CSPRNG_buffer), &CSPRNG_state_mat);

  const FZ_ELEM mask1 = ((FZ_ELEM)1 << BITS_TO_REPRESENT(Z - 1)) - 1;
  uint8_t CSPRNG_buffer1[ROUND_UP(BITS_W_CT_RNG, 8) / 8];
  csprng_randombytes(CSPRNG_buffer1, sizeof(CSPRNG_buffer1), &CSPRNG_state_mat);
  int placed = 0;
  uint64_t sub_buffer = *(uint64_t *)CSPRNG_buffer1;
  int bits_in_sub_buf = 64;
  /* position of the next fresh byte in CSPRNG_buffer*/
  int pos_in_buf = 8;

  FZ_ELEM zeta[M];
  CSPRNG_zz_inf_w(zeta, &CSPRNG_state_eta);
  memset(eta, 0, (N - M) * sizeof(FZ_ELEM));
  memcpy(eta + (N - M), zeta, M * sizeof(FZ_ELEM));
  int i2 = 0, j2 = 0;
  while (placed < M * (N - M)) {
    if (bits_in_sub_buf <= 32) {
      /* get 32 fresh bits from main buffer with a single load */
      uint32_t refresh_buf1 = *(uint32_t *)(CSPRNG_buffer1 + pos_in_buf);
      pos_in_buf += 4;
      sub_buffer |= ((uint64_t)refresh_buf1) << bits_in_sub_buf;
      bits_in_sub_buf += 32;
    }
    //*((FZ_ELEM*)W_mat+placed1) = sub_buffer1 & mask1;
    if ((FZ_ELEM)(sub_buffer & mask1) < Z) {
      eta[j2] =
          FZRED_DOUBLE((FZ_DOUBLEPREC)eta[j2] +
                       (FZ_DOUBLEPREC)zeta[i2] *
                           (FZ_DOUBLEPREC)((FZ_ELEM)(sub_buffer & mask1)));
      j2++;
      if (j2 == N - M) {
        i2++;
        j2 = 0;
      }
      placed++;
      sub_buffer = sub_buffer >> BITS_FOR_Z;
      bits_in_sub_buf -= BITS_FOR_Z;

    } else {
      sub_buffer = sub_buffer >> 1;
      bits_in_sub_buf -= 1;
    }
  }

  fz_dz_norm_sigma(eta);
  FQ_ELEM pub_syn[N - K];
  for (int i = K; i < N; i++) {
    pub_syn[i - K] = RESTR_TO_VAL(eta[i]);
  }
  int i1 = 0, j1 = 0;
  placed = 0;
  sub_buffer = *(uint64_t *)CSPRNG_buffer;
  bits_in_sub_buf = 64;
  pos_in_buf = 8;

  while (placed < K * (N - K)) {
    if (bits_in_sub_buf <= 32) {
      uint32_t refresh_buf = *(uint32_t *)(CSPRNG_buffer + pos_in_buf);
      pos_in_buf += 4;
      sub_buffer |= ((uint64_t)refresh_buf) << bits_in_sub_buf;
      bits_in_sub_buf += 32;
    }
    //*((FQ_ELEM*)V_tr+placed) = sub_buffer & mask;
    if ((FQ_ELEM)(sub_buffer & mask) < Q) {
      pub_syn[j1] =
          FQRED_DOUBLE((FQ_DOUBLEPREC)pub_syn[j1] +
                       (FQ_DOUBLEPREC)RESTR_TO_VAL(eta[i1]) *
                           (FQ_DOUBLEPREC)((FQ_ELEM)(sub_buffer & mask)));
      j1++;
      if (j1 == N - K) {
        i1++;
        j1 = 0;
      }
      placed++;
      sub_buffer = sub_buffer >> BITS_FOR_Q;
      bits_in_sub_buf -= BITS_FOR_Q;

    } else {
      sub_buffer = sub_buffer >> 1;
      bits_in_sub_buf -= 1;
    }
  }

  // restr_vec_by_fq_matrix(pub_syn,eta,V_tr);
  fq_dz_norm_synd(pub_syn);
  pack_fq_syn(PK->s, pub_syn);
#endif
}

void CROSS_keygen_old(prikey_t *SK, pubkey_t *PK) {
  /* generation of random material for public and private key */
  randombytes(SK->seed, KEYPAIR_SEED_LENGTH_BYTES);
  uint8_t seede_seed_pub[2][KEYPAIR_SEED_LENGTH_BYTES];

  CSPRNG_STATE_T CSPRNG_state;
  initialize_csprng(&CSPRNG_state, SK->seed, KEYPAIR_SEED_LENGTH_BYTES);
  csprng_randombytes((uint8_t *)seede_seed_pub, 2 * KEYPAIR_SEED_LENGTH_BYTES,
                     &CSPRNG_state);
  memcpy(PK->seed_pub, seede_seed_pub[1], KEYPAIR_SEED_LENGTH_BYTES);

  /* expansion of matrix/matrices */
  FQ_ELEM V_tr[K][N - K];
#if defined(RSDP)
  expand_public_seed(V_tr, PK->seed_pub);
#elif defined(RSDPG)
  FZ_ELEM W_mat[M][N - M];
  expand_public_seed(V_tr, W_mat, PK->seed_pub);
#endif

  /* expansion of secret key material */
  FZ_ELEM eta[N];
  CSPRNG_STATE_T CSPRNG_state_eta;
  initialize_csprng(&CSPRNG_state_eta, seede_seed_pub[0],
                    KEYPAIR_SEED_LENGTH_BYTES);

#if defined(RSDP)
  CSPRNG_zz_vec(eta, &CSPRNG_state_eta);
#elif defined(RSDPG)
  FZ_ELEM zeta[M];
  CSPRNG_zz_inf_w(zeta, &CSPRNG_state_eta);
  fz_inf_w_by_fz_matrix(eta, zeta, W_mat);
  fz_dz_norm_sigma(eta);
#endif
  /* compute public syndrome */
  FQ_ELEM pub_syn[N - K];
  restr_vec_by_fq_matrix(pub_syn, eta, V_tr);
  fq_dz_norm_synd(pub_syn);
  pack_fq_syn(PK->s, pub_syn);
}

/*****************************************************/
/******************* CROSS SIGN **********************/
/*****************************************************/

void CROSS_sign_inithash(CSPRNG_STATE_T *csprng_state) {
  // xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
}

void CROSS_sign_hash(uint8_t *buf, size_t buf_len, uint8_t *m_new, uint8_t *m,
                     size_t dlen, int offset, CSPRNG_STATE_T *csprng_state) {
  // xof_shake_update_new(&csprng_state, m_new, &dlen, (uint8_t *)m, offset);
  // xof_shake_final_new(&csprng_state);
  // xof_shake_extract_new(&csprng_state, buf, buf_len);
}

// Commit to tree and return seed leaves
void CROSS_sign_commit(uint16_t *merkle_leaf_indices, uint8_t *salt) {
  /****** Computing the commitments ******/
  uint8_t root_seed[SEED_LENGTH_BYTES];
  randombytes(root_seed, SEED_LENGTH_BYTES);
  // randombytes(sig->salt, SALT_LENGTH_BYTES);
  send_unsigned("after setup: ", hal_checkstack());

#if defined(NO_TREES)
  unsigned char rounds_seeds[T * SEED_LENGTH_BYTES] = {0};
  compute_round_seeds(rounds_seeds, root_seed, sig->salt);
#else
  uint8_t seed_tree[SEED_LENGTH_BYTES * NUM_NODES_SEED_TREE] = {0};
  generate_seed_tree_from_root(seed_tree, root_seed, salt);
  uint8_t *rounds_seeds =
      seed_tree + SEED_LENGTH_BYTES * NUM_INNER_NODES_SEED_TREE;
#endif

  send_unsigned("seed tree from root generation stack: ", hal_checkstack());

  // uint16_t merkle_leaf_indices[T];
  uint16_t layer_offsets[LOG2(T) + 1];
  uint16_t nodes_per_layer[LOG2(T) + 1];

  setup_tree(layer_offsets, nodes_per_layer);
  get_leaf_indices(merkle_leaf_indices, layer_offsets);
}

void CROSS_sign(const prikey_t *SK, const char *const m, const uint64_t mlen,
                sig_t *sig) {
  send_unsigned("start sign: ", hal_checkstack());

  /* Wipe any residual information in the sig structure allocated by the
   * caller */
  memset(sig, 0, sizeof(sig_t));

  /****** Key material expansion *******/
  FQ_ELEM H[K][N - K];
  FZ_ELEM eta[N];
#if defined(RSDP)
  expand_private_seed(eta, H, SK->seed);
#elif defined(RSDPG)
  FZ_ELEM zeta[M];
  FZ_ELEM W_mat[M][N - M];
  expand_private_seed(eta, zeta, H, W_mat, SK->seed);
#endif

  /****** Commit to tree ******/
  uint8_t merkle_tree_0[NUM_NODES_MERKLE_TREE * HASH_DIGEST_LENGTH];
  uint16_t merkle_leaf_indices[T];
  randombytes(sig->salt, SALT_LENGTH_BYTES);
  /****** Computing the commitments ******/
  uint8_t root_seed[SEED_LENGTH_BYTES];
  randombytes(root_seed, SEED_LENGTH_BYTES);
  // randombytes(sig->salt, SALT_LENGTH_BYTES);
  send_unsigned("after setup: ", hal_checkstack());

#if defined(NO_TREES)
  unsigned char rounds_seeds[T * SEED_LENGTH_BYTES] = {0};
  compute_round_seeds(rounds_seeds, root_seed, sig->salt);
#else
  uint8_t seed_tree[SEED_LENGTH_BYTES * NUM_NODES_SEED_TREE] = {0};
  generate_seed_tree_from_root(seed_tree, root_seed, sig->salt);
  uint8_t *rounds_seeds =
      seed_tree + SEED_LENGTH_BYTES * NUM_INNER_NODES_SEED_TREE;
#endif

  send_unsigned("seed tree from root generation stack: ", hal_checkstack());

  // uint16_t merkle_leaf_indices[T];
  uint16_t layer_offsets[LOG2(T) + 1];
  uint16_t nodes_per_layer[LOG2(T) + 1];

  setup_tree(layer_offsets, nodes_per_layer);
  get_leaf_indices(merkle_leaf_indices, layer_offsets);

  // CROSS_sign_commit(merkle_leaf_indices, sig->salt);

  /***** CSPRNG Setup ******/
  FZ_ELEM eta_tilde[T][N];
  // FZ_ELEM sigma[T][N];
  FZ_ELEM sigma_new[N];
  FQ_ELEM u_tilde[T][N];
  FQ_ELEM s_tilde[N - K];

#if defined(RSDP)
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#elif defined(RSDPG)
  FZ_ELEM zeta_tilde[M];
  FZ_ELEM delta[T][M];
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#endif
  /* cmt_0_i_input is syndrome||sigma ||salt ; place salt at the end */
  memcpy(cmt_0_i_input + offset_salt, sig->salt, SALT_LENGTH_BYTES);

  uint8_t
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t)];
  /* cmt_1_i_input is concat(seed,salt,round index) */
  memcpy(cmt_1_i_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);

  uint8_t *m_new = cmt_0_i_input;
  size_t dlen = 0, dlen1 = 0;
  CSPRNG_STATE_T csprng_state1;
  CSPRNG_STATE_T csprng_state;

#if defined(CATEGORY_1)
  uint8_t r = SHAKE128_RATE;
#else
  uint8_t r = SHA3_256_RATE;
#endif

  CSPRNG_STATE_T CSPRNG_state;
  uint8_t commit_digests[2][HASH_DIGEST_LENGTH];
  xof_shake_init_new(&csprng_state1, SEED_LENGTH_BYTES * 8);
  // CROSS_sign_inithash(*csprng_state1);
  uint16_t domain_sep_idx_hash;
  uint16_t domain_sep_i;
  /*#if defined(NO_TREES)
  size_t i1;
  #else*/
  size_t i1;
  unsigned int node_ctr, parent_layer;
  uint8_t cmt_1_new[r + HASH_DIGEST_LENGTH];
  int i;
  for (i = 0; i < r + HASH_DIGEST_LENGTH; i++)
    cmt_1_new[i] = 0;
  uint8_t cmt_0_new[HASH_DIGEST_LENGTH] = {0};

  for (i = 0; i < T; i++) {
    /* CSPRNG is fed with concat(seed,salt,round index) represented
     * as a 2 bytes little endian unsigned integer */

    // Re-declared? Put outside loops
    uint8_t
        csprng_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t)];
    memcpy(csprng_input, rounds_seeds + SEED_LENGTH_BYTES * i,
           SEED_LENGTH_BYTES);
    memcpy(csprng_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);
    /* i+c */
    domain_sep_i = i + NUM_NODES_SEED_TREE;
    csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES] =
        (domain_sep_i >> 8) & 0xFF;
    csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES + 1] =
        domain_sep_i & 0xFF;

    /* expand seed[i] into seed_e and seed_u */
    initialize_csprng(&CSPRNG_state, csprng_input,
                      SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t));
    /* expand eta_tilde */
#if defined(RSDP)
    CSPRNG_zz_vec(eta_tilde[i], &CSPRNG_state);
#elif defined(RSDPG)
    CSPRNG_zz_inf_w(zeta_tilde, &CSPRNG_state);
    restr_inf_w_sub(delta[i], zeta, zeta_tilde);
    fz_dz_norm_delta(delta[i]);
    fz_inf_w_by_fz_matrix(eta_tilde[i], zeta_tilde, W_mat);
    fz_dz_norm_sigma(eta_tilde[i]);
#endif
    restr_vec_sub(sigma_new, eta, eta_tilde[i]);

    // Outside loop?
    FQ_ELEM v[N];
    convert_restr_vec_to_fq(v, sigma_new);
    fz_dz_norm_sigma(sigma_new);
    /* expand u_tilde */
    CSPRNG_fq_vec(u_tilde[i], &CSPRNG_state);

    FQ_ELEM u[N];
    fq_vec_by_fq_vec_pointwise(u, v, u_tilde[i]);
    fq_vec_by_fq_matrix(s_tilde, u, H);
    fq_dz_norm_synd(s_tilde);

    /* cmt_0_i_input contains s-tilde || sigma_i || salt */
    pack_fq_syn(cmt_0_i_input, s_tilde);

#if defined(RSDP)
    pack_fz_vec(cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE, sigma_new);
#elif defined(RSDPG)
    pack_fz_rsdp_g_vec(cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE, delta[i]);
#endif
    /* Fixed endianness marshalling of round counter
     * i+c+dsc */
    domain_sep_idx_hash = domain_sep_i + HASH_CSPRNG_DOMAIN_SEP_CONST;
    cmt_0_i_input[offset_round_idx] = (domain_sep_idx_hash >> 8) & 0xFF;
    cmt_0_i_input[offset_round_idx + 1] = domain_sep_idx_hash & 0xFF;

    m_new = cmt_0_i_input;
    dlen = sizeof(cmt_0_i_input);
    xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
    xof_shake_update_new(&csprng_state, m_new, &dlen, cmt_0_i_input, 1);
    xof_shake_final_new(&csprng_state);
    xof_shake_extract_new(&csprng_state, cmt_0_new, HASH_DIGEST_LENGTH);
    // CROSS_sign_inithash(*csprng_state);
    // CROSS_sign_hash(cmt_0_new, HASH_DIGEST_LENGTH, m_new, cmt_0_i_input,
    // dlen,
    //                 csprng_state);

    memcpy(merkle_tree_0 + merkle_leaf_indices[i] * HASH_DIGEST_LENGTH,
           cmt_0_new, HASH_DIGEST_LENGTH);
    // #endif
    memcpy(cmt_1_i_input, rounds_seeds + SEED_LENGTH_BYTES * i,
           SEED_LENGTH_BYTES);

    cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES] =
        (domain_sep_idx_hash >> 8) & 0xFF;
    cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + 1] =
        domain_sep_idx_hash & 0xFF;

    // hash(cmt_1[i],cmt_1_i_input,sizeof(cmt_1_i_input));
    m_new = cmt_1_i_input;
    dlen = sizeof(cmt_1_i_input);
    xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
    // CROSS_inithash(*csprng_state);
    xof_shake_update_new(&csprng_state, m_new, &dlen, cmt_1_i_input, 1);
    xof_shake_final_new(&csprng_state);
    xof_shake_extract_new(&csprng_state, cmt_1_new + dlen1, HASH_DIGEST_LENGTH);
    // CROSS_sign_hash(cmt_1_new + dlen1, HASH_DIGEST_LENGTH, cmt_1_i_input,
    //                 cmt_1_i_input, dlen, csprng_input);

    dlen1 += HASH_DIGEST_LENGTH;
    if (dlen1 > r && i != T - 1) {
      m_new = cmt_1_new;
      xof_shake_update_new(&csprng_state1, m_new, &dlen1, cmt_1_new, 0);
    }
    if (i == T - 1) {
      m_new = cmt_1_new;
      xof_shake_update_new(&csprng_state1, m_new, &dlen1, cmt_1_new, 1);
      xof_shake_final_new(&csprng_state1);
      xof_shake_extract_new(&csprng_state1, commit_digests[1],
                            HASH_DIGEST_LENGTH);
    }
  }

  /* vector containing d_0 and d_1 from spec */
  // uint8_t commit_digests[2][HASH_DIGEST_LENGTH];
  /*#if defined(NO_TREES)
      merkle_tree_root_compute(commit_digests[0], cmt_0);
  #else*/
  // uint8_t merkle_tree_0[NUM_NODES_MERKLE_TREE * HASH_DIGEST_LENGTH];
  // merkle_tree_root_compute(commit_digests[0], merkle_tree_0, cmt_0);
  // generate_merkle_tree(merkle_tree_0, cmt_0);
  /* Root is at first position of the tree */
  node_ctr = 0;
  parent_layer = LOG2(T) - 1;
  for (i1 = NUM_NODES_MERKLE_TREE - 1; i1 > 0; i1 -= 2) {
    // hash(merkle_tree_0 + OFFSET(PARENT(i1) + layer_offsets[parent_layer]),
    // merkle_tree_0 + OFFSET(SIBLING(i1)), 2*HASH_DIGEST_LENGTH);
    m_new = merkle_tree_0 + OFFSET(SIBLING(i1));
    dlen = 2 * HASH_DIGEST_LENGTH;
    xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
    xof_shake_update_new(&csprng_state, m_new, &dlen,
                         merkle_tree_0 + OFFSET(SIBLING(i1)), 1);
    xof_shake_final_new(&csprng_state);
    xof_shake_extract_new(&csprng_state,
                          merkle_tree_0 +
                              OFFSET(PARENT(i1) + layer_offsets[parent_layer]),
                          HASH_DIGEST_LENGTH);
    if (node_ctr >= nodes_per_layer[parent_layer + 1] - 2) {
      parent_layer--;
      node_ctr = 0;
    } else {
      node_ctr += 2;
    }
  }
  memcpy(commit_digests[0], merkle_tree_0, HASH_DIGEST_LENGTH);
  // #endif
  // hash(commit_digests[1], (unsigned char*)cmt_1, sizeof(cmt_1));
  /*hash(sig->digest_01,
            (unsigned char*) commit_digests,
            sizeof(commit_digests));*/

  m_new = (unsigned char *)commit_digests;
  dlen = sizeof(commit_digests);
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update_new(&csprng_state, m_new, &dlen,
                       (unsigned char *)commit_digests, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state, sig->digest_01, HASH_DIGEST_LENGTH);

  /* first challenge extraction */
  uint8_t beta_buf[2 * HASH_DIGEST_LENGTH + SALT_LENGTH_BYTES];
  /* place d_m at the beginning of the input of the hash generating d_beta*/
  // hash(beta_buf,(uint8_t*) m,mlen);
  m_new = (uint8_t *)m;
  dlen = mlen;
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update_new(&csprng_state, m_new, &dlen, (uint8_t *)m, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state, beta_buf, HASH_DIGEST_LENGTH);

  memcpy(beta_buf + HASH_DIGEST_LENGTH, sig->digest_01, HASH_DIGEST_LENGTH);
  memcpy(beta_buf + 2 * HASH_DIGEST_LENGTH, sig->salt, SALT_LENGTH_BYTES);

  uint8_t d_beta[HASH_DIGEST_LENGTH];
  //    hash(d_beta,beta_buf,2*HASH_DIGEST_LENGTH+SALT_LENGTH_BYTES);
  m_new = beta_buf;
  dlen = 2 * HASH_DIGEST_LENGTH + SALT_LENGTH_BYTES;
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update_new(&csprng_state, m_new, &dlen, beta_buf, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state, d_beta, HASH_DIGEST_LENGTH);

  FQ_ELEM beta[T];
  initialize_csprng(&CSPRNG_state, d_beta, HASH_DIGEST_LENGTH);
  CSPRNG_fq_vec_beta(beta, &CSPRNG_state);

  /* Computation of the first round of responses */
  // FQ_ELEM y[T][N];
  uint8_t digest_b_buf_new[r + DENSELY_PACKED_FQ_VEC_SIZE];
  dlen = 0;
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
  for (i = 0; i < T; i++) {
    /*fq_vec_by_restr_vec_scaled(y[i],
                               eta_tilde[i],
                               beta[i],
                               u_tilde[i]);
    fq_dz_norm(y[i]);*/
    fq_vec_by_restr_vec_scaled(u_tilde[i], eta_tilde[i], beta[i], u_tilde[i]);
    fq_dz_norm(u_tilde[i]);
    pack_fq_vec(digest_b_buf_new + dlen, u_tilde[i]);
    m_new = digest_b_buf_new;
    dlen += DENSELY_PACKED_FQ_VEC_SIZE;
    if (dlen > r)
      xof_shake_update_new(&csprng_state, m_new, &dlen, digest_b_buf_new, 0);
    if (i == T - 1) {
      memcpy(digest_b_buf_new + dlen, d_beta, HASH_DIGEST_LENGTH);
      dlen += HASH_DIGEST_LENGTH;
      m_new = digest_b_buf_new;
      xof_shake_update_new(&csprng_state, m_new, &dlen, digest_b_buf_new, 1);
      xof_shake_final_new(&csprng_state);
      xof_shake_extract_new(&csprng_state, sig->digest_b, HASH_DIGEST_LENGTH);
    }
  }
  /* y vectors are packed before being hashed */
  /*uint8_t digest_b_buf[T*DENSELY_PACKED_FQ_VEC_SIZE+HASH_DIGEST_LENGTH];
  for(int x = 0; x < T; x++){
      pack_fq_vec(digest_b_buf+(x*DENSELY_PACKED_FQ_VEC_SIZE),y[x]);
  }*/
  /* Second challenge extraction */
  // memcpy(digest_b_buf+T*DENSELY_PACKED_FQ_VEC_SIZE,d_beta,HASH_DIGEST_LENGTH);

  // hash(sig->digest_b, digest_b_buf, sizeof(digest_b_buf));

  uint8_t fixed_weight_b[T] = {0};
  expand_digest_to_fixed_weight(fixed_weight_b, sig->digest_b);

  /* Computation of the second round of responses */

  /*#if defined(NO_TREES)
      merkle_tree_proof_compute(sig->mtp,cmt_0,fixed_weight_b);
      publish_round_seeds(sig->stp,rounds_seeds,fixed_weight_b);
  #else*/
  merkle_tree_proof_compute_new(sig->mtp, merkle_tree_0, fixed_weight_b);
  publish_seeds(sig->stp, seed_tree, fixed_weight_b);
  // #endif
  merkle_tree_proof_compute_new(sig->mtp, merkle_tree_0, fixed_weight_b);
  publish_seeds(sig->stp, seed_tree, fixed_weight_b);

  unsigned char flags_tree_to_publish[NUM_NODES_STENCIL_SEED_TREE] = {0};
  compute_seeds_to_publish_new(flags_tree_to_publish, fixed_weight_b);
  const int missing_nodes_before[LOG2(T) + 1] =
      MISSING_NODES_BEFORE_LEVEL_ARRAY;
  const int nodes_in_level[LOG2(T) + 1] = NODES_PER_LEVEL_ARRAY;

  int num_seeds_published = 0;
  // int node_idx = 1;
  /*const uint32_t csprng_input_len = SALT_LENGTH_BYTES +
                                    SEED_LENGTH_BYTES +
                                    sizeof(uint16_t);
  unsigned char csprng_input[csprng_input_len];
   CSPRNG_STATE_T tree_csprng_state;
memcpy(csprng_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);

uint8_t stp_new[TREE_NODES_TO_STORE*SEED_LENGTH_BYTES];*/
  int published_rsps = 0;
  int c_;
  for (int i = 0; i < T;) {
    int c = (NUM_LEAVES_STENCIL_SEED_TREE - 1) + i;
    c_ = c;
    int flag = 0;
    int h = LOG2(T), h_ = LOG2(T);
    do {
      if (flags_tree_to_publish[c] == TO_PUBLISH) {
        c_ = c;
        h_ = h;
        flag = 1;
      }
      h--;
      c = PARENT(c);
    } while (c != 0);

    if (flag == 0) {
      assert(published_rsps < T - W);
      pack_fq_vec(sig->rsp_0[published_rsps].y, u_tilde[i]);
#if defined(RSDP)
      restr_vec_sub(sigma_new, eta, eta_tilde[i]);
      fz_dz_norm_sigma(sigma_new);
      pack_fz_vec(sig->rsp_0[published_rsps].sigma, sigma_new);
#elif defined(RSDPG)
      pack_fz_rsdp_g_vec(sig->rsp_0[published_rsps].delta, delta[i]);
#endif
      memcpy(cmt_1_i_input, rounds_seeds + SEED_LENGTH_BYTES * i,
             SEED_LENGTH_BYTES);
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES] =
          (i + NUM_NODES_SEED_TREE + HASH_CSPRNG_DOMAIN_SEP_CONST >> 8) & 0xFF;
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + 1] =
          i + NUM_NODES_SEED_TREE + HASH_CSPRNG_DOMAIN_SEP_CONST & 0xFF;
      m_new = cmt_1_i_input;
      dlen = sizeof(cmt_1_i_input);
      xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
      xof_shake_update_new(&csprng_state, m_new, &dlen, cmt_1_i_input, 1);
      xof_shake_final_new(&csprng_state);
      xof_shake_extract_new(&csprng_state, cmt_1_new, HASH_DIGEST_LENGTH);
      memcpy(sig->rsp_1[published_rsps], cmt_1_new, HASH_DIGEST_LENGTH);
      published_rsps++;
      i++;
    }

    else {
      int node_storage_idx = c_ - missing_nodes_before[h_];
      memcpy(sig->stp + num_seeds_published * SEED_LENGTH_BYTES,
             seed_tree + node_storage_idx * SEED_LENGTH_BYTES,
             SEED_LENGTH_BYTES);
      // memcpy(seed_tree1 + node_storage_idx *SEED_LENGTH_BYTES,
      // stp_new + num_seeds_published*SEED_LENGTH_BYTES,
      //         SEED_LENGTH_BYTES);
      /*for (int sub_level = h_; sub_level < LOG2(T); sub_level++){
          int index = ((1<<sub_level)-1)+nodes_in_level[sub_level];
          int father_node_idx = c_;
          int count =0;
          while(count<(1<<(sub_level-h_)) && father_node_idx<index){
              memcpy(csprng_input,
                 seed_tree1 +
      (father_node_idx-missing_nodes_before[sub_level])*SEED_LENGTH_BYTES,
                 SEED_LENGTH_BYTES);

              *((uint16_t *)(csprng_input + SALT_LENGTH_BYTES +
      SEED_LENGTH_BYTES)) = father_node_idx;
              initialize_csprng(&tree_csprng_state, csprng_input,
      csprng_input_len); csprng_randombytes(seed_tree1 +
      (LEFT_CHILD(father_node_idx)-missing_nodes_before[sub_level+1])*SEED_LENGTH_BYTES,
                             SEED_LENGTH_BYTES,
                             &tree_csprng_state);
              if ((RIGHT_CHILD(father_node_idx)-
      missing_nodes_before[sub_level+1]) < NUM_NODES_SEED_TREE )
                  csprng_randombytes(seed_tree1 +
      (RIGHT_CHILD(father_node_idx)-missing_nodes_before[sub_level+1])*SEED_LENGTH_BYTES,
                              SEED_LENGTH_BYTES,
                              &tree_csprng_state);
              father_node_idx++;
              count++;
          }
          c_=LEFT_CHILD(c_);

      }*/
      num_seeds_published++;
      /*for(int i1=0; i1<(1<<(LOG2(T)-h_)); i1++){
          int check=0;
          if (memcmp(seed_tree1+((NUM_LEAVES_STENCIL_SEED_TREE-1) +
      i1+i-missing_nodes_before[LOG2(T)]),
          seed_tree+SEED_LENGTH_BYTES*NUM_INNER_NODES_SEED_TREE+i1+i,SEED_LENGTH_BYTES
      )==0) check=1; assert(check>0);
      }*/
      i = i + (1 << (LOG2(T) - h_));
    }
  }
  /* int published_rsps = 0;
   for(i = 0; i<T; i++){
       if(fixed_weight_b[i] == 0){
           assert(published_rsps < T-W);
           pack_fq_vec(sig->rsp_0[published_rsps].y, u_tilde[i]);
#if defined(RSDP)
           restr_vec_sub(sigma_new, eta,eta_tilde[i]);
           fz_dz_norm_sigma(sigma_new);
           pack_fz_vec(sig->rsp_0[published_rsps].sigma, sigma_new);
#elif defined(RSDPG)
           pack_fz_rsdp_g_vec(sig->rsp_0[published_rsps].delta, delta[i]);
#endif
           memcpy(cmt_1_i_input,
              rounds_seeds+SEED_LENGTH_BYTES*i,
              SEED_LENGTH_BYTES);

           cmt_1_i_input[SEED_LENGTH_BYTES+SALT_LENGTH_BYTES] =
(i+NUM_NODES_SEED_TREE+HASH_CSPRNG_DOMAIN_SEP_CONST >> 8) &0xFF;
           cmt_1_i_input[SEED_LENGTH_BYTES+SALT_LENGTH_BYTES+1] =
i+NUM_NODES_SEED_TREE+HASH_CSPRNG_DOMAIN_SEP_CONST & 0xFF;


           m_new = cmt_1_i_input;
           dlen = sizeof(cmt_1_i_input);
           xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES*8);
           xof_shake_update_new(&csprng_state, m_new, &dlen, cmt_1_i_input, 1);
           xof_shake_final_new(&csprng_state);
           xof_shake_extract_new(&csprng_state, cmt_1_new,HASH_DIGEST_LENGTH);
           memcpy(sig->rsp_1[published_rsps], cmt_1_new, HASH_DIGEST_LENGTH);
           published_rsps++;
       }
   }*/
}

/* verify returns 1 if signature is ok, 0 otherwise */
int CROSS_verify(const pubkey_t *const PK, const char *const m,
                 const uint64_t mlen, const sig_t *const sig) {
  send_unsigned("start verify: ", hal_checkstack());
  CSPRNG_STATE_T CSPRNG_state;

  FQ_ELEM V_tr[K][N - K];

#if defined(RSDP)
  expand_public_seed(V_tr, PK->seed_pub);
#elif defined(RSDPG)
  FZ_ELEM W_mat[M][N - M];
  expand_public_seed(V_tr, W_mat, PK->seed_pub);
#endif

  FQ_ELEM pub_syn[N - K];
  unpack_fq_syn(pub_syn, PK->s);

  send_unsigned("init beta: ", hal_checkstack());
  // This will hold:
  // 1. digest_msg
  // 2. digest_cmt
  // 3. Salt
  uint8_t beta_buf[2 * HASH_DIGEST_LENGTH + SALT_LENGTH_BYTES];
  uint8_t *m_new = beta_buf;
  // uint8_t *m_new1=beta_buf;
  size_t dlen = 0, dlen1 = 0, dlen2 = 0;
  CSPRNG_STATE_T csprng_state1, csprng_state2;
  CSPRNG_STATE_T csprng_state;

#if defined(CATEGORY_1)
  uint8_t r = SHAKE128_RATE;
#if defined(NO_TREES)
#else
#endif
#else
  uint8_t r = SHA3_256_RATE;
#if defined(NO_TREES)
#else
#endif
#endif

  // Compute digest_msg and put it in the first part of
  // beta_buf

  // hash(beta_buf,(uint8_t*) m,mlen);
  m_new = (uint8_t *)m;
  dlen = mlen;
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update_new(&csprng_state, m_new, &dlen, (uint8_t *)m, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state, beta_buf, HASH_DIGEST_LENGTH);
  send_unsigned("hash beta stack:", hal_checkstack());

  // Put digest_cmt and Salt from the signature in beta buf to
  // form:
  //  beta_buf = digest_msg | digest_cmt | Salt
  memcpy(beta_buf + HASH_DIGEST_LENGTH, sig->digest_01, HASH_DIGEST_LENGTH);
  memcpy(beta_buf + 2 * HASH_DIGEST_LENGTH, sig->salt, SALT_LENGTH_BYTES);

  // Calculate digest_chall_1 from beta_buf

  uint8_t d_beta[HASH_DIGEST_LENGTH];
  // hash(d_beta,beta_buf,sizeof(beta_buf));
  m_new = beta_buf;
  dlen = sizeof(beta_buf);
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update_new(&csprng_state, m_new, &dlen, beta_buf, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state, d_beta, HASH_DIGEST_LENGTH);

  // Beta is chall_1, calculate from CSPRNG

  FQ_ELEM beta[T];
  initialize_csprng(&CSPRNG_state, d_beta, HASH_DIGEST_LENGTH);
  CSPRNG_fq_vec_beta(beta, &CSPRNG_state);

  uint8_t fixed_weight_b[T] = {0};
  expand_digest_to_fixed_weight(fixed_weight_b, sig->digest_b);

#if defined(NO_TREES)
  uint8_t rounds_seeds[T * SEED_LENGTH_BYTES] = {0};
  regenerate_round_seeds(rounds_seeds, fixed_weight_b, sig->stp);
#else
  uint8_t seed_tree[SEED_LENGTH_BYTES * NUM_NODES_SEED_TREE] = {0};
  regenerate_round_seeds(seed_tree, fixed_weight_b, sig->stp, sig->salt);
  uint8_t *rounds_seeds =
      seed_tree + SEED_LENGTH_BYTES * NUM_INNER_NODES_SEED_TREE;
#endif

#if defined(RSDP)
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#elif defined(RSDPG)
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#endif
  /* cmt_0_i_input is syndrome||sigma ||salt */
  memcpy(cmt_0_i_input + offset_salt, sig->salt, SALT_LENGTH_BYTES);

  /* cmt_1_i_input is concat(seed,salt,round index) */
  uint8_t
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t)];
  memcpy(cmt_1_i_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);

#if defined(NO_TREES)
  uint8_t cmt_0[T][HASH_DIGEST_LENGTH] = {0};
#else
  uint8_t cmt_0_new[HASH_DIGEST_LENGTH] = {0};
#endif
  // uint8_t cmt_1[T][HASH_DIGEST_LENGTH] = {0};
  uint8_t cmt_1_new[r + HASH_DIGEST_LENGTH];

  for (int i = 0; i < r + HASH_DIGEST_LENGTH; i++) {
    cmt_1_new[i] = 0;
  }
  uint8_t commit_digests[2][HASH_DIGEST_LENGTH];
  // xof_shake_init_new(&csprng_state1, SEED_LENGTH_BYTES*8);
  FZ_ELEM eta_tilde[N];
  FQ_ELEM u_tilde[N];

  FQ_ELEM y_tilde[N] = {0};
  FQ_ELEM s_tilde[N - K] = {0};

  // FQ_ELEM y[T][N];

  int used_rsps = 0;
  int is_signature_ok = 1;
  uint8_t digest_b_buf[DENSELY_PACKED_FQ_VEC_SIZE + r];
  uint8_t digest_b_recomputed[HASH_DIGEST_LENGTH];
  xof_shake_init_new(&csprng_state2, SEED_LENGTH_BYTES * 8);
  xof_shake_init_new(&csprng_state1, SEED_LENGTH_BYTES * 8);
#if defined(NO_TREES)
#else
  unsigned char tree[NUM_NODES_MERKLE_TREE * HASH_DIGEST_LENGTH];
  uint16_t flag_tree_valid[NUM_NODES_MERKLE_TREE] = {INVALID_MERKLE_NODE};

  uint16_t merkle_leaf_indices[T];
  uint16_t layer_offsets[LOG2(T) + 1];
  uint16_t nodes_per_layer[LOG2(T) + 1];

  uint16_t ctr;
  unsigned int node_ctr, parent_layer;
  size_t i;

  unsigned char hash_input[2 * HASH_DIGEST_LENGTH];

  setup_tree(layer_offsets, nodes_per_layer);
  get_leaf_indices(merkle_leaf_indices, layer_offsets);
#endif
  for (uint16_t i = 0; i < T; i++) {

    /* i+c */
    uint16_t domain_sep_i = i + NUM_NODES_SEED_TREE;
    /* i+c+dsc */
    uint16_t domain_sep_idx_hash = domain_sep_i + HASH_CSPRNG_DOMAIN_SEP_CONST;

    if (fixed_weight_b[i] == 1) {
      memcpy(cmt_1_i_input, rounds_seeds + SEED_LENGTH_BYTES * i,
             SEED_LENGTH_BYTES);

      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES] =
          (domain_sep_idx_hash >> 8) & 0xFF;
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + 1] =
          domain_sep_idx_hash & 0xFF;
      // hash(cmt_1[i],cmt_1_i_input,sizeof(cmt_1_i_input));
      m_new = cmt_1_i_input;
      dlen = sizeof(cmt_1_i_input);
      xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
      xof_shake_update_new(&csprng_state, m_new, &dlen, cmt_1_i_input, 1);
      xof_shake_final_new(&csprng_state);
      xof_shake_extract_new(&csprng_state, cmt_1_new + dlen1,
                            HASH_DIGEST_LENGTH);

      /* CSPRNG is fed with concat(seed,salt,round index) represented
       * as a 2 bytes little endian unsigned integer */
      const int csprng_input_length =
          SALT_LENGTH_BYTES + SEED_LENGTH_BYTES + sizeof(uint16_t);
      uint8_t csprng_input[csprng_input_length];
      memcpy(csprng_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);
      memcpy(csprng_input, rounds_seeds + SEED_LENGTH_BYTES * i,
             SEED_LENGTH_BYTES);
      csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES] =
          (domain_sep_i >> 8) & 0xFF;
      csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES + 1] =
          domain_sep_i & 0xFF;

      /* expand seed[i] into seed_e and seed_u */
      initialize_csprng(&CSPRNG_state, csprng_input, csprng_input_length);
#if defined(RSDP)
      /* expand eta_tilde */
      CSPRNG_zz_vec(eta_tilde, &CSPRNG_state);
#elif defined(RSDPG)
      FZ_ELEM zeta_tilde[M];
      CSPRNG_zz_inf_w(zeta_tilde, &CSPRNG_state);
      fz_inf_w_by_fz_matrix(eta_tilde, zeta_tilde, W_mat);
      fz_dz_norm_sigma(eta_tilde);
#endif
      /* expand u_tilde */
      CSPRNG_fq_vec(u_tilde, &CSPRNG_state);
      fq_vec_by_restr_vec_scaled(u_tilde, eta_tilde, beta[i], u_tilde);
      fq_dz_norm(u_tilde);
    } else {
      /* place y[i] in the buffer for later on hashing */
      unpack_fq_vec(u_tilde, sig->rsp_0[used_rsps].y);
      FZ_ELEM sigma_local[N];
#if defined(RSDP)
      /*sigma is memcpy'ed directly into cmt_0 input buffer */
      FZ_ELEM *sigma_ptr = cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE;
      unpack_fz_vec(sigma_local, sig->rsp_0[used_rsps].sigma);
      memcpy(sigma_ptr, &sig->rsp_0[used_rsps].sigma,
             DENSELY_PACKED_FZ_VEC_SIZE);
      is_signature_ok =
          is_signature_ok && is_zz_vec_in_restr_group(sigma_local);
#elif defined(RSDPG)
      /*delta is memcpy'ed directly into cmt_0 input buffer */
      FZ_ELEM *delta_ptr = cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE;
      memcpy(delta_ptr, &sig->rsp_0[used_rsps].delta,
             DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE);
      FZ_ELEM delta_local[M];
      unpack_fz_rsdp_g_vec(delta_local, sig->rsp_0[used_rsps].delta);
      is_signature_ok = is_signature_ok && is_zz_inf_w_valid(delta_local);
      fz_inf_w_by_fz_matrix(sigma_local, delta_local, W_mat);

#endif
      memcpy(cmt_1_new + dlen1, sig->rsp_1[used_rsps], HASH_DIGEST_LENGTH);
      used_rsps++;

      FQ_ELEM v[N];
      convert_restr_vec_to_fq(v, sigma_local);
      fq_vec_by_fq_vec_pointwise(y_tilde, v, u_tilde);
      fq_vec_by_fq_matrix(s_tilde, y_tilde, V_tr);
      fq_dz_norm_synd(s_tilde);
      FQ_ELEM to_compress[N - K];
      fq_synd_minus_fq_vec_scaled(to_compress, s_tilde, beta[i], pub_syn);
      fq_dz_norm_synd(to_compress);
      pack_fq_syn(cmt_0_i_input, to_compress);
      cmt_0_i_input[offset_round_idx] = (domain_sep_idx_hash >> 8) & 0xFF;
      cmt_0_i_input[offset_round_idx + 1] = domain_sep_idx_hash & 0xFF;
#if defined(NO_TREES)
      hash(cmt_0[i], cmt_0_i_input, sizeof(cmt_0_i_input));
#else
      m_new = cmt_0_i_input;
      dlen = sizeof(cmt_0_i_input);
      xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
      xof_shake_update_new(&csprng_state, m_new, &dlen, cmt_0_i_input, 1);
      xof_shake_final_new(&csprng_state);
      xof_shake_extract_new(&csprng_state, cmt_0_new, HASH_DIGEST_LENGTH);

      flag_tree_valid[merkle_leaf_indices[i]] = VALID_MERKLE_NODE;
      memcpy(tree + merkle_leaf_indices[i] * HASH_DIGEST_LENGTH, cmt_0_new,
             HASH_DIGEST_LENGTH);
#endif
    }
    dlen1 += HASH_DIGEST_LENGTH;
    m_new = cmt_1_new;
    if (dlen1 > r && i != T - 1)
      xof_shake_update_new(&csprng_state1, m_new, &dlen1, cmt_1_new, 0);
    if (i == (T - 1)) {
      m_new = cmt_1_new;
      xof_shake_update_new(&csprng_state1, m_new, &dlen1, cmt_1_new, 1);
      xof_shake_final_new(&csprng_state1);
      xof_shake_extract_new(&csprng_state1, commit_digests[1],
                            HASH_DIGEST_LENGTH);
    }

    pack_fq_vec(digest_b_buf + dlen2, u_tilde);
    dlen2 += DENSELY_PACKED_FQ_VEC_SIZE;
    m_new = digest_b_buf;
    if (dlen2 > r) {
      xof_shake_update_new(&csprng_state2, m_new, &dlen2, digest_b_buf, 0);
    }
    if (i == T - 1) {
      memcpy(digest_b_buf + dlen2, d_beta, HASH_DIGEST_LENGTH);
      dlen2 += HASH_DIGEST_LENGTH;
      m_new = digest_b_buf;
      xof_shake_update_new(&csprng_state2, m_new, &dlen2, digest_b_buf, 1);
      xof_shake_final_new(&csprng_state2);
      xof_shake_extract_new(&csprng_state2, digest_b_recomputed,
                            HASH_DIGEST_LENGTH);
    }
  } /* end for iterating on ZKID iterations */

  // Remove assert
  // assert(is_signature_ok)

  // uint8_t commit_digests[2][HASH_DIGEST_LENGTH];
  /*merkle_tree_root_recompute(commit_digests[0],
                             cmt_0,
                             sig->mtp,
                             fixed_weight_b);*/
  // unsigned char tree[NUM_NODES_MERKLE_TREE * HASH_DIGEST_LENGTH];

  // rebuild_merkle_tree(tree, sig->mtp, cmt_0, fixed_weight_b);

  /*uint16_t flag_tree_valid[NUM_NODES_MERKLE_TREE] = {INVALID_MERKLE_NODE};

  uint16_t merkle_leaf_indices[T];
  uint16_t layer_offsets[LOG2(T)+1];
  uint16_t nodes_per_layer[LOG2(T)+1];

  uint16_t ctr;
  unsigned int node_ctr, parent_layer;
  size_t i;


  unsigned char hash_input[2*HASH_DIGEST_LENGTH];


  setup_tree(layer_offsets, nodes_per_layer);
  get_leaf_indices(merkle_leaf_indices, layer_offsets);*/

  /*for (i=0; i<T; i++) {
      if (fixed_weight_b[i] == CHALLENGE_PROOF_VALUE) {
          flag_tree_valid[merkle_leaf_indices[i]] = VALID_MERKLE_NODE;
          memcpy(tree + merkle_leaf_indices[i]*HASH_DIGEST_LENGTH, cmt_0 + i,
  HASH_DIGEST_LENGTH);
      }
  }*/
#if defined(NO_TREES)
  merkle_tree_root_recompute(commit_digests[0], cmt_0, sig->mtp,
                             fixed_weight_b);
#else
  ctr = 0;
  node_ctr = 0;
  parent_layer = LOG2(T) - 1;
  for (i = NUM_NODES_MERKLE_TREE - 1; i > 0; i -= 2) {

    if (flag_tree_valid[i] == INVALID_MERKLE_NODE &&
        flag_tree_valid[SIBLING(i)] == INVALID_MERKLE_NODE) {
      if (node_ctr >= nodes_per_layer[parent_layer + 1] - 2) {
        parent_layer--;
        node_ctr = 0;
      } else {
        node_ctr += 2;
      }
      continue;
    }

    if (flag_tree_valid[i] == VALID_MERKLE_NODE) {
      memcpy(hash_input + HASH_DIGEST_LENGTH, tree + OFFSET(i),
             HASH_DIGEST_LENGTH);
    } else {
      memcpy(hash_input + HASH_DIGEST_LENGTH, sig->mtp + OFFSET(ctr),
             HASH_DIGEST_LENGTH);
      ctr++;
    }

    if (flag_tree_valid[SIBLING(i)] == VALID_MERKLE_NODE) {
      memcpy(hash_input, tree + OFFSET(SIBLING(i)), HASH_DIGEST_LENGTH);
    } else {
      memcpy(hash_input, sig->mtp + OFFSET(ctr), HASH_DIGEST_LENGTH);
      ctr++;
    }

    // hash(tree + OFFSET(PARENT(i) + layer_offsets[parent_layer]), hash_input,
    // 2*HASH_DIGEST_LENGTH);
    m_new = hash_input;
    dlen = 2 * HASH_DIGEST_LENGTH;
    xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
    xof_shake_update_new(&csprng_state, m_new, &dlen, hash_input, 1);
    xof_shake_final_new(&csprng_state);
    xof_shake_extract_new(
        &csprng_state, tree + OFFSET(PARENT(i) + layer_offsets[parent_layer]),
        HASH_DIGEST_LENGTH);

    flag_tree_valid[PARENT(i) + layer_offsets[parent_layer]] =
        VALID_MERKLE_NODE;

    if (node_ctr >= nodes_per_layer[parent_layer + 1] - 2) {
      parent_layer--;
      node_ctr = 0;
    } else {
      node_ctr += 2;
    }
  }

  memcpy(commit_digests[0], tree, HASH_DIGEST_LENGTH);
#endif
  // hash(commit_digests[1], (unsigned char*)cmt_1, sizeof(cmt_1));
  /*m_new = (unsigned char*)cmt_1;
  dlen = sizeof(cmt_1);
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES*8);
  xof_shake_update_new(&csprng_state, m_new, &dlen, (unsigned char*)cmt_1, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state, commit_digests[1],HASH_DIGEST_LENGTH);*/
  uint8_t digest_01_recomputed[HASH_DIGEST_LENGTH];
  /*hash(digest_01_recomputed,
            (unsigned char*) commit_digests,
            sizeof(commit_digests));*/

  m_new = (unsigned char *)commit_digests;
  dlen = sizeof(commit_digests);
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES * 8);
  xof_shake_update_new(&csprng_state, m_new, &dlen,
                       (unsigned char *)commit_digests, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state, digest_01_recomputed,
                        HASH_DIGEST_LENGTH);

  /*uint8_t digest_b_buf[T*DENSELY_PACKED_FQ_VEC_SIZE+HASH_DIGEST_LENGTH];
  for(int x = 0; x < T; x++){
      pack_fq_vec(digest_b_buf+(x*DENSELY_PACKED_FQ_VEC_SIZE),y[x]);
  }
  memcpy(digest_b_buf+T*DENSELY_PACKED_FQ_VEC_SIZE,d_beta,HASH_DIGEST_LENGTH);*/

  // uint8_t digest_b_recomputed[HASH_DIGEST_LENGTH];
  // hash(digest_b_recomputed, digest_b_buf, sizeof(digest_b_buf));
  /*m_new = digest_b_buf;
  dlen = sizeof(digest_b_buf);
  xof_shake_init_new(&csprng_state, SEED_LENGTH_BYTES*8);
  xof_shake_update_new(&csprng_state, m_new, &dlen, digest_b_buf, 1);
  xof_shake_final_new(&csprng_state);
  xof_shake_extract_new(&csprng_state,
  digest_b_recomputed,HASH_DIGEST_LENGTH);*/

  // Don't bother local variables, if statement will shortcircuit.
  // Remove assert
  if (is_signature_ok ||
      (memcmp(digest_01_recomputed, sig->digest_01, HASH_DIGEST_LENGTH) == 0) ||
      (memcmp(digest_b_recomputed, sig->digest_b, HASH_DIGEST_LENGTH) == 0))
    return 1;
  return 0;
}

/* sign cannot fail */
void CROSS_sign_old(const prikey_t *SK, const char *const m,
                    const uint64_t mlen, sig_t *sig) {
  /* Wipe any residual information in the sig structure allocated by the
   * caller */
  memset(sig, 0, sizeof(sig_t));
  /* Key material expansion */
  FQ_ELEM V_tr[K][N - K];
  FZ_ELEM eta[N];
#if defined(RSDP)
  expand_private_seed(eta, V_tr, SK->seed);
#elif defined(RSDPG)
  FZ_ELEM zeta[M];
  FZ_ELEM W_mat[M][N - M];
  expand_private_seed(eta, zeta, V_tr, W_mat, SK->seed);
#endif

  uint8_t root_seed[SEED_LENGTH_BYTES];
  randombytes(root_seed, SEED_LENGTH_BYTES);
  randombytes(sig->salt, SALT_LENGTH_BYTES);

#if defined(NO_TREES)
  unsigned char rounds_seeds[T * SEED_LENGTH_BYTES] = {0};
  compute_round_seeds(rounds_seeds, root_seed, sig->salt);
#else
  uint8_t seed_tree[SEED_LENGTH_BYTES * NUM_NODES_SEED_TREE] = {0};
  generate_seed_tree_from_root(seed_tree, root_seed, sig->salt);
  uint8_t *rounds_seeds =
      seed_tree + SEED_LENGTH_BYTES * NUM_INNER_NODES_SEED_TREE;
#endif

  FZ_ELEM eta_tilde[T][N];
  FZ_ELEM sigma[T][N];
  FQ_ELEM u_tilde[T][N];
  FQ_ELEM s_tilde[N - K];

#if defined(RSDP)
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#elif defined(RSDPG)
  FZ_ELEM zeta_tilde[M];
  FZ_ELEM delta[T][M];
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#endif
  /* cmt_0_i_input is syndrome||sigma ||salt ; place salt at the end */
  memcpy(cmt_0_i_input + offset_salt, sig->salt, SALT_LENGTH_BYTES);

  uint8_t
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t)];
  /* cmt_1_i_input is concat(seed,salt,round index) */
  memcpy(cmt_1_i_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);

  uint8_t cmt_0[T][HASH_DIGEST_LENGTH] = {0};
  uint8_t cmt_1[T][HASH_DIGEST_LENGTH] = {0};

  CSPRNG_STATE_T CSPRNG_state;
  for (uint16_t i = 0; i < T; i++) {
    /* CSPRNG is fed with concat(seed,salt,round index) represented
     * as a 2 bytes little endian unsigned integer */
    uint8_t
        csprng_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t)];
    memcpy(csprng_input, rounds_seeds + SEED_LENGTH_BYTES * i,
           SEED_LENGTH_BYTES);
    memcpy(csprng_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);
    /* i+c */
    uint16_t domain_sep_i = i + NUM_NODES_SEED_TREE;
    csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES] =
        (domain_sep_i >> 8) & 0xFF;
    csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES + 1] =
        domain_sep_i & 0xFF;

    /* expand seed[i] into seed_e and seed_u */
    initialize_csprng(&CSPRNG_state, csprng_input,
                      SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t));
    /* expand eta_tilde */
#if defined(RSDP)
    CSPRNG_zz_vec(eta_tilde[i], &CSPRNG_state);
#elif defined(RSDPG)
    CSPRNG_zz_inf_w(zeta_tilde, &CSPRNG_state);
    restr_inf_w_sub(delta[i], zeta, zeta_tilde);
    fz_dz_norm_delta(delta[i]);
    fz_inf_w_by_fz_matrix(eta_tilde[i], zeta_tilde, W_mat);
    fz_dz_norm_sigma(eta_tilde[i]);
#endif
    restr_vec_sub(sigma[i], eta, eta_tilde[i]);

    FQ_ELEM v[N];
    convert_restr_vec_to_fq(v, sigma[i]);
    fz_dz_norm_sigma(sigma[i]);
    /* expand u_tilde */
    CSPRNG_fq_vec(u_tilde[i], &CSPRNG_state);

    FQ_ELEM u[N];
    fq_vec_by_fq_vec_pointwise(u, v, u_tilde[i]);
    fq_vec_by_fq_matrix(s_tilde, u, V_tr);
    fq_dz_norm_synd(s_tilde);

    /* cmt_0_i_input contains s-tilde || sigma_i || salt */
    pack_fq_syn(cmt_0_i_input, s_tilde);

#if defined(RSDP)
    pack_fz_vec(cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE, sigma[i]);
#elif defined(RSDPG)
    pack_fz_rsdp_g_vec(cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE, delta[i]);
#endif
    /* Fixed endianness marshalling of round counter
     * i+c+dsc */
    uint16_t domain_sep_idx_hash = domain_sep_i + HASH_CSPRNG_DOMAIN_SEP_CONST;
    cmt_0_i_input[offset_round_idx] = (domain_sep_idx_hash >> 8) & 0xFF;
    cmt_0_i_input[offset_round_idx + 1] = domain_sep_idx_hash & 0xFF;

    hash(cmt_0[i], cmt_0_i_input, sizeof(cmt_0_i_input));
    memcpy(cmt_1_i_input, rounds_seeds + SEED_LENGTH_BYTES * i,
           SEED_LENGTH_BYTES);

    cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES] =
        (domain_sep_idx_hash >> 8) & 0xFF;
    cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + 1] =
        domain_sep_idx_hash & 0xFF;
    hash(cmt_1[i], cmt_1_i_input, sizeof(cmt_1_i_input));
  }

  /* vector containing d_0 and d_1 from spec */
  uint8_t commit_digests[2][HASH_DIGEST_LENGTH];
#if defined(NO_TREES)
  merkle_tree_root_compute(commit_digests[0], cmt_0);
#else
  uint8_t merkle_tree_0[NUM_NODES_MERKLE_TREE * HASH_DIGEST_LENGTH];
  merkle_tree_root_compute(commit_digests[0], merkle_tree_0, cmt_0);
#endif
  hash(commit_digests[1], (unsigned char *)cmt_1, sizeof(cmt_1));
  hash(sig->digest_01, (unsigned char *)commit_digests, sizeof(commit_digests));

  /* first challenge extraction */
  uint8_t beta_buf[2 * HASH_DIGEST_LENGTH + SALT_LENGTH_BYTES];
  /* place d_m at the beginning of the input of the hash generating d_beta*/
  hash(beta_buf, (uint8_t *)m, mlen);
  memcpy(beta_buf + HASH_DIGEST_LENGTH, sig->digest_01, HASH_DIGEST_LENGTH);
  memcpy(beta_buf + 2 * HASH_DIGEST_LENGTH, sig->salt, SALT_LENGTH_BYTES);

  uint8_t d_beta[HASH_DIGEST_LENGTH];
  hash(d_beta, beta_buf, 2 * HASH_DIGEST_LENGTH + SALT_LENGTH_BYTES);

  FQ_ELEM beta[T];
  initialize_csprng(&CSPRNG_state, d_beta, HASH_DIGEST_LENGTH);
  CSPRNG_fq_vec_beta(beta, &CSPRNG_state);

  /* Computation of the first round of responses */
  FQ_ELEM y[T][N];
  for (int i = 0; i < T; i++) {
    fq_vec_by_restr_vec_scaled(y[i], eta_tilde[i], beta[i], u_tilde[i]);
    fq_dz_norm(y[i]);
  }
  /* y vectors are packed before being hashed */
  uint8_t digest_b_buf[T * DENSELY_PACKED_FQ_VEC_SIZE + HASH_DIGEST_LENGTH];
  for (int x = 0; x < T; x++) {
    pack_fq_vec(digest_b_buf + (x * DENSELY_PACKED_FQ_VEC_SIZE), y[x]);
  }
  /* Second challenge extraction */
  memcpy(digest_b_buf + T * DENSELY_PACKED_FQ_VEC_SIZE, d_beta,
         HASH_DIGEST_LENGTH);

  hash(sig->digest_b, digest_b_buf, sizeof(digest_b_buf));

  uint8_t fixed_weight_b[T] = {0};
  expand_digest_to_fixed_weight(fixed_weight_b, sig->digest_b);

  /* Computation of the second round of responses */

#if defined(NO_TREES)
  merkle_tree_proof_compute(sig->mtp, cmt_0, fixed_weight_b);
  publish_round_seeds(sig->stp, rounds_seeds, fixed_weight_b);
#else
  merkle_tree_proof_compute(sig->mtp, merkle_tree_0, cmt_0, fixed_weight_b);
  publish_seeds(sig->stp, seed_tree, fixed_weight_b);
#endif

  int published_rsps = 0;
  for (int i = 0; i < T; i++) {
    if (fixed_weight_b[i] == 0) {
      assert(published_rsps < T - W);
      pack_fq_vec(sig->rsp_0[published_rsps].y, y[i]);
#if defined(RSDP)
      pack_fz_vec(sig->rsp_0[published_rsps].sigma, sigma[i]);
#elif defined(RSDPG)
      pack_fz_rsdp_g_vec(sig->rsp_0[published_rsps].delta, delta[i]);
#endif
      memcpy(sig->rsp_1[published_rsps], cmt_1[i], HASH_DIGEST_LENGTH);
      published_rsps++;
    }
  }
}

/* verify returns 1 if signature is ok, 0 otherwise */
int CROSS_verify_old(const pubkey_t *const PK, const char *const m,
                     const uint64_t mlen, const sig_t *const sig) {
  CSPRNG_STATE_T CSPRNG_state;

  FQ_ELEM V_tr[K][N - K];
#if defined(RSDP)
  expand_public_seed(V_tr, PK->seed_pub);
#elif defined(RSDPG)
  FZ_ELEM W_mat[M][N - M];
  expand_public_seed(V_tr, W_mat, PK->seed_pub);
#endif

  FQ_ELEM pub_syn[N - K];
  unpack_fq_syn(pub_syn, PK->s);

  uint8_t beta_buf[2 * HASH_DIGEST_LENGTH + SALT_LENGTH_BYTES];
  hash(beta_buf, (uint8_t *)m, mlen);
  memcpy(beta_buf + HASH_DIGEST_LENGTH, sig->digest_01, HASH_DIGEST_LENGTH);
  memcpy(beta_buf + 2 * HASH_DIGEST_LENGTH, sig->salt, SALT_LENGTH_BYTES);

  uint8_t d_beta[HASH_DIGEST_LENGTH];
  hash(d_beta, beta_buf, sizeof(beta_buf));

  FQ_ELEM beta[T];
  initialize_csprng(&CSPRNG_state, d_beta, HASH_DIGEST_LENGTH);
  CSPRNG_fq_vec_beta(beta, &CSPRNG_state);

  uint8_t fixed_weight_b[T] = {0};
  expand_digest_to_fixed_weight(fixed_weight_b, sig->digest_b);

#if defined(NO_TREES)
  uint8_t rounds_seeds[T * SEED_LENGTH_BYTES] = {0};
  regenerate_round_seeds(rounds_seeds, fixed_weight_b, sig->stp);
#else
  uint8_t seed_tree[SEED_LENGTH_BYTES * NUM_NODES_SEED_TREE] = {0};
  regenerate_round_seeds(seed_tree, fixed_weight_b, sig->stp, sig->salt);
  uint8_t *rounds_seeds =
      seed_tree + SEED_LENGTH_BYTES * NUM_INNER_NODES_SEED_TREE;
#endif

#if defined(RSDP)
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#elif defined(RSDPG)
  uint8_t cmt_0_i_input[DENSELY_PACKED_FQ_SYN_SIZE +
                        DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE + SALT_LENGTH_BYTES +
                        sizeof(uint16_t)];
  const int offset_salt =
      DENSELY_PACKED_FQ_SYN_SIZE + DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE;
  const int offset_round_idx = offset_salt + SALT_LENGTH_BYTES;
#endif
  /* cmt_0_i_input is syndrome||sigma ||salt */
  memcpy(cmt_0_i_input + offset_salt, sig->salt, SALT_LENGTH_BYTES);

  /* cmt_1_i_input is concat(seed,salt,round index) */
  uint8_t
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + sizeof(uint16_t)];
  memcpy(cmt_1_i_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);

  uint8_t cmt_0[T][HASH_DIGEST_LENGTH] = {0};
  uint8_t cmt_1[T][HASH_DIGEST_LENGTH] = {0};

  FZ_ELEM eta_tilde[N];
  FQ_ELEM u_tilde[N];

  FQ_ELEM y_tilde[N] = {0};
  FQ_ELEM s_tilde[N - K] = {0};

  FQ_ELEM y[T][N];

  int used_rsps = 0;
  int is_signature_ok = 1;
  for (uint16_t i = 0; i < T; i++) {

    /* i+c */
    uint16_t domain_sep_i = i + NUM_NODES_SEED_TREE;
    /* i+c+dsc */
    uint16_t domain_sep_idx_hash = domain_sep_i + HASH_CSPRNG_DOMAIN_SEP_CONST;

    if (fixed_weight_b[i] == 1) {
      memcpy(cmt_1_i_input, rounds_seeds + SEED_LENGTH_BYTES * i,
             SEED_LENGTH_BYTES);

      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES] =
          (domain_sep_idx_hash >> 8) & 0xFF;
      cmt_1_i_input[SEED_LENGTH_BYTES + SALT_LENGTH_BYTES + 1] =
          domain_sep_idx_hash & 0xFF;
      hash(cmt_1[i], cmt_1_i_input, sizeof(cmt_1_i_input));

      /* CSPRNG is fed with concat(seed,salt,round index) represented
       * as a 2 bytes little endian unsigned integer */
      const int csprng_input_length =
          SALT_LENGTH_BYTES + SEED_LENGTH_BYTES + sizeof(uint16_t);
      uint8_t csprng_input[csprng_input_length];
      memcpy(csprng_input + SEED_LENGTH_BYTES, sig->salt, SALT_LENGTH_BYTES);
      memcpy(csprng_input, rounds_seeds + SEED_LENGTH_BYTES * i,
             SEED_LENGTH_BYTES);
      csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES] =
          (domain_sep_i >> 8) & 0xFF;
      csprng_input[SALT_LENGTH_BYTES + SEED_LENGTH_BYTES + 1] =
          domain_sep_i & 0xFF;

      /* expand seed[i] into seed_e and seed_u */
      initialize_csprng(&CSPRNG_state, csprng_input, csprng_input_length);
#if defined(RSDP)
      /* expand eta_tilde */
      CSPRNG_zz_vec(eta_tilde, &CSPRNG_state);
#elif defined(RSDPG)
      FZ_ELEM zeta_tilde[M];
      CSPRNG_zz_inf_w(zeta_tilde, &CSPRNG_state);
      fz_inf_w_by_fz_matrix(eta_tilde, zeta_tilde, W_mat);
      fz_dz_norm_sigma(eta_tilde);
#endif
      /* expand u_tilde */
      CSPRNG_fq_vec(u_tilde, &CSPRNG_state);
      fq_vec_by_restr_vec_scaled(y[i], eta_tilde, beta[i], u_tilde);
      fq_dz_norm(y[i]);
    } else {
      /* place y[i] in the buffer for later on hashing */
      unpack_fq_vec(y[i], sig->rsp_0[used_rsps].y);

      FZ_ELEM sigma_local[N];
#if defined(RSDP)
      /*sigma is memcpy'ed directly into cmt_0 input buffer */
      FZ_ELEM *sigma_ptr = cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE;
      unpack_fz_vec(sigma_local, sig->rsp_0[used_rsps].sigma);
      memcpy(sigma_ptr, &sig->rsp_0[used_rsps].sigma,
             DENSELY_PACKED_FZ_VEC_SIZE);
      is_signature_ok =
          is_signature_ok && is_zz_vec_in_restr_group(sigma_local);
#elif defined(RSDPG)
      /*delta is memcpy'ed directly into cmt_0 input buffer */
      FZ_ELEM *delta_ptr = cmt_0_i_input + DENSELY_PACKED_FQ_SYN_SIZE;
      memcpy(delta_ptr, &sig->rsp_0[used_rsps].delta,
             DENSELY_PACKED_FZ_RSDP_G_VEC_SIZE);
      FZ_ELEM delta_local[M];
      unpack_fz_rsdp_g_vec(delta_local, sig->rsp_0[used_rsps].delta);
      is_signature_ok = is_signature_ok && is_zz_inf_w_valid(delta_local);
      fz_inf_w_by_fz_matrix(sigma_local, delta_local, W_mat);

#endif
      memcpy(cmt_1[i], sig->rsp_1[used_rsps], HASH_DIGEST_LENGTH);
      used_rsps++;

      FQ_ELEM v[N];
      convert_restr_vec_to_fq(v, sigma_local);
      fq_vec_by_fq_vec_pointwise(y_tilde, v, y[i]);
      fq_vec_by_fq_matrix(s_tilde, y_tilde, V_tr);
      fq_dz_norm_synd(s_tilde);
      FQ_ELEM to_compress[N - K];
      fq_synd_minus_fq_vec_scaled(to_compress, s_tilde, beta[i], pub_syn);
      fq_dz_norm_synd(to_compress);
      pack_fq_syn(cmt_0_i_input, to_compress);
      cmt_0_i_input[offset_round_idx] = (domain_sep_idx_hash >> 8) & 0xFF;
      cmt_0_i_input[offset_round_idx + 1] = domain_sep_idx_hash & 0xFF;

      hash(cmt_0[i], cmt_0_i_input, sizeof(cmt_0_i_input));
    }
  } /* end for iterating on ZKID iterations */

  assert(is_signature_ok);

  uint8_t commit_digests[2][HASH_DIGEST_LENGTH];
  merkle_tree_root_recompute(commit_digests[0], cmt_0, sig->mtp,
                             fixed_weight_b);
  hash(commit_digests[1], (unsigned char *)cmt_1, sizeof(cmt_1));

  uint8_t digest_01_recomputed[HASH_DIGEST_LENGTH];
  hash(digest_01_recomputed, (unsigned char *)commit_digests,
       sizeof(commit_digests));

  uint8_t digest_b_buf[T * DENSELY_PACKED_FQ_VEC_SIZE + HASH_DIGEST_LENGTH];
  for (int x = 0; x < T; x++) {
    pack_fq_vec(digest_b_buf + (x * DENSELY_PACKED_FQ_VEC_SIZE), y[x]);
  }
  memcpy(digest_b_buf + T * DENSELY_PACKED_FQ_VEC_SIZE, d_beta,
         HASH_DIGEST_LENGTH);

  uint8_t digest_b_recomputed[HASH_DIGEST_LENGTH];
  hash(digest_b_recomputed, digest_b_buf, sizeof(digest_b_buf));

  int does_digest_01_match =
      (memcmp(digest_01_recomputed, sig->digest_01, HASH_DIGEST_LENGTH) == 0);
  assert(does_digest_01_match);

  int does_digest_b_match =
      (memcmp(digest_b_recomputed, sig->digest_b, HASH_DIGEST_LENGTH) == 0);
  assert(does_digest_b_match);

  is_signature_ok =
      is_signature_ok && does_digest_01_match && does_digest_b_match;
  return is_signature_ok;
}
