/* Based on the public domain implementation in
 * crypto_hash/sha512/ref/ from http://bench.cr.yp.to/supercop.html
 * by D. J. Bernstein */

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "sha2.h"
#include "crypto_hashblocks_sha512.h"

#ifdef PROFILE_HASHING
#include "hal.h"
extern unsigned long long hash_cycles;
#endif

static uint32_t load_bigendian_32(const uint8_t *x) {
    return (uint32_t)(x[3]) | (((uint32_t)(x[2])) << 8) |
           (((uint32_t)(x[1])) << 16) | (((uint32_t)(x[0])) << 24);
}

static uint64_t load_bigendian_64(const uint8_t *x) {
    return (uint64_t)(x[7]) | (((uint64_t)(x[6])) << 8) |
           (((uint64_t)(x[5])) << 16) | (((uint64_t)(x[4])) << 24) |
           (((uint64_t)(x[3])) << 32) | (((uint64_t)(x[2])) << 40) |
           (((uint64_t)(x[1])) << 48) | (((uint64_t)(x[0])) << 56);
}

static void store_bigendian_32(uint8_t *x, uint64_t u) {
    x[3] = (uint8_t) u;
    u >>= 8;
    x[2] = (uint8_t) u;
    u >>= 8;
    x[1] = (uint8_t) u;
    u >>= 8;
    x[0] = (uint8_t) u;
}

static void store_bigendian_64(uint8_t *x, uint64_t u) {
    x[7] = (uint8_t) u;
    u >>= 8;
    x[6] = (uint8_t) u;
    u >>= 8;
    x[5] = (uint8_t) u;
    u >>= 8;
    x[4] = (uint8_t) u;
    u >>= 8;
    x[3] = (uint8_t) u;
    u >>= 8;
    x[2] = (uint8_t) u;
    u >>= 8;
    x[1] = (uint8_t) u;
    u >>= 8;
    x[0] = (uint8_t) u;
}

#define SHR(x, c) ((x) >> (c))
#define ROTR_32(x, c) (((x) >> (c)) | ((x) << (32 - (c))))

#define Ch(x, y, z) (((x) & (y)) ^ (~(x) & (z)))
#define Maj(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))

#define Sigma0_32(x) (ROTR_32(x, 2) ^ ROTR_32(x,13) ^ ROTR_32(x,22))
#define Sigma1_32(x) (ROTR_32(x, 6) ^ ROTR_32(x,11) ^ ROTR_32(x,25))
#define sigma0_32(x) (ROTR_32(x, 7) ^ ROTR_32(x,18) ^ SHR(x, 3))
#define sigma1_32(x) (ROTR_32(x,17) ^ ROTR_32(x,19) ^ SHR(x,10))

#define M_32(w0, w14, w9, w1) w0 = sigma1_32(w14) + (w9) + sigma0_32(w1) + (w0);

#define EXPAND_32           \
    M_32(w0, w14, w9, w1)   \
    M_32(w1, w15, w10, w2)  \
    M_32(w2, w0, w11, w3)   \
    M_32(w3, w1, w12, w4)   \
    M_32(w4, w2, w13, w5)   \
    M_32(w5, w3, w14, w6)   \
    M_32(w6, w4, w15, w7)   \
    M_32(w7, w5, w0, w8)    \
    M_32(w8, w6, w1, w9)    \
    M_32(w9, w7, w2, w10)   \
    M_32(w10, w8, w3, w11)  \
    M_32(w11, w9, w4, w12)  \
    M_32(w12, w10, w5, w13) \
    M_32(w13, w11, w6, w14) \
    M_32(w14, w12, w7, w15) \
    M_32(w15, w13, w8, w0)

#define F_32(w, k)                                 \
    T1 = h + Sigma1_32(e) + Ch(e, f, g) + (k) + (w); \
    T2 = Sigma0_32(a) + Maj(a, b, c);                \
    h = g;                                           \
    g = f;                                           \
    f = e;                                           \
    e = d + T1;                                      \
    d = c;                                           \
    c = b;                                           \
    b = a;                                           \
    a = T1 + T2;


static size_t crypto_hashblocks_sha256(uint8_t *statebytes,
                                   const uint8_t *in, size_t inlen) {
    uint32_t state[8];
    uint32_t a;
    uint32_t b;
    uint32_t c;
    uint32_t d;
    uint32_t e;
    uint32_t f;
    uint32_t g;
    uint32_t h;
    uint32_t T1;
    uint32_t T2;

    a = load_bigendian_32(statebytes + 0);
    state[0] = a;
    b = load_bigendian_32(statebytes + 4);
    state[1] = b;
    c = load_bigendian_32(statebytes + 8);
    state[2] = c;
    d = load_bigendian_32(statebytes + 12);
    state[3] = d;
    e = load_bigendian_32(statebytes + 16);
    state[4] = e;
    f = load_bigendian_32(statebytes + 20);
    state[5] = f;
    g = load_bigendian_32(statebytes + 24);
    state[6] = g;
    h = load_bigendian_32(statebytes + 28);
    state[7] = h;

    while (inlen >= 64) {
        uint32_t w0  = load_bigendian_32(in + 0);
        uint32_t w1  = load_bigendian_32(in + 4);
        uint32_t w2  = load_bigendian_32(in + 8);
        uint32_t w3  = load_bigendian_32(in + 12);
        uint32_t w4  = load_bigendian_32(in + 16);
        uint32_t w5  = load_bigendian_32(in + 20);
        uint32_t w6  = load_bigendian_32(in + 24);
        uint32_t w7  = load_bigendian_32(in + 28);
        uint32_t w8  = load_bigendian_32(in + 32);
        uint32_t w9  = load_bigendian_32(in + 36);
        uint32_t w10 = load_bigendian_32(in + 40);
        uint32_t w11 = load_bigendian_32(in + 44);
        uint32_t w12 = load_bigendian_32(in + 48);
        uint32_t w13 = load_bigendian_32(in + 52);
        uint32_t w14 = load_bigendian_32(in + 56);
        uint32_t w15 = load_bigendian_32(in + 60);

        F_32(w0, 0x428a2f98)
        F_32(w1, 0x71374491)
        F_32(w2, 0xb5c0fbcf)
        F_32(w3, 0xe9b5dba5)
        F_32(w4, 0x3956c25b)
        F_32(w5, 0x59f111f1)
        F_32(w6, 0x923f82a4)
        F_32(w7, 0xab1c5ed5)
        F_32(w8, 0xd807aa98)
        F_32(w9, 0x12835b01)
        F_32(w10, 0x243185be)
        F_32(w11, 0x550c7dc3)
        F_32(w12, 0x72be5d74)
        F_32(w13, 0x80deb1fe)
        F_32(w14, 0x9bdc06a7)
        F_32(w15, 0xc19bf174)

        EXPAND_32

        F_32(w0, 0xe49b69c1)
        F_32(w1, 0xefbe4786)
        F_32(w2, 0x0fc19dc6)
        F_32(w3, 0x240ca1cc)
        F_32(w4, 0x2de92c6f)
        F_32(w5, 0x4a7484aa)
        F_32(w6, 0x5cb0a9dc)
        F_32(w7, 0x76f988da)
        F_32(w8, 0x983e5152)
        F_32(w9, 0xa831c66d)
        F_32(w10, 0xb00327c8)
        F_32(w11, 0xbf597fc7)
        F_32(w12, 0xc6e00bf3)
        F_32(w13, 0xd5a79147)
        F_32(w14, 0x06ca6351)
        F_32(w15, 0x14292967)

        EXPAND_32

        F_32(w0, 0x27b70a85)
        F_32(w1, 0x2e1b2138)
        F_32(w2, 0x4d2c6dfc)
        F_32(w3, 0x53380d13)
        F_32(w4, 0x650a7354)
        F_32(w5, 0x766a0abb)
        F_32(w6, 0x81c2c92e)
        F_32(w7, 0x92722c85)
        F_32(w8, 0xa2bfe8a1)
        F_32(w9, 0xa81a664b)
        F_32(w10, 0xc24b8b70)
        F_32(w11, 0xc76c51a3)
        F_32(w12, 0xd192e819)
        F_32(w13, 0xd6990624)
        F_32(w14, 0xf40e3585)
        F_32(w15, 0x106aa070)

        EXPAND_32

        F_32(w0, 0x19a4c116)
        F_32(w1, 0x1e376c08)
        F_32(w2, 0x2748774c)
        F_32(w3, 0x34b0bcb5)
        F_32(w4, 0x391c0cb3)
        F_32(w5, 0x4ed8aa4a)
        F_32(w6, 0x5b9cca4f)
        F_32(w7, 0x682e6ff3)
        F_32(w8, 0x748f82ee)
        F_32(w9, 0x78a5636f)
        F_32(w10, 0x84c87814)
        F_32(w11, 0x8cc70208)
        F_32(w12, 0x90befffa)
        F_32(w13, 0xa4506ceb)
        F_32(w14, 0xbef9a3f7)
        F_32(w15, 0xc67178f2)

        a += state[0];
        b += state[1];
        c += state[2];
        d += state[3];
        e += state[4];
        f += state[5];
        g += state[6];
        h += state[7];

        state[0] = a;
        state[1] = b;
        state[2] = c;
        state[3] = d;
        state[4] = e;
        state[5] = f;
        state[6] = g;
        state[7] = h;

        in += 64;
        inlen -= 64;
    }

    store_bigendian_32(statebytes + 0, state[0]);
    store_bigendian_32(statebytes + 4, state[1]);
    store_bigendian_32(statebytes + 8, state[2]);
    store_bigendian_32(statebytes + 12, state[3]);
    store_bigendian_32(statebytes + 16, state[4]);
    store_bigendian_32(statebytes + 20, state[5]);
    store_bigendian_32(statebytes + 24, state[6]);
    store_bigendian_32(statebytes + 28, state[7]);

    return inlen;
}

static const uint8_t iv_224[32] = {
    0xc1, 0x05, 0x9e, 0xd8, 0x36, 0x7c, 0xd5, 0x07,
    0x30, 0x70, 0xdd, 0x17, 0xf7, 0x0e, 0x59, 0x39,
    0xff, 0xc0, 0x0b, 0x31, 0x68, 0x58, 0x15, 0x11,
    0x64, 0xf9, 0x8f, 0xa7, 0xbe, 0xfa, 0x4f, 0xa4
};

static const uint8_t iv_256[32] = {
    0x6a, 0x09, 0xe6, 0x67, 0xbb, 0x67, 0xae, 0x85,
    0x3c, 0x6e, 0xf3, 0x72, 0xa5, 0x4f, 0xf5, 0x3a,
    0x51, 0x0e, 0x52, 0x7f, 0x9b, 0x05, 0x68, 0x8c,
    0x1f, 0x83, 0xd9, 0xab, 0x5b, 0xe0, 0xcd, 0x19
};

static const uint8_t iv_384[64] = {
    0xcb, 0xbb, 0x9d, 0x5d, 0xc1, 0x05, 0x9e, 0xd8, 0x62, 0x9a, 0x29,
    0x2a, 0x36, 0x7c, 0xd5, 0x07, 0x91, 0x59, 0x01, 0x5a, 0x30, 0x70,
    0xdd, 0x17, 0x15, 0x2f, 0xec, 0xd8, 0xf7, 0x0e, 0x59, 0x39, 0x67,
    0x33, 0x26, 0x67, 0xff, 0xc0, 0x0b, 0x31, 0x8e, 0xb4, 0x4a, 0x87,
    0x68, 0x58, 0x15, 0x11, 0xdb, 0x0c, 0x2e, 0x0d, 0x64, 0xf9, 0x8f,
    0xa7, 0x47, 0xb5, 0x48, 0x1d, 0xbe, 0xfa, 0x4f, 0xa4
};

static const uint8_t iv_512[64] = {
    0x6a, 0x09, 0xe6, 0x67, 0xf3, 0xbc, 0xc9, 0x08, 0xbb, 0x67, 0xae,
    0x85, 0x84, 0xca, 0xa7, 0x3b, 0x3c, 0x6e, 0xf3, 0x72, 0xfe, 0x94,
    0xf8, 0x2b, 0xa5, 0x4f, 0xf5, 0x3a, 0x5f, 0x1d, 0x36, 0xf1, 0x51,
    0x0e, 0x52, 0x7f, 0xad, 0xe6, 0x82, 0xd1, 0x9b, 0x05, 0x68, 0x8c,
    0x2b, 0x3e, 0x6c, 0x1f, 0x1f, 0x83, 0xd9, 0xab, 0xfb, 0x41, 0xbd,
    0x6b, 0x5b, 0xe0, 0xcd, 0x19, 0x13, 0x7e, 0x21, 0x79
};

void sha224_inc_init(sha224ctx *state) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    for (size_t i = 0; i < 32; ++i) {
        state->ctx[i] = iv_224[i];
    }
    for (size_t i = 32; i < 40; ++i) {
        state->ctx[i] = 0;
    }

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}

void sha256_inc_init(sha256ctx *state) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    for (size_t i = 0; i < 32; ++i) {
        state->ctx[i] = iv_256[i];
    }
    for (size_t i = 32; i < 40; ++i) {
        state->ctx[i] = 0;
    }

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}

void sha384_inc_init(sha384ctx *state) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    for (size_t i = 0; i < 64; ++i) {
        state->ctx[i] = iv_384[i];
    }
    for (size_t i = 64; i < 72; ++i) {
        state->ctx[i] = 0;
    }

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}

void sha512_inc_init(sha512ctx *state) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    for (size_t i = 0; i < 64; ++i) {
        state->ctx[i] = iv_512[i];
    }
    for (size_t i = 64; i < 72; ++i) {
        state->ctx[i] = 0;
    }

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}

void sha224_inc_ctx_clone(sha224ctx *stateout, const sha224ctx *statein) {
    memcpy(stateout, statein, sizeof(sha224ctx));
}

void sha256_inc_ctx_clone(sha256ctx *stateout, const sha256ctx *statein) {
    memcpy(stateout, statein, sizeof(sha256ctx));
}

void sha384_inc_ctx_clone(sha384ctx *stateout, const sha384ctx *statein) {
    memcpy(stateout, statein, sizeof(sha384ctx));
}

void sha512_inc_ctx_clone(sha512ctx *stateout, const sha512ctx *statein) {
    memcpy(stateout, statein, sizeof(sha512ctx));
}

/* Destroy the hash state.
 *
 * Because this implementation is stack-based, this is a no-op
 */
void sha224_inc_ctx_release(sha224ctx *state) {
    (void)state;
}

/* Destroy the hash state.
 *
 * Because this implementation is stack-based, this is a no-op
 */
void sha256_inc_ctx_release(sha256ctx *state) {
    (void)state;
}

/* Destroy the hash state.
 *
 * Because this implementation is stack-based, this is a no-op
 */
void sha384_inc_ctx_release(sha384ctx *state) {
    (void)state;
}

/* Destroy the hash state.
 *
 * Because this implementation is stack-based, this is a no-op
 */
void sha512_inc_ctx_release(sha512ctx *state) {
    (void)state;
}


void sha256_inc_blocks(sha256ctx *state, const uint8_t *in, size_t inblocks) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    uint64_t bytes = load_bigendian_64(state->ctx + 32);

    crypto_hashblocks_sha256(state->ctx, in, 64 * inblocks);
    bytes += 64 * inblocks;

    store_bigendian_64(state->ctx + 32, bytes);

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}

void sha224_inc_blocks(sha224ctx *state, const uint8_t *in, size_t inblocks) {
    sha256_inc_blocks((sha256ctx*) state, in, inblocks);
}

void sha512_inc_blocks(sha512ctx *state, const uint8_t *in, size_t inblocks) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    uint64_t bytes = load_bigendian_64(state->ctx + 64);

    crypto_hashblocks_sha512(state->ctx, in, 128 * inblocks);
    bytes += 128 * inblocks;

    store_bigendian_64(state->ctx + 64, bytes);

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}

void sha384_inc_blocks(sha384ctx *state, const uint8_t *in, size_t inblocks) {
    sha512_inc_blocks((sha512ctx*) state, in, inblocks);
}

void sha256_inc_finalize(uint8_t *out, sha256ctx *state, const uint8_t *in, size_t inlen) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    uint8_t padded[128];
    uint64_t bytes = load_bigendian_64(state->ctx + 32) + inlen;

    crypto_hashblocks_sha256(state->ctx, in, inlen);
    in += inlen;
    inlen &= 63;
    in -= inlen;

    for (size_t i = 0; i < inlen; ++i) {
        padded[i] = in[i];
    }
    padded[inlen] = 0x80;

    if (inlen < 56) {
        for (size_t i = inlen + 1; i < 56; ++i) {
            padded[i] = 0;
        }
        padded[56] = (uint8_t) (bytes >> 53);
        padded[57] = (uint8_t) (bytes >> 45);
        padded[58] = (uint8_t) (bytes >> 37);
        padded[59] = (uint8_t) (bytes >> 29);
        padded[60] = (uint8_t) (bytes >> 21);
        padded[61] = (uint8_t) (bytes >> 13);
        padded[62] = (uint8_t) (bytes >> 5);
        padded[63] = (uint8_t) (bytes << 3);
        crypto_hashblocks_sha256(state->ctx, padded, 64);
    } else {
        for (size_t i = inlen + 1; i < 120; ++i) {
            padded[i] = 0;
        }
        padded[120] = (uint8_t) (bytes >> 53);
        padded[121] = (uint8_t) (bytes >> 45);
        padded[122] = (uint8_t) (bytes >> 37);
        padded[123] = (uint8_t) (bytes >> 29);
        padded[124] = (uint8_t) (bytes >> 21);
        padded[125] = (uint8_t) (bytes >> 13);
        padded[126] = (uint8_t) (bytes >> 5);
        padded[127] = (uint8_t) (bytes << 3);
        crypto_hashblocks_sha256(state->ctx, padded, 128);
    }

    for (size_t i = 0; i < 32; ++i) {
        out[i] = state->ctx[i];
    }

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}


void sha224_inc_finalize(uint8_t *out, sha224ctx *state, const uint8_t *in, size_t inlen) {
    sha256_inc_finalize(state->ctx, (sha256ctx*)state, in, inlen);

    for (size_t i = 0; i < 28; ++i) {
        out[i] = state->ctx[i];
    }
}

void sha512_inc_finalize(uint8_t *out, sha512ctx *state, const uint8_t *in, size_t inlen) {
#ifdef PROFILE_HASHING
    uint64_t t0 = hal_get_time();
#endif

    uint8_t padded[256];
    uint64_t bytes = load_bigendian_64(state->ctx + 64) + inlen;

    crypto_hashblocks_sha512(state->ctx, in, inlen);
    in += inlen;
    inlen &= 127;
    in -= inlen;

    for (size_t i = 0; i < inlen; ++i) {
        padded[i] = in[i];
    }
    padded[inlen] = 0x80;

    if (inlen < 112) {
        for (size_t i = inlen + 1; i < 119; ++i) {
            padded[i] = 0;
        }
        padded[119] = (uint8_t) (bytes >> 61);
        padded[120] = (uint8_t) (bytes >> 53);
        padded[121] = (uint8_t) (bytes >> 45);
        padded[122] = (uint8_t) (bytes >> 37);
        padded[123] = (uint8_t) (bytes >> 29);
        padded[124] = (uint8_t) (bytes >> 21);
        padded[125] = (uint8_t) (bytes >> 13);
        padded[126] = (uint8_t) (bytes >> 5);
        padded[127] = (uint8_t) (bytes << 3);
        crypto_hashblocks_sha512(state->ctx, padded, 128);
    } else {
        for (size_t i = inlen + 1; i < 247; ++i) {
            padded[i] = 0;
        }
        padded[247] = (uint8_t) (bytes >> 61);
        padded[248] = (uint8_t) (bytes >> 53);
        padded[249] = (uint8_t) (bytes >> 45);
        padded[250] = (uint8_t) (bytes >> 37);
        padded[251] = (uint8_t) (bytes >> 29);
        padded[252] = (uint8_t) (bytes >> 21);
        padded[253] = (uint8_t) (bytes >> 13);
        padded[254] = (uint8_t) (bytes >> 5);
        padded[255] = (uint8_t) (bytes << 3);
        crypto_hashblocks_sha512(state->ctx, padded, 256);
    }

    for (size_t i = 0; i < 64; ++i) {
        out[i] = state->ctx[i];
    }

#ifdef PROFILE_HASHING
    uint64_t t1 = hal_get_time();
    hash_cycles += (t1-t0);
#endif
}

void sha384_inc_finalize(uint8_t *out, sha384ctx *state, const uint8_t *in, size_t inlen) {
    sha512_inc_finalize(state->ctx, (sha512ctx*)state, in, inlen);

    for (size_t i = 0; i < 48; ++i) {
        out[i] = state->ctx[i];
    }
}

void sha224(uint8_t *out, const uint8_t *in, size_t inlen) {
    sha224ctx state;

    sha224_inc_init(&state);
    sha224_inc_finalize(out, &state, in, inlen);
}

void sha256(uint8_t *out, const uint8_t *in, size_t inlen) {
    sha256ctx state;

    sha256_inc_init(&state);
    sha256_inc_finalize(out, &state, in, inlen);
}

void sha384(uint8_t *out, const uint8_t *in, size_t inlen) {
    sha384ctx state;

    sha384_inc_init(&state);
    sha384_inc_finalize(out, &state, in, inlen);
}

void sha512(uint8_t *out, const uint8_t *in, size_t inlen) {
    sha512ctx state;

    sha512_inc_init(&state);
    sha512_inc_finalize(out, &state, in, inlen);
}
