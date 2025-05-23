// SPDX-License-Identifier: Apache-2.0 or CC0-1.0
#include "api.h"
#include "hal.h"
#include "randombytes.h"
#include "sendfn.h"

#include <stdio.h>
#include <string.h>

#ifndef MAX_STACK_SIZE
#define MAX_STACK_SIZE hal_get_stack_size()
#endif

#ifndef STACK_SIZE_INCR
#define STACK_SIZE_INCR 0x1000
#endif

#define MLEN 32
// https://stackoverflow.com/a/1489985/1711232
#define PASTER(x, y) x##y
#define EVALUATOR(x, y) PASTER(x, y)
#define NAMESPACE(fun) EVALUATOR(MUPQ_NAMESPACE, fun)

// use different names so we can have empty namespaces
#define MUPQ_CRYPTO_PUBLICKEYBYTES NAMESPACE(CRYPTO_PUBLICKEYBYTES)
#define MUPQ_CRYPTO_SECRETKEYBYTES NAMESPACE(CRYPTO_SECRETKEYBYTES)
#define MUPQ_CRYPTO_BYTES NAMESPACE(CRYPTO_BYTES)
#define MUPQ_CRYPTO_ALGNAME NAMESPACE(CRYPTO_ALGNAME)

#define MUPQ_crypto_sign_keypair NAMESPACE(crypto_sign_keypair)
#define MUPQ_crypto_sign NAMESPACE(crypto_sign)
#define MUPQ_crypto_sign_open NAMESPACE(crypto_sign_open)
#define MUPQ_crypto_sign_signature NAMESPACE(crypto_sign_signature)
#define MUPQ_crypto_sign_verify NAMESPACE(crypto_sign_verify)

#define send_stack_usage(S, U) send_unsigned((S), (U))

unsigned char pk[MUPQ_CRYPTO_PUBLICKEYBYTES];
unsigned char sk[MUPQ_CRYPTO_SECRETKEYBYTES];
unsigned char sm[MLEN + MUPQ_CRYPTO_BYTES];
unsigned char m[MLEN];

size_t mlen;
size_t smlen;
unsigned int rc;
unsigned int stack_key_gen, stack_sign, stack_verify;

static int test_sign(void) {
  // Alice generates a public key
  MUPQ_crypto_sign_keypair(pk, sk);

  // Bob derives a secret key and creates a response
  randombytes(m, MLEN);
  MUPQ_crypto_sign(sm, &smlen, m, MLEN, sk);

  // Alice uses Bobs response to get her secret key
  // Loop forever for profiling
  while (1) {
    rc = MUPQ_crypto_sign_open(sm, &mlen, sm, smlen, pk);
  }
}

int main(void) {
  hal_setup(CLOCK_FAST);

  // marker for automated benchmarks
  hal_send_str("==========================");
  test_sign();
  // marker for automated benchmarks
  hal_send_str("#");

  return 0;
}
