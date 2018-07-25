/* Copyright (c) 2017 David Kaloper Meršinjak. All rights reserved.
   See LICENSE.md. */

/* Generic table-driven GHASH.
 *
 * References:
 * - The Galois/Counter Mode of Operation. David A. McGrew and John Viega.
 * - NIST SP 800-38D. Recommendation for Block Cipher Modes of Operation:
 *   Galois/Counter Mode (GCM) and GMAC.
 */

/*  LARGE_TABLES -> 65K per key
 * !LARGE_TABLES -> 8K per key, ~3x slower. */

#include "../nocrypto.h"
#if !defined (__nc_PCLMUL__)

#include <string.h>


#if defined (__NC_GHASH_LARGE_TABLES)
#define __t_width  8     // coefficient window
#define __t_tables 16    // 128 / t_width
#define __t_size   4096  // 2^t_width * t_tables
#else
#define __t_width  4
#define __t_tables 32
#define __t_size   512
#endif

#ifdef HAVE_UINT128_T

#define __set_uint128_t(w1, w0) (((__uint128_t) w1 << 64) | w0)

static const __uint128_t r = __set_uint128_t (0xe100000000000000, 0);

static inline __uint128_t __load_128_t (const uint64_t s[2]) {
  return __set_uint128_t (be64toh (s[0]), be64toh (s[1]));
}

static inline __uint128_t __load_128_t_with_padding (const uint8_t *src, size_t n) {
  uint64_t buf[2] = { 0 };
  memcpy (buf, src, n);
  return __load_128_t (buf);
}

static inline void __store_128_t (uint64_t s[2], __uint128_t x) {
  s[0] = htobe64 (x >> 64);
  s[1] = htobe64 (x);
}

static inline __uint128_t __gfmul (__uint128_t a, __uint128_t b) {
  __uint128_t z = 0,
              v = a;
  for (int i = 0; i < 128; i ++) {
    if ((uint64_t) (b >> (127 - i)) & 1)
      z = z ^ v;
    v = (uint64_t) v & 1 ? (v >> 1) ^ r : v >> 1;
  }
  return z;
}

// NB Exponents are reversed.
// TODO: Fast table derivation.
static inline void __derive (uint64_t key[2], __uint128_t m[__t_size]) {
  __uint128_t e = 1 << (__t_width - 1),
              h = __load_128_t (key);
  for (int i = 0; i < __t_tables; i ++, e <<= __t_width) {
    __uint128_t exph = __gfmul (h, e);
    for (int j = 0; j < (1 << __t_width); j ++)
      m[(i << __t_width) | j] = __gfmul (exph, (__uint128_t) j << (128 - __t_width));
  }
}

#define __t_mask ((1 << __t_width) - 1)
static inline __uint128_t __gfmul_tab (__uint128_t m[__t_size], __uint128_t x) {
  __uint128_t r = 0;
  for (int i = 0; i < __t_tables; i ++)
    r ^= m[(i << __t_width) | ((uint8_t) (x >> (i * __t_width)) & __t_mask)];
  return r;
}

static inline void __ghash (__uint128_t m[__t_size], uint64_t hash[2], const uint8_t *src, size_t n) {
  __uint128_t acc = __load_128_t (hash);
  for (; n >= 16; src += 16, n -= 16)
    acc = __gfmul_tab (m, acc ^ __load_128_t ((uint64_t *) src));
  if (n > 0)
    acc = __gfmul_tab (m, acc ^ __load_128_t_with_padding (src, n));
  __store_128_t (hash, acc);
}

#else

#include <gmp.h>

typedef mpz_t __uint128_t;


/* #### UINT128 HELPERS #### */
static inline void
u128_init_from_u32 (__uint128_t ret, uint32_t hi, uint32_t mh, uint32_t ml,
	           uint32_t lo)
{
  mpz_init2  (ret, 128);
  /* mpn_z::_mp_size is total number of mpz_z::_mp_d being used to represent
     the number (for instance, if mpz_z::_mp_size of 2 the number can be
     represented in a 64-bits variable.  */
  ret->_mp_size = 4;

  ret->_mp_d[3] = hi;
  if (hi == 0)
    ret->_mp_size--;
  ret->_mp_d[2] = mh;
  if (mh == 0 && hi == 0)
    ret->_mp_size--;
  ret->_mp_d[1] = ml;
  if (ml == 0 && mh == 0 && hi == 0)
    ret->_mp_size--;
  ret->_mp_d[0] = lo;
  if (lo == 0 && ml == 0 && mh == 0 && hi == 0)
    ret->_mp_size--;
}

static inline 
void 
u128_init_from_u64 (__uint128_t res, const uint64_t s[2]) 
{
  u128_init_from_u32(res, s[0] >> 32, s[0], s[1] >> 32, s[1]);
}

static __uint128_t r;

static inline 
void 
u128_init_with_padding (__uint128_t res, const uint8_t *src, size_t n) {
  uint32_t buf[4] = { 0 };
  memcpy (buf, src, n);
  u128_init_from_u32 (res, buf[0], buf[1], buf[2], buf[3]);
}

static inline 
uint32_t
__u128_extract_u32 (mpz_t x, int word)
{
  return (x->_mp_size >= (word + 1)) ? x->_mp_d[word] : 0UL;
}

static inline
uint64_t
__u128_extract_64(mpz_t x, int word)
{
  uint64_t ret;
  ret   = __u128_extract_u32(x, 2*word+1);
  ret <<= 32;
  ret  |= __u128_extract_u32(x, 2*word);
  return ret;
}

#define u128_init(__x) mpz_init2 (__x, 128)

/* #### GASH TABLE COMPUTATION #### */

static inline 
void 
__gfmul (__uint128_t result, __uint128_t a, __uint128_t b) {
  __uint128_t v;
  u128_init(v);

  mpz_set_ui(result, 0);
  mpz_set(v, a);

  for (int i = 0; i < 128; i ++) {
    if (mpz_tstbit(b, 127-i)) {
      mpz_xor(result, result, v);
    }

    if (mpz_tstbit(v, 0)) { // v >> 1
      mpz_div_2exp(v, v, 1);
    } else { // (v >> 1) ^ r
      mpz_div_2exp(v, v, 1);
      mpz_xor(v, v, r);
    }
  }
  mpz_clear(v);
}

// NB Exponents are reversed.
// TODO: Fast table derivation.
static inline void __derive (uint64_t key[2], __uint128_t m[__t_size]) {
  __uint128_t e, h, exph, tmp;
  
  u128_init_from_u32(e, 0, 0, 0, 1 << (__t_width - 1));
  u128_init_from_u64(h, key);
  u128_init(exph);
  u128_init(tmp);

  for (int i = 0; i < __t_tables; i ++, mpz_mul_2exp(e, e, __t_width)) 
  {
    __gfmul(exph, h, e);
    for (int j = 0; j < (1 << __t_width); j ++) {
      u128_init (m[(i << __t_width) | j]);
      mpz_set_si(tmp, j);
      mpz_mul_2exp(tmp, tmp, 128 - __t_width);
      __gfmul (m[(i << __t_width) | j], exph, tmp);
    }
  }

  mpz_clear(exph);
  mpz_clear(tmp);
  mpz_clear(h);
  mpz_clear(e);
}


/* #### GHASH COMPUTATION USING THE TABLE #### */
#define __t_mask ((1 << __t_width) - 1)
static inline void __gfmul_tab (__uint128_t result, __uint128_t m[__t_size], __uint128_t x) {
  mpz_set_ui(result, 0);

  __uint128_t table_index;
  mpz_init(table_index);

  for (int i = 0; i < __t_tables; i ++) {
    mpz_div_2exp(table_index, x, i * __t_width);
    int index = (i << __t_width) | ((uint8_t) (mpz_get_ui(table_index)) & __t_mask);
    mpz_xor(result, result, m[index]);
  }

  mpz_clear(table_index);
}

static inline void __ghash (__uint128_t m[__t_size], uint64_t hash[2], const uint8_t *src, size_t n) {
  __uint128_t acc, tmp;
  u128_init_from_u64(acc, hash);

  for (; n >= 16; src += 16, n -= 16) {
    u128_init_from_u32(tmp, ((uint32_t *) src)[0], ((uint32_t *) src)[1], ((uint32_t *) src)[2], ((uint32_t *) src)[3]);
    mpz_xor(tmp, tmp, acc);
    __gfmul_tab (acc, m, tmp);
    mpz_clear(tmp);
  }

  if (n > 0) {
    u128_init_with_padding(tmp, src, n);
    mpz_xor(tmp, tmp, acc);
    __gfmul_tab (acc, m, tmp);
    mpz_clear(tmp);
  }

  hash[0] = __u128_extract_64(acc, 0);
  hash[1] = __u128_extract_64(acc, 1);
  mpz_clear(acc);
}

#endif

/* #### CAML BINDINGS #### */
CAMLprim value caml_nc_ghash_key_size (__unit ()) {
  return Val_int (sizeof(__uint128_t) * __t_size);
}

static const uint64_t val[] = {0xe100000000000000, 0};

CAMLprim value caml_nc_ghash_init_key (value key, value off, value m) {
  u128_init_from_u64 (r, val);
  __derive ((uint64_t *) _ba_uint8_off (key, off), (__uint128_t *) Bp_val (m));
  mpz_clear(r);
  return Val_unit;
}

CAMLprim value
caml_nc_ghash (value m, value hash, value src, value off, value len) {
  __ghash ((__uint128_t *) Bp_val (m), (uint64_t *) Bp_val (hash),
           _ba_uint8_off (src, off), Int_val (len) );
  return Val_unit;
}

CAMLprim value caml_nc_ghash_mode (__unit ()) { return Val_int (0); }

#endif /* __nc_PCLMUL__ */
