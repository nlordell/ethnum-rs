#include <stdbool.h>
#include <stdint.h>

typedef unsigned _BitInt(256) u256;
typedef signed _BitInt(256) i256;

// Shifting by >= BITS is undefined behavior.
#define SHIFT_MASK 255

#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#define EXPORT(ty, name) extern ty __ethnum_##name

EXPORT(void, add2)(u256 *r, const u256 *a) { *r += *a; }

EXPORT(void, add3)(u256 *r, const u256 *a, const u256 *b) { *r = *a + *b; }

EXPORT(bool, uaddc)(u256 *r, const u256 *a, const u256 *b) {
#if __has_builtin(__builtin_add_overflow)
  return __builtin_add_overflow(*a, *b, r);
#else
  u256 res = *a + *b;
  bool ov = res < *a;
  *r = res;
  return ov;
#endif
}

EXPORT(bool, iaddc)(i256 *r, const i256 *a, const i256 *b) {
#if __has_builtin(__builtin_add_overflow)
  return __builtin_add_overflow(*a, *b, r);
#else
  i256 res = *a + *b;
  bool ov = ((*a > 0 && *b > 0 && res < 0) || (*a < 0 && *b < 0 && res > 0));
  *r = res;
  return ov;
#endif
}

EXPORT(void, sub2)(u256 *r, const u256 *a) { *r -= *a; }

EXPORT(void, sub3)(u256 *r, const u256 *a, const u256 *b) { *r = *a - *b; }

EXPORT(bool, usubc)(u256 *r, const u256 *a, const u256 *b) {
#if __has_builtin(__builtin_sub_overflow)
  return __builtin_sub_overflow(*a, *b, r);
#else
  bool ov = *a < *b;
  *r = *a - *b;
  return ov;
#endif
}

EXPORT(bool, isubc)(i256 *r, const i256 *a, const i256 *b) {
#if __has_builtin(__builtin_sub_overflow)
  return __builtin_sub_overflow(*a, *b, r);
#else
  i256 res = *a - *b;
  bool ov = ((*a >= 0 && *b < 0 && res < 0) || (*a < 0 && *b >= 0 && res >= 0));
  *r = res;
  return ov;
#endif
}

EXPORT(void, mul2)(u256 *r, const u256 *a) { *r *= *a; }

EXPORT(void, mul3)(u256 *r, const u256 *a, const u256 *b) { *r = *a * *b; }

EXPORT(bool, umulc)(u256 *r, const u256 *a, const u256 *b) {
#if __has_builtin(__builtin_mul_overflow)
  return __builtin_mul_overflow(*a, *b, r);
#else
  u256 res = *a * *b;
  bool ov = (*a != 0 && *b != 0 && (res / *a != *b || res / *b != *a));
  *r = res;
  return ov;
#endif
}

EXPORT(bool, imulc)(i256 *r, const i256 *a, const i256 *b) {
  // TODO: clang doesn't support > 128 bits
  #if __has_builtin(__builtin_mul_overflow) && !defined(__clang__)
   return __builtin_mul_overflow(*a, *b, r);
  #else
  i256 res = *a * *b;
  bool ov =
      ((*a != 0 && *b != 0 && (res / *a != *b || res / *b != *a)) ||
       (*a == -1 && *b == -1 && res > 0) || (*a == -1 && *b == 1 && res < 0) ||
       (*a == 1 && *b == -1 && res < 0));
  *r = res;
  return ov;
  #endif
}

EXPORT(void, udiv2)(u256 *r, const u256 *a) { *r /= *a; }
EXPORT(void, udiv3)(u256 *r, const u256 *a, const u256 *b) { *r = *a / *b; }
EXPORT(void, urem2)(u256 *r, const u256 *a) { *r %= *a; }
EXPORT(void, urem3)(u256 *r, const u256 *a, const u256 *b) { *r = *a % *b; }

EXPORT(void, idiv2)(i256 *r, const i256 *a) { *r /= *a; }
EXPORT(void, idiv3)(i256 *r, const i256 *a, const i256 *b) { *r = *a / *b; }
EXPORT(void, irem2)(i256 *r, const i256 *a) { *r %= *a; }
EXPORT(void, irem3)(i256 *r, const i256 *a, const i256 *b) { *r = *a % *b; }

EXPORT(void, shl2)(u256 *r, uint32_t a) { *r <<= (a & SHIFT_MASK); }

EXPORT(void, shl3)(u256 *r, const u256 *a, uint32_t b) {
  *r = *a << (b & SHIFT_MASK);
}

EXPORT(void, sar2)(i256 *r, uint32_t a) { *r >>= (a & SHIFT_MASK); }

EXPORT(void, sar3)(i256 *r, const i256 *a, uint32_t b) {
  *r = *a >> (b & SHIFT_MASK);
}

EXPORT(void, shr2)(u256 *r, uint32_t a) { *r >>= (a & SHIFT_MASK); }

EXPORT(void, shr3)(u256 *r, const u256 *a, uint32_t b) {
  *r = *a >> (b & SHIFT_MASK);
}

EXPORT(void, rol3)(u256 *r, const u256 *a, uint32_t b) {
  b &= SHIFT_MASK;
  *r = (*a << b) | (*a >> (256 - b));
}

EXPORT(void, ror3)(u256 *r, const u256 *a, uint32_t b) {
  b &= SHIFT_MASK;
  *r = (*a >> b) | (*a << (256 - b));
}

EXPORT(uint32_t, ctlz)(const u256 *a) {
#if __has_builtin(__builtin_clzg)
  return __builtin_clzg(*a, 256);
#else
// TODO
#endif
}

EXPORT(uint32_t, cttz)(const u256 *a) {
#if __has_builtin(__builtin_ctzg)
  return __builtin_ctzg(*a, 256);
#else
// TODO
#endif
}
