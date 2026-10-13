/* easing.h: the readings of motion of lean4-whatwg, in C.
 *
 * A transcription, line by line, of the readings as Whatwg/Svg/Scene/Machine.lean writes them
 * for a machine (mix?, Easing.stopsOf?, Easing.cubicOf?, Easing.of?, Easing.at?,
 * Transition.at?, Change.at?), which are proved equal to the readings of
 * Whatwg/Svg/Scene/Motion.lean. It is a reading aid. The test is the table,
 * motion-readings.tsv, which easing_test.c reads.
 *
 * Two things to keep when this is copied into a player.
 *
 * 1. Every division is fdiv. C's `/` rounds toward zero and Lean's rounds down; they differ
 *    wherever a negative number does not divide evenly: in mix of a value that rises, at
 *    every moment before its end; in a cubic below 0; and in stops that fall.
 * 2. Every number is 64 bits wide. A cubic at the half of a duration of 270 has the term
 *    1000 * 135 * 135 * 135, which 32 bits do not hold. On data that passes the test `Small`
 *    of Machine.lean no value is 2^63 or more in size (Track.at?_eq), so nothing here
 *    overflows: stops and heights within 100000, a duration of 10000 at most, a delay and a
 *    moment of a thousand million at most, coordinates within a thousand million.
 *
 * WHATWG_INT is the type of every number. It is int64_t. The test sets it to int32_t to show
 * that the table catches a narrow transcription, and WHATWG_TOWARD_ZERO to show that it
 * catches C's own division.
 *
 * C99. No dependency beyond <stdint.h>.
 */
#ifndef WHATWG_EASING_H
#define WHATWG_EASING_H

#include <stdint.h>

#ifndef WHATWG_INT
#define WHATWG_INT int64_t
#endif
typedef WHATWG_INT wint;

/* fdiv a b: division that rounds down, for a divisor that is not negative, and 0 for the
 * divisor 0. Lean: `if b = 0 then 0 else if a.tmod b < 0 then a.tdiv b - 1 else a.tdiv b`,
 * and `fdiv_eq : 0 <= b -> fdiv a b = a / b`. */
static inline wint fdiv(wint a, wint b) {
  if (b == 0) return 0;
#ifdef WHATWG_TOWARD_ZERO
  return a / b; /* the wrong division, for the control of the test */
#else
  wint q = a / b;        /* Int.tdiv: toward zero */
  if (a % b < 0) q -= 1; /* Int.tmod: the sign of a */
  return q;
#endif
}

/* mix u v e: the value e per mille of the way from u to v. Lean: mix_fdiv. */
static inline wint mix(wint u, wint v, wint e) {
  const wint way = u - v;
  const wint left = 1000 - e;
  return v + fdiv(way * left, 1000);
}

/* Easing.stopsOf values num den: straight lines between `count` values at evenly spaced
 * stops, read at the share num / den. Lean: Easing.stopsOf_fdiv. No value reads as 0, one
 * value as itself, and a place past the values as the last value. */
static inline wint stops_of(const wint *values, wint count, wint num, wint den) {
  const wint pieces = count == 0 ? 0 : count - 1;
  const wint last = count == 0 ? 0 : values[count - 1];
  const wint whole = num * pieces;
  const wint i = fdiv(whole, den);
  const wint rest = whole - den * i;
  const wint a = i < count ? values[i] : last;
  const wint b = i + 1 < count ? values[i + 1] : last;
  return a + fdiv((b - a) * rest, den);
}

/* Easing.cubicOf y1 y2 num den: the cubic of the two heights, read at the share num / den.
 * Lean: Easing.cubicOf_fdiv. */
static inline wint cubic_of(wint y1, wint y2, wint num, wint den) {
  const wint left = den - num;
  const wint left2 = left * left;
  const wint num2 = num * num;
  const wint num3 = num2 * num;
  const wint den3 = den * den * den;
  return fdiv(3 * y1 * num * left2 + 3 * y2 * num2 * left + 1000 * num3, den3);
}

/* Easing.stopsAt and Easing.cubicAt: the same at the share p / 1000 (Easing.of_thousand). */
static inline wint stops_at(const wint *values, wint count, wint p) {
  return stops_of(values, count, p, 1000);
}

static inline wint cubic_at(wint y1, wint y2, wint p) { return cubic_of(y1, y2, p, 1000); }

/* An easing: stops (kind 0) or the two heights of a cubic (kind 1). */
typedef struct Easing {
  int kind;
  wint count;         /* stops: how many values */
  const wint *values; /* stops: the values */
  wint y1, y2;        /* cubic: the two heights */
} Easing;

/* Easing.of e num den. */
static inline wint easing_of(const Easing *e, wint num, wint den) {
  return e->kind == 0 ? stops_of(e->values, e->count, num, den)
                      : cubic_of(e->y1, e->y2, num, den);
}

/* Easing.at e p. */
static inline wint easing_at(const Easing *e, wint p) { return easing_of(e, p, 1000); }

/* A transition: a delay, a duration and an easing. */
typedef struct Transition {
  wint delay, duration;
  Easing ease;
} Transition;

/* Transition.at tr t: the easing's end once the duration is over, its start until the delay
 * is over, and between them the easing at the share of the duration that has passed. The
 * share is never rounded to a per mille first. */
static inline wint transition_at(const Transition *tr, wint t) {
  if (tr->delay + tr->duration <= t) return easing_at(&tr->ease, 1000);
  if (t <= tr->delay) return easing_at(&tr->ease, 0);
  return easing_of(&tr->ease, t - tr->delay, tr->duration);
}

/* Change.at c e: the numbers of the pose of a change at the eased progress e, written to
 * `out`; answers how many. The change is the numbers of `Change.numbers`:
 *   0 ax ay bx by   a shift: two numbers
 *   1 a b           a size: one number      2 a b  a part      3 a b  an opacity
 *   4 m c[8m] n d[8n]   a change of shape from m segments to n: 8m numbers where m = n, each
 *                       coordinate mixed; with two lengths, the first list while e < 500 and
 *                       the second from then on.
 * `out` holds 8 * max(m, n) numbers, or 2. */
static inline wint change_at(const wint *c, wint e, wint *out) {
  if (c[0] == 0) {
    out[0] = mix(c[1], c[3], e);
    out[1] = mix(c[2], c[4], e);
    return 2;
  }
  if (c[0] != 4) {
    out[0] = mix(c[1], c[2], e);
    return 1;
  }
  const wint m = c[1];
  const wint *a = c + 2;
  const wint n = a[8 * m];
  const wint *b = a + 8 * m + 1;
  if (m == n) {
    for (wint k = 0; k < 8 * m; k++) out[k] = mix(a[k], b[k], e);
    return 8 * m;
  }
  const wint *shown = e < 500 ? a : b;
  const wint count = 8 * (e < 500 ? m : n);
  for (wint k = 0; k < count; k++) out[k] = shown[k];
  return count;
}

/* How many numbers a change takes in `Change.numbers`. */
static inline wint change_length(const wint *c) {
  if (c[0] == 0) return 5;
  if (c[0] != 4) return 3;
  return 2 + 8 * c[1] + 1 + 8 * c[2 + 8 * c[1]];
}

#endif
