/* easing_test.c: holds easing.h's numbers equal to the kit's.
 *
 *   easing_test motion-readings.tsv
 *
 * The table is `Case.text Case.battery` of Whatwg/Svg/Scene/Vector.lean. Every line is
 *
 *   kind  name  g  x1 ... xg  r  y1 ... yr
 *
 * two words, a count and that many numbers given, a count and that many readings. For each
 * line this program computes the readings from the numbers given, with easing.h, and
 * compares. It prints one line for each case that differs, then the counts, and answers 0
 * where every reading is the kit's.
 *
 * C99. Reads with fscanf alone.
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "easing.h"

/* A count and that many numbers. NULL where the file does not have them. */
static wint *numbers(FILE *f, long *count) {
  int64_t n = 0;
  if (fscanf(f, "%" SCNd64, &n) != 1 || n < 0) return NULL;
  wint *x = malloc(((size_t)n + 1) * sizeof *x);
  if (!x) return NULL;
  for (int64_t i = 0; i < n; i++) {
    int64_t v = 0;
    if (fscanf(f, "%" SCNd64, &v) != 1) { free(x); return NULL; }
    x[i] = (wint)v;
  }
  *count = (long)n;
  return x;
}

/* An easing from the numbers of `Easing.numbers`: `0 k v1 ... vk` or `1 y1 y2`. Answers how
 * many numbers it took. */
static long easing_from(const wint *x, Easing *e) {
  memset(e, 0, sizeof *e);
  if (x[0] == 0) {
    e->kind = 0;
    e->count = x[1];
    e->values = x + 2;
    return 2 + (long)x[1];
  }
  e->kind = 1;
  e->y1 = x[1];
  e->y2 = x[2];
  return 3;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: easing_test motion-readings.tsv\n"); return 2; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror(argv[1]); return 2; }
  char kind[32], name[128];
  long cases = 0, readings = 0, wrong = 0, wrongCases = 0, unknown = 0;
  while (fscanf(f, "%31s %127s", kind, name) == 2) {
    long g = 0, r = 0;
    wint *in = numbers(f, &g);
    wint *out = in ? numbers(f, &r) : NULL;
    if (!in || !out) { fprintf(stderr, "%s %s: the line does not read\n", kind, name); return 2; }
    long bad = 0;
    if (!strcmp(kind, "format")) {
      if (strcmp(name, "whatwg-motion-1")) { fprintf(stderr, "format %s: not known\n", name); return 2; }
      free(in); free(out);
      continue;
    } else if (!strcmp(kind, "mix")) {
      /* given: u v lo last; readings: mix u v e for e = lo ... lo + last */
      if (g != 4 || r != (long)in[3] + 1) bad = r + 1;
      else for (long i = 0; i < r; i++) bad += mix(in[0], in[1], in[2] + (wint)i) != out[i];
    } else if (!strcmp(kind, "at")) {
      /* given: an easing; readings: Easing.at at the moments 0 ... 1000 */
      Easing e;
      easing_from(in, &e);
      for (long p = 0; p < r; p++) bad += easing_at(&e, (wint)p) != out[p];
    } else if (!strcmp(kind, "of")) {
      /* given: den, an easing; readings: Easing.of n den for n = 0 ... den */
      Easing e;
      easing_from(in + 1, &e);
      if (r != (long)in[0] + 1) bad = r + 1;
      else for (long n = 0; n < r; n++) bad += easing_of(&e, (wint)n, in[0]) != out[n];
    } else if (!strcmp(kind, "timed")) {
      /* given: delay duration, an easing; readings: Transition.at at the moments 0 ... 1000 */
      Transition tr;
      tr.delay = in[0];
      tr.duration = in[1];
      easing_from(in + 2, &tr.ease);
      for (long t = 0; t < r; t++) bad += transition_at(&tr, (wint)t) != out[t];
    } else if (!strcmp(kind, "track")) {
      /* given: a change, delay duration, an easing; readings: for each moment 0 ... 1000 a
       * count and that many numbers of the pose */
      const long c = (long)change_length(in);
      Transition tr;
      tr.delay = in[c];
      tr.duration = in[c + 1];
      easing_from(in + c + 2, &tr.ease);
      wint *pose = malloc(((size_t)g + 2) * sizeof *pose);
      if (!pose) return 2;
      long at = 0;
      for (long t = 0; t <= 1000; t++) {
        if (at >= r) { bad += 1; break; }
        const long want = (long)out[at];
        const long got = (long)change_at(in, transition_at(&tr, (wint)t), pose);
        if (got != want) bad += 1;
        else for (long k = 0; k < want; k++) bad += pose[k] != out[at + 1 + k];
        at += 1 + want;
      }
      if (at != r) bad += 1;
      free(pose);
    } else {
      unknown++;
      fprintf(stderr, "%s %s: a kind this test does not know\n", kind, name);
    }
    if (bad) { wrongCases++; printf("DIFFERS %s %s: %ld of %ld readings\n", kind, name, bad, r); }
    cases++;
    readings += r;
    wrong += bad;
    free(in);
    free(out);
  }
  fclose(f);
  printf("%ld cases, %ld readings, %ld readings differ in %ld cases, %ld cases of no known kind\n",
         cases, readings, wrong, wrongCases, unknown);
  return wrong || unknown || !cases ? 1 : 0;
}
