/*
 * We assume that the stack grows downward.
 * <overflow.c>=
 */
#include "all.h"

static volatile char *low_water_mark = NULL;

int checkoverflow(int limit) {
  volatile char c;
  if (low_water_mark == NULL) {
    low_water_mark = &c;
    return 0;
  } else if (low_water_mark - &c >= limit) {
    error("Recursion too deep");
    return -1; /* not reachable, but the compiler can't tell */
  } else {
    return (low_water_mark - &c);
  }
}
