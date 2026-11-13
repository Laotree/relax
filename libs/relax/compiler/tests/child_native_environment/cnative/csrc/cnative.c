#include <stdint.h>
#include <stdlib.h>
int32_t cn_add(int32_t a, int32_t b) { return a + b + DELTA; }
int32_t cn_home_is_unset(void) { return getenv("HOME") == NULL; }
