#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "memlib.h"
#include "mm.h"

typedef struct {
  void *p;
  size_t s;
} array;

inline size_t min(const size_t a, const size_t b) {
  return a < b? a : b;
}

array test_malloc(const size_t s) {
  printf("mm_malloc(%u)\n", s);
  const array a = {mm_malloc(s), s};
  assert(a.p != NULL);

  size_t i;
  for (i = 0; i < a.s; i++)
    ((char *)a.p)[i] = rand();

  return a;
}

array test_realloc(const array a, const size_t s) {
  char tmp[a.s];
  memcpy(tmp, a.p, a.s);

  printf("mm_realloc(%p, %u)\n", a.p, s);
  const array b = {mm_realloc(a.p, s), s};
  assert(b.p != NULL);
  assert(!memcmp(b.p, tmp, min(a.s, b.s)));

  if (b.s > a.s) {
    size_t i;
    for (i = a.s; i < b.s; i++)
      ((char *)b.p)[i] = rand();

  }

  return b;
}

void test_free(const array a) {
  printf("mm_free(%p)\n", a.p);
  mm_free(a.p);
}

int main() {
  mem_init();
  mm_init();
  array a = test_malloc(8);
  a = test_realloc(a, 1024);
  a = test_realloc(a, 8);
  a = test_realloc(a, 256);
  a = test_realloc(a, 2048);
  array b = test_malloc(256);
  test_free(a);
  b = test_realloc(b, 512);
  b = test_realloc(b, 640);
  b = test_realloc(b, 4096);
  test_free(b);
  mem_deinit();
  return 0;
}
