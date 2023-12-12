#include <stdint.h>

int64_t result_count = 0;

extern int branch_count(int aa, int bb);

int __attribute__((optimize("O1")))  main ()
{
  for (int a = 0; a < 100; a++) {
    result_count ++;
  }

  return 0;
}
