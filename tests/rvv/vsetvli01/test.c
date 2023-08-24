#include <riscv_vector.h>
#include <stddef.h>

int main ()
{
  const int n = 100;

  size_t vl;
  for (int i = 0; i < n; i += vl) {
    vl = __riscv_vsetvl_e32m1(n - i);
  }

  return 0;
}
