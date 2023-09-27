#include <riscv_vector.h>
#include <stddef.h>

int main ()
{
  const int n = 100;

  size_t vl;
  for (int i = 0; i < n; i += vl) {
    vl = __riscv_vsetvl_e64m1(n - i);
    register volatile vint64m1_t vx = __riscv_vmv_v_x_i64m1 (i, vl);
  }

  for (int i = 0; i < n; i += vl) {
    vl = __riscv_vsetvl_e32m1(n - i);
    register volatile vint32m1_t vx = __riscv_vmv_v_x_i32m1 (i, vl);
  }

  for (int i = 0; i < n; i += vl) {
    vl = __riscv_vsetvl_e16m1(n - i);
    register volatile vint16m1_t vx = __riscv_vmv_v_x_i16m1 (i, vl);
  }

  for (int i = 0; i < n; i += vl) {
    vl = __riscv_vsetvl_e8m1(n - i);
    register volatile vint8m1_t vx = __riscv_vmv_v_x_i8m1 (i, vl);
  }

  return 0;
}
