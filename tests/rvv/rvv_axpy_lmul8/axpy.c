#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <assert.h>

#ifdef USE_RISCV_VECTOR

#include "vector_defines_m8.h"

void axpy_intrinsics(double a, double *dx, double *dy, int n) {
  int i;

  long gvl = _MM_VSETVLI(e64, n); //PLCT

  // _MMR_f64 v_a = _MM_SET_f64(a, gvl);

  for (i = 0; i < n;) {
    gvl = _MM_VSETVLI(e64, n - i); //PLCT

    {
      _MMR_f64 v_dx = _MM_LOAD_f64(dx, gvl);
      _MMR_f64 v_dy = _MM_LOAD_f64(dy, gvl);
      _MMR_f64 v_res = _MM_MACC_f64_f(v_dy, a, v_dx, gvl);
      _MM_STORE_f64(dy, v_res, gvl);
    }

    dx += gvl;
    dy += gvl;
    i += gvl;
  }

FENCE();
}

#else // USE_RISCV_VECTOR

#define FENCE()   asm volatile( "fence" : : );

void axpy_intrinsics(double a, double *dx, double *dy, int n) {

  for (int i = 0; i < n; i++) {
    dy[i] = a * dx[i] + dy[i];
  }

  FENCE();
}

#endif // USE_RISCV_VECTOR
