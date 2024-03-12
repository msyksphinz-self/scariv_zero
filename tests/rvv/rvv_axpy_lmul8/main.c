#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <assert.h>
#include "utils.h"

/*************************************************************************
*GET_TIME
*returns a long int representing the time
*************************************************************************/

#include <time.h>
#include <sys/time.h>

#include "count_utils.h"

long long get_time() {
  return get_cycle();
}

// Returns the number of seconds elapsed between the two specified times
float elapsed_time(long long start_time, long long end_time) {
  return (float) (end_time - start_time) / (1000 * 1000);
}
/*************************************************************************/

void axpy_intrinsics(double a, double *dx, double *dy, int n);

// Ref version
void axpy_ref(double a, double *dx, double *dy, int n) {
  int i;
  for (i=0; i<n; i++) {
    dy[i] += a*dx[i];
  }
}

#define ARRAY_SIZE (8*1024)

void init_vector(double *pv, long n, double value)
{
  for (int i=0; i<n; i++) pv[i]= value;
}

/* Allocate the source and result vectors */
double dx    [ARRAY_SIZE];
double dy    [ARRAY_SIZE];
double dy_ref[ARRAY_SIZE];

int main(int argc, char *argv[])
{
  long long start,end;
  start = get_time();

  double a=1.0;
  long n;

  if (argc == 2)
    n = 1024*atol(argv[1]); // input argument: vector size in Ks
  else
    n = ARRAY_SIZE;


  init_vector(dx, n, 1.0);
  init_vector(dy, n, 2.0);

  end = get_time();
  printf("init_vector time: %f\n", elapsed_time(start, end));

  printf ("doing reference axpy\n");
  start = get_time();
  axpy_ref(a, dx, dy, n);
  end = get_time();
  printf("axpy_reference time: %f\n", elapsed_time(start, end));

  capture_ref_result(dy, dy_ref, n);
  init_vector(dx, n, 1.0);
  init_vector(dy, n, 2.0);

  printf ("doing vector axpy\n");
  start = get_time();
  long long start_cycle = get_cycle();
  // long long start_vecinst = get_vecinst();

  axpy_intrinsics(a, dx, dy, n);

  long long end_cycle = get_cycle();
  // long long end_vecinst = get_vecinst();
  end = get_time();
  printf("cycles = %lld\n", end_cycle - start_cycle);
  // printf("vecinst = %lld\n", end_vecinst - start_vecinst);

  printf ("done\n");
  test_result(dy, dy_ref, n);

  return 0;
}
