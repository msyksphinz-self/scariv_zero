#include <stdio.h>

uint64_t get_mcycle() {
  uint64_t mcycle = 0;
  asm volatile ("csrr %0, mcycle"   : "=r" (mcycle)  );
  return mcycle;
}


void* memcpy2 (void*, const void*, size_t);

#define DATA_SIZE_BYTE (64 * 1024)

const int init_data[DATA_SIZE_BYTE/sizeof(int)] = {0xdeadbeef};
int store_data[DATA_SIZE_BYTE/sizeof(int)];

int main ()
{

  size_t start = get_mcycle();
  memcpy2 ((void*)store_data, (const void*)init_data, DATA_SIZE_BYTE);
  size_t end = get_mcycle();

  printf("start = %ld, end = %ld, cycle = %ld\n", start, end, end - start);

  // __asm__ __volatile__ ("fence");
  // // __asm__ __volatile__ ("sfence.vma");
  // memcpy2 ((void*)store_data, (const void*)init_data, sizeof(init_data[0])*128*8);

  return 0;
}
