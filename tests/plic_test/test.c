#include <stdint.h>

#define PLIC_BASE_ADDR         0xc000000
#define PLIC_SOURCE_BASE_ADDR  (PLIC_BASE_ADDR)
#define PLIC_PENDING_BASE_ADDR (PLIC_BASE_ADDR + 0x1000)
#define PLIC_ENABLE_BASE_ADDR  (PLIC_BASE_ADDR + 0x2000)
#define PLIC_THRESHOLD_ADDR    (PLIC_BASE_ADDR + 0x200000)

#define NUM_OF_SOURCE 8

int plic_reg_rw_test()
{
  // Priority Register Test
  for (int i = 0; i <= 4 * NUM_OF_SOURCE; i+= sizeof(uint8_t)) {
    *((volatile uint8_t *)(PLIC_SOURCE_BASE_ADDR + i)) = 0xdeadbeef;
    *((volatile uint8_t *)(PLIC_SOURCE_BASE_ADDR + i));
  }
  for (int i = 0; i <= 4 * NUM_OF_SOURCE; i+= sizeof(uint16_t)) {
    *((volatile uint16_t *)(PLIC_SOURCE_BASE_ADDR + i)) = 0xdeadbeef;
    *((volatile uint16_t *)(PLIC_SOURCE_BASE_ADDR + i));
  }
  for (int i = 0; i <= 4 * NUM_OF_SOURCE; i+= sizeof(uint32_t)) {
    *((volatile uint32_t *)(PLIC_SOURCE_BASE_ADDR + i)) = 0xdeadbeef;
    *((volatile uint32_t *)(PLIC_SOURCE_BASE_ADDR + i));
  }
  for (int i = 0; i <= 4 * NUM_OF_SOURCE; i+= sizeof(uint64_t)) {
    *((volatile uint64_t *)(PLIC_SOURCE_BASE_ADDR + i)) = 0xdeadbeef;
    *((volatile uint64_t *)(PLIC_SOURCE_BASE_ADDR + i));
  }

  // *((volatile unsigned int *)(PLIC_PENDING_BASE_ADDR)) = 0xdeadbeef;
  // *(volatile unsigned int *)(PLIC_PENDING_BASE_ADDR);

  return 0;
}


int main ()
{
  plic_reg_rw_test();

  return 0;
}
