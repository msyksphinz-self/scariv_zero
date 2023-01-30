#define PLIC_BASE_ADDR         0xc000000
#define PLIC_SOURCE_BASE_ADDR  (PLIC_BASE_ADDR)
#define PLIC_PENDING_BASE_ADDR (PLIC_BASE_ADDR + 0x1000)
#define PLIC_ENABLE_BASE_ADDR  (PLIC_BASE_ADDR + 0x2000)
#define PLIC_THRESHOLD_ADDR    (PLIC_BASE_ADDR + 0x200000)

int plic_reg_rw_test()
{
  *((volatile unsigned int *)(PLIC_SOURCE_BASE_ADDR)) = 0xdeadbeef;
  *(volatile unsigned int *)(PLIC_SOURCE_BASE_ADDR);

  *((volatile unsigned int *)(PLIC_PENDING_BASE_ADDR)) = 0xdeadbeef;
  *(volatile unsigned int *)(PLIC_PENDING_BASE_ADDR);

  return 0;
}


int main ()
{
  plic_reg_rw_test();

  return 0;
}
