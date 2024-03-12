long long get_cycle()
{
  long long cycle;
  asm volatile ("rdcycle %0; add x0,x0,x0":"=r"(cycle));

  return cycle;
}

long long get_instret()
{
  long long cycle;
  asm volatile ("rdinstret %0; add x0,x0,x0":"=r"(cycle));

  return cycle;
}

long long get_vecinst()
{
  long long num;
  asm volatile ("csrr %0, mhpmcounter10":"=r"(num));

  return num;
}


long long start_konatadump()
{
  long long cycle;
  asm volatile ("rdcycle %0; add x0,x0,x1":"=r"(cycle));

  return cycle;
}


long long stop_konatadump()
{
  long long cycle;
  asm volatile ("rdcycle %0; add x0,x0,x2":"=r"(cycle));

  return cycle;
}
