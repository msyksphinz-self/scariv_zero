#include <gmpxx.h>
#include <iostream>
#include <iomanip>
#include <stdint.h>

int main ()
{
  std::string rs1_val;
  std::string rs2_val;

  std::cin >> rs1_val;
  std::cin >> rs2_val;

  mpz_class *rs1_mpz = new mpz_class(rs1_val, 16);
  mpz_class *rs2_mpz = new mpz_class(rs2_val, 16);

  static int unroll = 8;

  for (int j = 64; j >= 0; j-=unroll) {
    printf ("  ");
  }
  std::cout << std::setw(64/4) << std::setfill('0') << std::hex << *rs1_mpz << '\n';
  for (int j = 64; j >= 0; j-=unroll) {
    printf ("  ");
  }
  std::cout << std::setw(64/4) << std::setfill('0') << std::hex << *rs2_mpz << '\n';
  for (int j = 64*2; j >= 0; j-=unroll) {
    printf ("--");
  }
  std::cout << '\n';

  mpz_class prod_ans = 0;

  for (int i = 0; i < 64; i += unroll) {
    mpz_class mplier = *rs1_mpz >> i & ((1 << unroll)-1);
    mpz_class part_pro = mplier * *rs2_mpz;

    std::cout << std::setw((64-i)/4) << std::setfill(' ') << " ";
    std::cout << std::setw((64+unroll)/4) << std::setfill('0') << std::hex << part_pro.get_str(16) << '\n';
    prod_ans += part_pro << i;
    std::cout << std::setw((128+unroll)/4) << std::setfill('0') << std::hex << prod_ans.get_str(16) << '\n';
  }

  for (int j = 64*2; j >= 0; j-=unroll) {
    printf ("--");
  }
  printf("\n");

  std::cout << std::setw((128+unroll)/4) << std::setfill('0') << std::hex << prod_ans.get_str(16) << '\n';

  return 0;
}
