int result_count = 0;

extern int branch_count(int aa, int bb);

int main ()
{
  for (int a = 0; a < 10; a++) {
    for (int b = 0; b < 10; b++) {
      if (branch_count (a, b)) {
        result_count ++;
      }
    }
  }

  return 0;
}
