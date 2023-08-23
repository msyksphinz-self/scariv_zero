void putc(char c)
{
  (*(volatile unsigned char *)0x54000000) = c;
}

void puts (char *s)
{
  while (*s != '\0') {
    putc(*s);
    s++;
  }
}

int main ()
{
  puts ("Hello World\n");

  return 0;
}
