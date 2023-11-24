SECTIONS
{

  /* text: test code section */
  . = 0x2000;
  .text : { *(.text) }
}
