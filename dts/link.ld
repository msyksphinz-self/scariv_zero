SECTIONS
{

  /* text: test code section */
  . = 0x1000;
  .text : { *(.text) }
}
