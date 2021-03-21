    .section    .text
_start:
    li      x10, 10
    li      x11, 1

loop:
    beq     x10, x11, finish
    addi    x11, x11, 1
    j       loop
finish:

#include "common_pkg.S"

    TEST_FINISH

    .section    .data
    .align      6
data:
    .dword  0x0
    .dword  0x0
    .dword  0x0
