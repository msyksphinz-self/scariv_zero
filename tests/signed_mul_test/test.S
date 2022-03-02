    .section    .text
_start:
    li      x10, -3
    li      x11, -5

    mul     x20, x10, x11
    mulh    x21, x10, x11

    nop
    nop
    nop

#include "common_pkg.S"

    TEST_FINISH

    .section    .data
    .align      6
data:
    .dword  0x0
    .dword  0x0
    .dword  0x0
