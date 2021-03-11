    .section    .text
_start:
    la      x1, data
    addi	x10, x0, 0x567
    addi	x11, x0, 0x233
    addi	x12, x0, 0x0bb
    sd  	x10,  0(x1)
    sd  	x11,  8(x1)
    sd  	x12, 16(x1)
    ld  	x16,  0(x1)
    ld  	x17,  8(x1)
    ld  	x18, 16(x1)
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
