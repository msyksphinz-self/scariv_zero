    .section    .text
_start:
    la      x1, data
    li      x2, 3
    la      x3, data
    li      x4, 1
    li		x10, 0x00567
    li		x11, 0x00233
    li		x12, 0x000bb
    li		x13, 0x11567
    li		x14, 0x11233
    li		x15, 0x110bb
    li		x16, 0x22567
    li		x17, 0x22233

loop:

    div     x3, x3, x4

    sd  	x10,  0(x3)
    sd  	x11,  8(x3)
    sd  	x12, 16(x3)
    sd  	x13, 24(x3)
    sd  	x14, 32(x3)
    sd  	x15, 40(x3)
    sd  	x16, 48(x3)
    sd  	x17, 56(x3)

    ld  	x20,  0(x1)
    ld  	x21,  8(x1)
    ld  	x22, 16(x1)
    ld  	x23, 24(x1)
    ld  	x24, 32(x1)
    ld  	x25, 40(x1)
    ld  	x26, 48(x1)
    ld  	x27, 56(x1)

    addi	x10, x10, 0x67
    addi	x11, x11, 0x33
    addi	x12, x12, 0xbb
    addi	x13, x13, 0x67
    addi	x14, x14, 0x33
    addi	x15, x15, 0xbb
    addi	x16, x16, 0x67
    addi	x17, x17, 0x33

    addi    x2, x2, -1
    bne     x2, zero, loop

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
