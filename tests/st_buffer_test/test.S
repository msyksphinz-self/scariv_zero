    .section    .text
_start:
    la      x1, data
    li      x10, 0x33
    li      x11, 0x77
    li      x12, 0xbb
    li      x13, 0xff
    li      x14, 0x67
    li      x15, 0xef
    li      x16, 0x01
    li      x17, 0x23
    li      x18, 0x45
    li      x19, 0x77
    li      x20, 0x89
    li      x21, 0xab
    li      x22, 0xcd
    li      x23, 0xef
    li      x24, 0x02
    li      x25, 0x46
    sb  	x10,  0(x1)
    sb  	x11,  1(x1)
    sb  	x12,  2(x1)
    sb  	x13,  3(x1)
    sb  	x14,  4(x1)
    sb  	x15,  5(x1)
    sb  	x16,  6(x1)
    sb  	x17,  7(x1)
    sb  	x18,  8(x1)
    sb  	x19,  9(x1)
    sb  	x20, 10(x1)
    sb  	x21, 11(x1)
    sb  	x22, 12(x1)
    sb  	x23, 13(x1)
    sb  	x24, 14(x1)
    sb  	x25, 15(x1)

    ld  	x16,  0(x1)
    ld  	x17,  8(x1)

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
