    .section    .text
_start:
    la      x1, data

    li      x10, 0x00112233
    sh  	x10,  0(x1)
    li      x10, 0x44556677
    sh  	x10,  2(x1)
    li      x10, 0x8899aabb
    sh  	x10,  4(x1)
    li      x10, 0xccddeeff
    sh  	x10,  6(x1)
    li      x10, 0x01234567
    sh  	x10,  8(x1)
    li      x10, 0x89abcdef
    sh  	x10, 10(x1)
    li      x10, 0x01010101
    sh  	x10, 12(x1)
    li      x10, 0x23232323
    sh  	x10, 14(x1)
    li      x10, 0x45454545
    sh  	x10, 16(x1)
    li      x10, 0x66667777
    sh  	x10, 18(x1)
    li      x10, 0x89898989
    sh  	x10, 20(x1)
    li      x10, 0xabababab
    sh  	x10, 22(x1)
    li      x10, 0xcdcdcdcd
    sh  	x10, 24(x1)
    li      x10, 0xefefefef
    sh  	x10, 26(x1)
    li      x10, 0x02020202
    sh  	x10, 28(x1)
    li      x10, 0x46464646
    sh  	x10, 30(x1)

    ld  	x16,  0(x1)
    ld  	x17,  8(x1)
    ld  	x18, 16(x1)
    ld  	x19, 24(x1)

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
