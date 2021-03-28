    .section    .text
_start:
    la      x1, data

    li      x10, 0x00112233
    sw  	x10,  0(x1)
    li      x10, 0x44556677
    sw  	x10,  4(x1)
    li      x10, 0x8899aabb
    sw  	x10,  8(x1)
    li      x10, 0xccddeeff
    sw  	x10, 12(x1)
    li      x10, 0x01234567
    sw  	x10, 16(x1)
    li      x10, 0x89abcdef
    sw  	x10, 20(x1)
    li      x10, 0x01010101
    sw  	x10, 24(x1)
    li      x10, 0x23232323
    sw  	x10, 28(x1)
    li      x10, 0x45454545
    sw  	x10, 32(x1)
    li      x10, 0x66667777
    sw  	x10, 36(x1)
    li      x10, 0x89898989
    sw  	x10, 40(x1)
    li      x10, 0xabababab
    sw  	x10, 44(x1)
    li      x10, 0xcdcdcdcd
    sw  	x10, 48(x1)
    li      x10, 0xefefefef
    sw  	x10, 52(x1)
    li      x10, 0x02020202
    sw  	x10, 56(x1)
    li      x10, 0x46464646
    sw  	x10, 60(x1)

    ld  	x16,  0(x1)
    ld  	x17,  8(x1)
    ld  	x18, 16(x1)
    ld  	x19, 24(x1)
    ld  	x16, 32(x1)
    ld  	x17, 40(x1)
    ld  	x18, 48(x1)
    ld  	x19, 56(x1)

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
