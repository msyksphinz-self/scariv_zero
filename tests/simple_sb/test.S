    .section    .text
_start:
    la      x1, data
    li      x10, 0x00112233
    sb  	x10,  0(x1)
    li      x10, 0x44556677
    sb  	x10,  1(x1)
    li      x10, 0x8899aabb
    sb  	x10,  2(x1)
    li      x10, 0xccddeeff
    sb  	x10,  3(x1)
    li      x10, 0x01234567
    sb  	x10,  4(x1)
    li      x10, 0x89abcdef
    sb  	x10,  5(x1)
    li      x10, 0x01010101
    sb  	x10,  6(x1)
    li      x10, 0x23232323
    sb  	x10,  7(x1)
    li      x10, 0x45454545
    sb  	x10,  8(x1)
    li      x10, 0x66667777
    sb  	x10,  9(x1)
    li      x10, 0x89898989
    sb  	x10, 10(x1)
    li      x10, 0xabababab
    sb  	x10, 11(x1)
    li      x10, 0xcdcdcdcd
    sb  	x10, 12(x1)
    li      x10, 0xefefefef
    sb  	x10, 13(x1)
    li      x10, 0x02020202
    sb  	x10, 14(x1)
    li      x10, 0x46464646
    sb  	x10, 15(x1)

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
