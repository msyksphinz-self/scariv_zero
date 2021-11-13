    .section    .text
_start:
    la      x1, data
    addi    x2, x1, 256/8
    li      x20, 500
loop:
    ld      x10,  0(x1)
    ld  	x11,  0(x2)
    addi    x20, x20, -1
    bne     x20, zero, loop

#include "common_pkg.S"

    TEST_FINISH

    .section    .data
    .align      6
data:
    .dword  0x0123456789abcdef
    .dword  0x0011223344556677
    .dword  0x8899aabbccddeeff
    .dword  0x0000000100000001
    .dword  0x0000000200000002
    .dword  0x0000000300000003
    .dword  0x0000000400000004
    .dword  0x0000000500000005
    .dword  0x0000000600000006
    .dword  0x0000000700000007
    .dword  0x0000000800000008
    .dword  0x0000000900000009
    .dword  0x0000001000000010
    .dword  0x0000001100000011
    .dword  0x0000001200000012
    .dword  0x0000001300000013
    .dword  0x0000001400000014
    .dword  0x0000001500000015
    .dword  0x0000001600000016
    .dword  0x0000001700000017
    .dword  0x0000001800000018
    .dword  0x0000001900000019
