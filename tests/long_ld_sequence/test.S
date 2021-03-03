    .section    .text
_start:
    la  x1, data
    ld  x10,  0(x1)
    ld  x11,  8(x1)
    ld  x12, 16(x1)
    ld  x13, 24(x1)
    ld  x14, 32(x1)
    ld  x15, 40(x1)
    ld  x16, 48(x1)
    ld  x18, 64(x1)
    ld  x19, 72(x1)
    ld  x10, 80(x1)
    ld  x11, 88(x1)
    ld  x12, 96(x1)
    ld  x13,104(x1)
    ld  x14,112(x1)
    ld  x15,120(x1)
    ld  x16,128(x1)
    ld  x18,136(x1)
    ld  x19,144(x1)

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
