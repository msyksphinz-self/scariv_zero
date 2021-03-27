    .section    .text
_start:
    la  x1, data
    lw  x2,   0(x1)
    lw  x3,   4(x1)
    lw  x4,   8(x1)
    lw  x5,  12(x1)
    lw  x6,  16(x1)
    lw  x7,  20(x1)
    lw  x8,  24(x1)
    lw  x9,  28(x1)
    lw  x10, 32(x1)
    lw  x11, 36(x1)
    lw  x12, 40(x1)
    lw  x13, 44(x1)
    lw  x14, 48(x1)
    lw  x15, 52(x1)
    lw  x16, 56(x1)
    lw  x17, 60(x1)
    lw  x18, 64(x1)
    lw  x19, 68(x1)

#include "common_pkg.S"

    TEST_FINISH

    .section    .data
    .align      6
data:
    .dword  0x0123456789abcdef
    .dword  0x0011223344556677
    .dword  0x8899aabbccddeeff
    .dword  0x0000111122223333
    .dword  0x4444555566667777
    .dword  0x88889999aaaabbbb
    .dword  0xccccddddeeeeffff
    .dword  0x0000000011111111
    .dword  0x2222222233333333
    .dword  0x4444444455555555
    .dword  0x6666666677777777
    .dword  0x8888888899999999
    .dword  0xaaaaaaaabbbbbbbb
    .dword  0xccccccccdddddddd
    .dword  0xeeeeeeeeffffffff
