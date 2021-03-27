    .section    .text
_start:
    la  x1, data
    lhu x2,   0(x1)
    lhu x3,   2(x1)
    lhu x4,   4(x1)
    lhu x5,   6(x1)
    lhu x6,   8(x1)
    lhu x7,  10(x1)
    lhu x8,  12(x1)
    lhu x9,  14(x1)
    lhu x10, 18(x1)
    lhu x11, 20(x1)
    lhu x12, 22(x1)
    lhu x13, 24(x1)
    lhu x14, 28(x1)
    lhu x15, 30(x1)
    lhu x16, 32(x1)
    lhu x17, 34(x1)
    lhu x18, 36(x1)
    lhu x19, 38(x1)

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
