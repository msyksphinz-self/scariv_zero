    .section    .text
_start:
    la  x1, data
    lbu x2,   0(x1)
    lbu x3,   1(x1)
    lbu x4,   2(x1)
    lbu x5,   3(x1)
    lbu x6,   4(x1)
    lbu x7,   5(x1)
    lbu x8,   6(x1)
    lbu x9,   7(x1)
    lbu x10,  8(x1)
    lbu x11,  9(x1)
    lbu x12, 10(x1)
    lbu x13, 11(x1)
    lbu x14, 12(x1)
    lbu x15, 13(x1)
    lbu x16, 14(x1)
    lbu x17, 15(x1)
    lbu x18, 16(x1)
    lbu x19, 17(x1)

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
