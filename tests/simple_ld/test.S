    .section    .text
_start:
    la  x1, data
    ld  x16,  0(x1)
    ld  x17,  8(x1)
    ld  x18, 16(x1)

#include "common_pkg.S"

    TEST_FINISH

    .section    .data
data:
    .dword  0x0123456789abcdef
    .dword  0x0011223344556677
    .dword  0x8899aabbccddeeff
