    .section    .text
_start:
    li      x2, 32*64       // 32-byte * 64-words

    la      x1, data
    li      x10, 0x33
    sd  	x10,  0(x1)

    add     x1, x1, x2
    li      x11, 0x77
    sd  	x11,  0(x1)

    add     x1, x1, x2
    li      x12, 0xbb
    sd  	x12,  0(x1)

    add     x1, x1, x2
    li      x13, 0xff
    sd  	x13,  0(x1)

    add     x1, x1, x2
    li      x14, 0x67
    sd  	x14,  0(x1)

    add     x1, x1, x2
    li      x15, 0xef
    sd  	x15,  0(x1)

    add     x1, x1, x2
    li      x16, 0x01
    sd  	x16,  0(x1)

    add     x1, x1, x2
    li      x17, 0x23
    sd  	x17,  0(x1)

    add     x1, x1, x2
    li      x18, 0x45
    sd  	x18,  0(x1)

    add     x1, x1, x2
    li      x19, 0x77
    sd  	x19,  0(x1)

    add     x1, x1, x2
    li      x20, 0x89
    sd  	x20,  0(x1)

    add     x1, x1, x2
    li      x21, 0xab
    sd  	x21,  0(x1)

    add     x1, x1, x2
    li      x22, 0xcd
    sd  	x22,  0(x1)

    add     x1, x1, x2
    li      x23, 0xef
    sd  	x23,  0(x1)

    add     x1, x1, x2
    li      x24, 0x02
    sd  	x24,  0(x1)

    add     x1, x1, x2
    li      x25, 0x46
    sd  	x25,  0(x1)

    la      x1, data

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

    ld  	x20,  0(x1)
    add     x1, x1, x2

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
