    .section    .text
_start:
    li      sp, 0x80001000
    li      x10, 10
    jal     func

    j       fin

func:

    beq     x10, zero, _func_fin

    addi    sp, sp, -0x20
    sd      x10, 0(sp)
    sd      ra , 8(sp)

    addi    x10, x10, -1
    jal     func

    ld      ra , 8(sp)
    ld      x13, 0(sp)
    addi    sp, sp, 0x20

    add     x10, x10, x13

    ret

_func_fin:
    ret


fin:
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
