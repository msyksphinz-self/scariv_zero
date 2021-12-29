    .section    .text
_start:
    li      sp, 0x80001000
    li      x10, 10
    jal     func1

    j       fin

func1:

    beq     x10, zero, _func_fin1

    addi    sp, sp, -0x20
    sd      x10, 0(sp)
    sd      ra , 8(sp)

    addi    x10, x10, -1
    jal     func2

    ld      ra , 8(sp)
    ld      x13, 0(sp)
    addi    sp, sp, 0x20

    add     x10, x10, x13

    ret

_func_fin1:
    ret


func2:

    beq     x10, zero, _func_fin2

    addi    sp, sp, -0x20
    sd      x10, 0(sp)
    sd      ra , 8(sp)

    addi    x10, x10, -1
    jal     func1

    ld      ra , 8(sp)
    ld      x13, 0(sp)
    addi    sp, sp, 0x20

    add     x10, x10, x13

    ret

_func_fin2:
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
