.global fadd_d_bandwidth

fadd_d_bandwidth:
    li      x10, 10
    li      x11, 1
    fcvt.d.l f0, x10
    fcvt.d.l f1, x11

    li      x10, 100
    li      x11, 0

_loop:
    fdiv.d  f10, f0, f1
    fdiv.d  f11, f0, f1
    fdiv.d  f12, f0, f1
    fdiv.d  f13, f0, f1
    fdiv.d  f14, f0, f1
    fdiv.d  f15, f0, f1
    fdiv.d  f16, f0, f1
    fdiv.d  f17, f0, f1
    fdiv.d  f18, f0, f1
    fdiv.d  f19, f0, f1

    addi    x11, x11, 1
    bne     x10, x11, _loop

	ret
