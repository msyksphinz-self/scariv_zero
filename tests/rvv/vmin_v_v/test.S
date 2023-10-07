	.text
	.align	1
	.globl	main
	.type	main, @function
main:
	li		a5, 0
	li		a1, 100
	li		a2, 99
.L2:
	subw	a4, a1, a5
	vsetvli	a4, a4, e64, m1, ta, mu
	vmv.v.x	v24, a5
	vmv.v.x	v25, a1
    vmin.vv v30, v24, v25
	addw	a5, a4, a5
	ble	    a5, a2, .L2

	li		a5, 0
	li		a1, 100
	add		a3, a4, sp
	li		a2, 99
.L3:
	subw	a4, a1, a5
	vsetvli	a4, a4, e32, m1, ta, mu
	vmv.v.x	v24, a5
	vmv.v.x	v25, a1
    vmin.vv v30, v24, v25
	addw	a5, a4, a5
	ble	    a5, a2, .L3

	li		a5, 0
	li		a1, 100
	sub		a3, a4, a3
	li		a2, 99
.L4:
	subw	a4, a1, a5
	vsetvli	a4, a4, e16, m1, ta, mu
	vmv.v.x	v24, a5
	vmv.v.x	v25, a1
    vmin.vv v30, v24, v25
	addw	a5, a4, a5
	ble	    a5, a2, .L4

	li	a5, 0
	li	a1, 100
	sub	a3, a4, a3
	li	a2, 99
.L5:
	subw	a4, a1, a5
	vsetvli	a4, a4, e8, m1, ta, mu
	vmv.v.x	v24, a5
	vmv.v.x	v25, a1
    vmin.vv v30, v24, v25
	addw	a5, a4, a5
	ble	    a5, a2, .L5

	li	a0, 0
	jr	ra
