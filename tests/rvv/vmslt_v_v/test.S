#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vmslt, e8)
VALU_VV(vmslt, e16)
VALU_VV(vmslt, e32)
VALU_VV(vmslt, e64)

	li	a0, 0
	jr	ra
