#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vmsle, e8)
VALU_VX(vmsle, e16)
VALU_VX(vmsle, e32)
VALU_VX(vmsle, e64)

	li	a0, 0
	jr	ra
