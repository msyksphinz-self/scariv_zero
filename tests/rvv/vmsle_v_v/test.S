#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vmsle, e8)
VALU_VV(vmsle, e16)
VALU_VV(vmsle, e32)
VALU_VV(vmsle, e64)

	li	a0, 0
	jr	ra
