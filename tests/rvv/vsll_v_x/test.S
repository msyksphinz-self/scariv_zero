#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vsll, e8)
VALU_VX(vsll, e16)
VALU_VX(vsll, e32)
VALU_VX(vsll, e64)

	li	a0, 0
	jr	ra
