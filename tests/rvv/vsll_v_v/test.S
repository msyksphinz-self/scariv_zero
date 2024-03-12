#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vsll, e8)
VALU_VV(vsll, e16)
VALU_VV(vsll, e32)
VALU_VV(vsll, e64)

	li	a0, 0
	jr	ra
