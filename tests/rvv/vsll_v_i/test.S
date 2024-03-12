#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vsll, e8)
VALU_VI(vsll, e16)
VALU_VI(vsll, e32)
VALU_VI(vsll, e64)

	li	a0, 0
	jr	ra
