#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vsra, e8)
VALU_VI(vsra, e16)
VALU_VI(vsra, e32)
VALU_VI(vsra, e64)

	li	a0, 0
	jr	ra
