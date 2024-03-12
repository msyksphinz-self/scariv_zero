#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vsra, e8)
VALU_VV(vsra, e16)
VALU_VV(vsra, e32)
VALU_VV(vsra, e64)

	li	a0, 0
	jr	ra
