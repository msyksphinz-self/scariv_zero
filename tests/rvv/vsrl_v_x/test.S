#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vsrl, e8)
VALU_VX(vsrl, e16)
VALU_VX(vsrl, e32)
VALU_VX(vsrl, e64)

	li	a0, 0
	jr	ra
