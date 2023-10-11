#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vsrl, e8)
VALU_VV(vsrl, e16)
VALU_VV(vsrl, e32)
VALU_VV(vsrl, e64)

	li	a0, 0
	jr	ra
