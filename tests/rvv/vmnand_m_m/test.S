#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmnand, e8)
VALU_MM(vmnand, e16)
VALU_MM(vmnand, e32)
VALU_MM(vmnand, e64)

	li	a0, 0
	jr	ra
