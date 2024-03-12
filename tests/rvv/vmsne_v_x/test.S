#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vmsne, e8)
VALU_VX(vmsne, e16)
VALU_VX(vmsne, e32)
VALU_VX(vmsne, e64)

	li	a0, 0
	jr	ra
