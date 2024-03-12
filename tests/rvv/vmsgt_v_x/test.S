#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vmsgt, e8)
VALU_VX(vmsgt, e16)
VALU_VX(vmsgt, e32)
VALU_VX(vmsgt, e64)

	li	a0, 0
	jr	ra
