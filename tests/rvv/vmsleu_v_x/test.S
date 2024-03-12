#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vmsleu, e8)
VALU_VX(vmsleu, e16)
VALU_VX(vmsleu, e32)
VALU_VX(vmsleu, e64)

	li	a0, 0
	jr	ra
