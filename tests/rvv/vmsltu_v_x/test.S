#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vmsltu, e8)
VALU_VX(vmsltu, e16)
VALU_VX(vmsltu, e32)
VALU_VX(vmsltu, e64)

	li	a0, 0
	jr	ra
