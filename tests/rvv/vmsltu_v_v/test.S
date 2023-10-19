#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vmsltu, e8)
VALU_VV(vmsltu, e16)
VALU_VV(vmsltu, e32)
VALU_VV(vmsltu, e64)

	li	a0, 0
	jr	ra
