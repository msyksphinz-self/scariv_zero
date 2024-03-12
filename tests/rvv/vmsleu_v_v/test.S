#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vmsleu, e8)
VALU_VV(vmsleu, e16)
VALU_VV(vmsleu, e32)
VALU_VV(vmsleu, e64)

	li	a0, 0
	jr	ra
