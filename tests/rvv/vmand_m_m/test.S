#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmand, e8)
VALU_MM(vmand, e16)
VALU_MM(vmand, e32)
VALU_MM(vmand, e64)

	li	a0, 0
	jr	ra
