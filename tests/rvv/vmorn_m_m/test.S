#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmorn, e8)
VALU_MM(vmorn, e16)
VALU_MM(vmorn, e32)
VALU_MM(vmorn, e64)

	li	a0, 0
	jr	ra
