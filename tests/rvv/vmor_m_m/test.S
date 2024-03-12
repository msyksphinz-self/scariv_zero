#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmor, e8)
VALU_MM(vmor, e16)
VALU_MM(vmor, e32)
VALU_MM(vmor, e64)

	li	a0, 0
	jr	ra
