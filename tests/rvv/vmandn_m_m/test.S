#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmandn, e8)
VALU_MM(vmandn, e16)
VALU_MM(vmandn, e32)
VALU_MM(vmandn, e64)

	li	a0, 0
	jr	ra
