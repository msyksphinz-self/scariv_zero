#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vsrl, e8)
VALU_VI(vsrl, e16)
VALU_VI(vsrl, e32)
VALU_VI(vsrl, e64)

	li	a0, 0
	jr	ra
