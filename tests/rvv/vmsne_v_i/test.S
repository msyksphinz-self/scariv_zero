#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vmsne, e8)
VALU_VI(vmsne, e16)
VALU_VI(vmsne, e32)
VALU_VI(vmsne, e64)

	li	a0, 0
	jr	ra
