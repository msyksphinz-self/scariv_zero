#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vmsgt, e8)
VALU_VI(vmsgt, e16)
VALU_VI(vmsgt, e32)
VALU_VI(vmsgt, e64)

	li	a0, 0
	jr	ra
