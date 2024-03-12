#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vmsle, e8)
VALU_VI(vmsle, e16)
VALU_VI(vmsle, e32)
VALU_VI(vmsle, e64)

	li	a0, 0
	jr	ra
