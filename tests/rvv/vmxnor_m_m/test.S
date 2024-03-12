#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmxnor, e8)
VALU_MM(vmxnor, e16)
VALU_MM(vmxnor, e32)
VALU_MM(vmxnor, e64)

	li	a0, 0
	jr	ra
