#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmxor, e8)
VALU_MM(vmxor, e16)
VALU_MM(vmxor, e32)
VALU_MM(vmxor, e64)

	li	a0, 0
	jr	ra
