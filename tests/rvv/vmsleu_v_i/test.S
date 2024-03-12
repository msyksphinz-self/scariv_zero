#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vmsleu, e8)
VALU_VI(vmsleu, e16)
VALU_VI(vmsleu, e32)
VALU_VI(vmsleu, e64)

	li	a0, 0
	jr	ra
