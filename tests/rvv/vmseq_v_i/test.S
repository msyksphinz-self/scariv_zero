#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VI(vmseq, e8)
VALU_VI(vmseq, e16)
VALU_VI(vmseq, e32)
VALU_VI(vmseq, e64)

	li	a0, 0
	jr	ra
