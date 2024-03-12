#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VX(vmseq, e8)
VALU_VX(vmseq, e16)
VALU_VX(vmseq, e32)
VALU_VX(vmseq, e64)

	li	a0, 0
	jr	ra
