#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_VV(vmseq, e8)
VALU_VV(vmseq, e16)
VALU_VV(vmseq, e32)
VALU_VV(vmseq, e64)

	li	a0, 0
	jr	ra
