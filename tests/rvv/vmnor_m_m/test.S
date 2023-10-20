#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VALU_MM(vmnor, e8)
VALU_MM(vmnor, e16)
VALU_MM(vmnor, e32)
VALU_MM(vmnor, e64)

	li	a0, 0
	jr	ra
