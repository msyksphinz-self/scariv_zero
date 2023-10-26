#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VVF_e32(vfmsac)
VFPU_VVF_e64(vfmsac)

	li	a0, 0
	jr	ra
