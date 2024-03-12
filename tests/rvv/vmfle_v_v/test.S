#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VV_e32(vmfle)
VFPU_VV_e64(vmfle)

	li	a0, 0
	jr	ra
