#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VV_e32(vmflt)
VFPU_VV_e64(vmflt)

	li	a0, 0
	jr	ra
