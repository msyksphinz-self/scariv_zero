#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VV_e32(vfsgnjx)
VFPU_VV_e64(vfsgnjx)

	li	a0, 0
	jr	ra
