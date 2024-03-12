#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VVF_e32(vfnmadd)
VFPU_VVF_e64(vfnmadd)

	li	a0, 0
	jr	ra
