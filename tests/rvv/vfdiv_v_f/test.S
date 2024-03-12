#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VF_e32(vfdiv)
VFPU_VF_e64(vfdiv)

	li	a0, 0
	jr	ra
