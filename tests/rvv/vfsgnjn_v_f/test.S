#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VF_e32(vfsgnjn)
VFPU_VF_e64(vfsgnjn)

	li	a0, 0
	jr	ra
