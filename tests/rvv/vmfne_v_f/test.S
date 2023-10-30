#include "../template/valu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VFPU_VF_e32(vmfne)
VFPU_VF_e64(vmfne)

	li	a0, 0
	jr	ra
