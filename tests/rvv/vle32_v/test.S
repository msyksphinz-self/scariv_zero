#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VLOAD_V_e32(vle32.v)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"
