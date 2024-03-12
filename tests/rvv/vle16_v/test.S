#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VLOAD_V(vle16.v, e16, 1)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"
