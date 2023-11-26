#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VLOAD_V(vle8.v, e8, 0)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"
