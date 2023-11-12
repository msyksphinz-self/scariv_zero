#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VSTORE_V(vse8.v, e8)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"
