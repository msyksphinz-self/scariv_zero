#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VSTORE_V(vse32.v, e32, 2)
VLOAD_V (vle64.v, e64, 3)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"
