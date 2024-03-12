#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 1*4)
VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 2*4)
VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 3*4)
VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 4*4)
VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 5*4)
VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 6*4)
VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 7*4)
VLOAD_V(vle32.v, e32, E32_WIDTH, initial_data, 8*4)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"
