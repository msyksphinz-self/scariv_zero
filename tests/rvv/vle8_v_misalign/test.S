#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 1)
VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 2)
VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 3)
VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 4)
VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 5)
VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 6)
VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 7)
VLOAD_V(vle8.v, e8, E8_WIDTH, initial_data, 8)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"
