.section .text
_init:
    la      a1, dtb
	csrr    a0, mhartid

	lw      t0, 24(t0)
	ld      t0, 24(t0)
	jr      t0

dtb:
