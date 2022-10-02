.section .text
_init:
    .word	0x00000297 # auipc   t0,0x0
    .word	0x02028593 # addi    a1,t0,24 # 1018 <dtb>
    # la      a1, dtb
	csrr    a0, mhartid

	ld      t0, 24(t0)
	jr      t0
    .word   0
    .word   0x80000000  # start PC
    .word   0x00000000  # start PC
dtb:
