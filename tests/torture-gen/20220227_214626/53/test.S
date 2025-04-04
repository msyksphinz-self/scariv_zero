// random assembly code generated by RISC-V torture test generator
// nseqs = 200
// memsize = 1024

#include "riscv_test.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

	j test_start

crash_backward:
	RVTEST_FAIL

test_start:

xreg_init:
	la x31, xreg_init_data
	ld x0, 0(x31)
	ld x1, 8(x31)
	ld x2, 16(x31)
	ld x3, 24(x31)
	ld x4, 32(x31)
	ld x5, 40(x31)
	ld x6, 48(x31)
	ld x7, 56(x31)
	ld x8, 64(x31)
	ld x9, 72(x31)
	ld x10, 80(x31)
	ld x11, 88(x31)
	ld x12, 96(x31)
	ld x13, 104(x31)
	ld x14, 112(x31)
	ld x15, 120(x31)
	ld x16, 128(x31)
	ld x17, 136(x31)
	ld x18, 144(x31)
	ld x19, 152(x31)
	ld x20, 160(x31)
	ld x21, 168(x31)
	ld x22, 176(x31)
	ld x23, 184(x31)
	ld x24, 192(x31)
	ld x25, 200(x31)
	ld x26, 208(x31)
	ld x27, 216(x31)
	ld x28, 224(x31)
	ld x29, 232(x31)
	ld x30, 240(x31)
	ld x31, 248(x31)

	j pseg_0

pseg_0:
	la x2, test_memory+648
	addi x26, x25, 0
	sw x30, 256(x2)
	la x20, test_memory-62
	remuw x18, x0, x24
	ori x11, x16, 430
	la x28, test_memory-543
	add x3, x16, x16
	andi x24, x1, 613
	div x27, x4, x4
	mulhsu x4, x3, x23
	remw x22, x1, x1
	addi x19, x26, 0
	la x13, test_memory-429
	la x2, test_memory-116
	mulhsu x1, x15, x15
	lw x25, 1353(x13)
	addi x10, x0, 1019
	mulh x6, x31, x31
	addi x5, x0, 298
	lwu x7, 1079(x28)
	addw x17, x21, x5
	addi x15, x0, 86
	rem x29, x10, x8
	addi x27, x0, -1779
	la x13, test_memory+1700
	sltiu x31, x14, -92
	sw x17, 428(x2)
	rem x6, x13, x4
	addi x17, x0, -1997
	addi x28, x0, 1
	add x12, x5, x15
	div x9, x31, x11
	la x18, test_memory+930
	and x2, x17, x17
	addi x23, x0, -573
	addi x30, x23, -481
	sltu x12, x16, x16
	bltu x23, x30, crash_backward
	lbu x16, 79(x20)
	divuw x22, x10, x27
	la x3, test_memory+1866
	addi x21, x0, -118
	la x24, test_memory-880
	blt x26, x19, crash_backward
	lb x4, -1270(x3)
	sll x28, x28, 63
	sh x16, 1172(x24)
	lhu x11, -372(x18)
	or x5, x13, x0
	addi x6, x0, 1444
	divu x9, x8, x17
	la x30, test_memory-522
	div x22, x1, x18
	ld x5, 1234(x30)
	addi x8, x0, 1987
	sraw x14, x21, x8
	divw x20, x15, x23
	la x23, test_memory-1279
	xor x18, x22, x22
	addi x11, x0, 1
	la x7, test_memory+1442
	sw x31, -1314(x7)
	la x2, test_memory-788
	addi x22, x0, 582
	lwu x1, -1412(x13)
	lbu x3, 1370(x23)
	lh x12, 1540(x2)
	la x18, test_memory-1571
	addi x5, x0, -1026
	slli x27, x23, 15
	lhu x14, 1683(x18)
	mulh x15, x6, x6
	addi x31, x0, -1
	xor x30, x22, x22
	addi x20, x0, -936
	sll x11, x11, 63
	addi x7, x0, 1782
	addi x8, x0, -358
	la x24, test_memory-1588
	remw x9, x7, x8
	lh x1, 1786(x24)
	addi x4, x0, 142
	addi x26, x0, 1982
	addi x16, x0, -1
	xor x31, x31, x28
	xor x16, x16, x11
	add x21, x5, x20
	and x19, x13, x16
	and x25, x24, x31
	or x10, x19, x11
	slt x17, x4, x26
	sraiw x30, x12, 8
	bgeu x19, x10, crash_backward
	la x17, test_memory-977
	addi x8, x24, 0
	addi x26, x0, 1
	la x12, test_memory+744
	addi x14, x0, 597
	lbu x7, 1084(x17)
	sll x26, x26, 63
	addi x15, x0, 455
	addi x18, x8, 0
	addi x24, x0, -1
	addi x4, x15, 175
	or x29, x21, x28
	addi x6, x0, 1
	addi x9, x14, 144
	beq x25, x29, crash_forward
	sh x19, 18(x12)
	addi x2, x0, 0
	la x1, test_memory-574
	addi x7, x0, 1
	la x29, test_memory+553
	xori x17, x19, 2022
	addi x31, x0, 480
	xor x24, x24, x26
	sll x7, x7, 63
	or x20, x25, x25
	lbu x25, -230(x29)
	la x29, test_memory-405
	lw x5, 1134(x1)
	lh x17, 923(x29)
	la x20, test_memory-148
	addi x12, x0, 1748
	lbu x4, 1134(x20)
	add x25, x19, x19
	sllw x22, x14, x8
	xor x28, x31, x12
	mulw x21, x24, x18
	remw x15, x27, x27
	addi x27, x0, 0
	bne x2, x27, crash_forward
	and x13, x30, x24
	or x23, x13, x26
	addi x11, x0, -1
	addi x27, x0, 0
	slt x21, x30, x17
	addi x2, x0, 0
	sltu x22, x31, x31
	sll x6, x6, 63
	addi x29, x0, -609
	remw x5, x26, x26
	addi x25, x0, 0
	xor x11, x11, x7
	sltu x1, x19, x4
	mulh x4, x19, x19
	addi x20, x0, 0
	bne x27, x25, crash_forward
	addi x16, x0, -1
	la x15, test_memory-506
	and x10, x6, x11
	lbu x17, 743(x15)
	xor x16, x16, x6
	divw x21, x16, x16
	bne x2, x20, crash_backward
	add x31, x29, x29
	and x30, x4, x16
	or x19, x12, x6
	addi x28, x0, 913
	la x14, test_memory+1116
	addi x8, x0, -884
	or x3, x10, x7
	addi x25, x0, 0
	addi x9, x0, 38
	beq x30, x19, crash_backward
	la x17, test_memory+359
	sltu x12, x28, x28
	la x18, test_memory-1029
	la x29, test_memory+1738
	lw x30, -1494(x29)
	la x2, test_memory-1348
	sltu x22, x8, x9
	la x19, test_memory-300
	slti x6, x21, -29
	addi x23, x0, 1
	sb x24, 767(x19)
	sll x23, x23, 63
	lwu x4, -335(x17)
	bgeu x10, x3, crash_forward
	sb x10, 1445(x2)
	sub x21, x24, x24
	divu x5, x25, x25
	addi x16, x0, 1
	sll x16, x16, 63
	addi x27, x0, 0
	la x15, test_memory-128
	sb x27, 339(x15)
	addi x26, x0, -1
	xor x26, x26, x23
	sw x3, -1116(x14)
	and x20, x26, x26
	addi x28, x0, -1
	or x31, x20, x23
	bgeu x20, x31, crash_backward
	lw x1, 1237(x18)
	xor x28, x28, x16
	and x24, x5, x28
	or x13, x0, x16
	bgeu x24, x13, crash_backward
	addi x18, x0, -327
	addi x17, x0, -475
	addi x6, x0, 1692
	mulhu x13, x18, x18
	addi x29, x0, 1671
	mulw x26, x21, x1
	sltiu x30, x7, -1234
	la x8, test_memory-513
	addi x15, x0, -783
	addi x9, x0, 662
	remu x20, x17, x6
	la x10, test_memory+1125
	sb x30, -331(x10)
	addi x11, x0, 901
	la x22, test_memory-906
	la x4, test_memory-9
	addi x30, x0, -1915
	addw x13, x0, x26
	addi x26, x0, 1
	addi x25, x0, -1395
	and x28, x25, x25
	mul x18, x30, x30
	sllw x2, x9, x9
	la x5, test_memory+2199
	remuw x12, x30, x30
	addi x27, x0, 819
	la x21, test_memory+1626
	addi x3, x0, 1324
	sh x26, -1641(x5)
	sll x26, x26, 63
	remw x14, x11, x3
	addi x10, x0, -1
	lwu x1, 1462(x22)
	and x24, x29, x27
	xor x10, x10, x26
	sw x20, -1230(x21)
	and x17, x28, x10
	lui x31, 109149
	lb x16, 401(x4)
	ld x19, 1505(x8)
	or x20, x17, x26
	addi x23, x0, 334
	add x7, x15, x23
	addi x8, x0, -1999
	div x27, x9, x9
	la x13, test_memory+2110
	la x7, test_memory-625
	sltu x21, x6, x27
	addi x19, x0, 0
	lh x24, -1646(x13)
	addi x29, x0, -1642
	addi x26, x0, -857
	la x1, test_memory+379
	sraw x16, x3, x3
	addi x18, x0, 496
	la x17, test_memory+172
	mulhsu x28, x31, x31
	or x25, x5, x5
	xor x2, x29, x26
	lh x6, 551(x1)
	lhu x22, 58(x17)
	addi x3, x0, -1510
	mulhsu x25, x21, x16
	sw x0, 1561(x7)
	addi x6, x0, -1819
	addi x24, x0, 484
	sll x15, x18, x3
	addi x26, x0, -1946
	addi x5, x0, 786
	addi x4, x0, 401
	mulw x31, x5, x5
	addi x10, x0, 0
	addi x1, x0, -575
	addi x29, x0, 696
	rem x14, x20, x2
	mulw x27, x24, x24
	bltu x19, x10, crash_backward
	addi x30, x0, -501
	addi x9, x0, -446
	addi x31, x0, 1
	slt x16, x26, x29
	addi x13, x0, 796
	sll x31, x31, 63
	sltiu x12, x16, -1855
	addi x25, x0, -1
	srl x2, x6, x13
	andi x11, x28, -677
	la x12, test_memory-798
	la x15, test_memory+1892
	slt x16, x9, x9
	la x2, test_memory-1306
	sb x5, 1716(x2)
	sb x18, 1202(x12)
	sll x13, x23, x23
	srl x29, x25, x26
	divw x20, x8, x8
	la x17, test_memory+1914
	addi x5, x0, 1333
	addi x27, x0, 1798
	remuw x28, x1, x9
	la x3, test_memory+324
	addi x11, x0, 2029
	xor x25, x25, x31
	srlw x24, x5, x27
	addi x20, x0, -39
	and x21, x21, x25
	la x5, test_memory-126
	addi x14, x0, -954
	sllw x9, x19, x23
	addi x10, x0, 1040
	sw x16, -1004(x15)
	addi x28, x0, -1937
	sra x23, x4, x30
	addi x24, x0, 478
	addi x6, x11, 1966
	ld x18, -1850(x17)
	slt x18, x4, x19
	la x17, test_memory-511
	or x13, x8, x8
	or x19, x18, x31
	addi x30, x24, 1630
	la x7, test_memory-758
	sw x27, 1142(x7)
	bge x19, x21, crash_forward
	bltu x6, x11, crash_backward
	sra x22, x14, x10
	srlw x8, x1, x10
	sh x18, 787(x17)
	la x12, test_memory+6
	la x14, test_memory+374
	subw x10, x23, x23
	div x11, x12, x12
	mulw x8, x19, x0
	div x29, x20, x28
	mulhu x22, x29, x29
	ori x25, x7, -555
	la x6, test_memory-910
	la x10, test_memory+255
	lh x21, 1160(x6)
	xor x8, x28, x5
	sb x27, -130(x3)
	addi x2, x0, 1
	addi x25, x0, -1882
	sb x9, 72(x14)
	lhu x16, 818(x12)
	addi x24, x0, 100
	la x29, test_memory-722
	srliw x11, x31, 3
	addi x17, x0, -405
	addw x6, x28, x28
	sb x16, 386(x10)
	addi x1, x0, -302
	sll x30, x17, x17
	addi x7, x0, -2044
	addi x17, x0, 978
	addi x28, x0, 1796
	sraw x20, x25, x24
	lh x22, 842(x29)
	addw x18, x28, x28
	lwu x27, 502(x5)
	sll x2, x2, 63
	addi x4, x0, 1
	addi x8, x0, 300
	remu x16, x29, x9
	mulhsu x10, x17, x17
	addi x30, x0, 962
	la x24, test_memory-657
	divw x6, x30, x30
	divuw x3, x18, x18
	la x27, test_memory+2323
	addi x21, x8, 825
	addi x12, x0, -517
	remuw x13, x1, x7
	addi x25, x0, -57
	la x10, test_memory-49
	addi x11, x0, 933
	la x16, test_memory-1321
	divuw x29, x25, x25
	la x28, test_memory-311
	sw x6, 583(x28)
	sw x22, -1779(x27)
	addi x19, x0, -1
	sb x4, 881(x24)
	la x28, test_memory+2138
	addi x1, x0, -401
	la x25, test_memory+907
	sd x4, 385(x10)
	mulhsu x20, x18, x8
	addi x5, x0, 455
	addi x22, x0, 289
	lw x7, -1858(x28)
	sra x14, x12, x11
	sb x9, 1385(x16)
	addi x3, x0, -643
	la x7, test_memory-549
	addi x28, x0, 1
	xor x19, x19, x2
	sll x4, x4, 63
	and x26, x15, x19
	addi x30, x0, 664
	la x24, test_memory-1691
	bge x8, x21, crash_backward
	addi x18, x0, -1975
	sll x28, x28, 63
	mulhu x17, x5, x22
	sw x1, 841(x7)
	or x31, x18, x2
	addi x10, x0, -1
	addi x23, x0, -1
	lb x13, -495(x25)
	xor x10, x10, x28
	xor x23, x23, x4
	and x15, x22, x23
	la x11, test_memory-1268
	and x20, x10, x10
	or x27, x28, x28
	sra x29, x1, x3
	sllw x6, x30, x18
	sh x18, 1502(x11)
	lwu x16, 1927(x24)
	or x9, x13, x4
	beq x15, x9, crash_forward
	j reg_dump

reg_dump:
	la x1, loop_count
	lw x2, 0(x1)
	addi x3, x2, -1
	sw x3, 0(x1)
	bnez x2, pseg_0
	la x1, xreg_output_data
	sd x0, 0(x1)
	sd x2, 16(x1)
	sd x3, 24(x1)
	sd x4, 32(x1)
	sd x5, 40(x1)
	sd x6, 48(x1)
	sd x8, 64(x1)
	sd x9, 72(x1)
	sd x10, 80(x1)
	sd x12, 96(x1)
	sd x13, 104(x1)
	sd x14, 112(x1)
	sd x15, 120(x1)
	sd x16, 128(x1)
	sd x17, 136(x1)
	sd x18, 144(x1)
	sd x19, 152(x1)
	sd x20, 160(x1)
	sd x21, 168(x1)
	sd x22, 176(x1)
	sd x23, 184(x1)
	sd x26, 208(x1)
	sd x27, 216(x1)
	sd x28, 224(x1)
	sd x29, 232(x1)
	sd x30, 240(x1)
	sd x31, 248(x1)

	j test_end

crash_forward:
	RVTEST_FAIL

test_end:
	RVTEST_PASS

RVTEST_CODE_END


	.data

hidden_data:
	.align 8
xreg_init_data:
reg_x0_init:	.dword 0xcf36a13bcb0d02f8
reg_x1_init:	.dword 0xffe32bf0a2e1e054
reg_x2_init:	.dword 0x0000000000000020
reg_x3_init:	.dword 0xffffffffffffffff
reg_x4_init:	.dword 0xffffffff80000006
reg_x5_init:	.dword 0x0000000000000000
reg_x6_init:	.dword 0xffffffff80000007
reg_x7_init:	.dword 0x8b12b3a642ecd2d0
reg_x8_init:	.dword 0xffffffffffff8005
reg_x9_init:	.dword 0x0000000000000000
reg_x10_init:	.dword 0x0000000000000001
reg_x11_init:	.dword 0xffffffffffffff88
reg_x12_init:	.dword 0x412e02cf543db797
reg_x13_init:	.dword 0x66d2d47cad41cf39
reg_x14_init:	.dword 0x632c797270472f66
reg_x15_init:	.dword 0xed3cd066af844311
reg_x16_init:	.dword 0xffffffffffffffff
reg_x17_init:	.dword 0xfc059e636534023a
reg_x18_init:	.dword 0x0c62996a714b65fb
reg_x19_init:	.dword 0x0800000000000006
reg_x20_init:	.dword 0xffffffffffffff88
reg_x21_init:	.dword 0xcede087741d88440
reg_x22_init:	.dword 0x5c0193bee3de9731
reg_x23_init:	.dword 0xffffffffffffff86
reg_x24_init:	.dword 0x5438f46739a5fdd4
reg_x25_init:	.dword 0xffffffffffffffff
reg_x26_init:	.dword 0x32b0f09580272d3d
reg_x27_init:	.dword 0xa562178e03a4fbfc
reg_x28_init:	.dword 0x5d898823a34efc91
reg_x29_init:	.dword 0xdb3c01fff37f02ce
reg_x30_init:	.dword 0x679c9eba8b94d1a7
reg_x31_init:	.dword 0x0000000000000007

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0x07e230da0f09e8d2
reg_x1_output:	.dword 0xc246a40bf328c7f0
reg_x2_output:	.dword 0x90ecf6f37dae4fa5
reg_x3_output:	.dword 0x1bb53c357a5ed9cc
reg_x4_output:	.dword 0xb5d32780756dbc64
reg_x5_output:	.dword 0x802180462606a829
reg_x6_output:	.dword 0x0123220393b36104
reg_x7_output:	.dword 0x479b33fbc104ca7d
reg_x8_output:	.dword 0x97350b51d4817294
reg_x9_output:	.dword 0xdf2135e4fe650faf
reg_x10_output:	.dword 0x21b7496213f25a7e
reg_x11_output:	.dword 0x61969159ecc45afe
reg_x12_output:	.dword 0x6a666867acc5380c
reg_x13_output:	.dword 0x33a23babdc80eb22
reg_x14_output:	.dword 0x8ab5bd21c272762e
reg_x15_output:	.dword 0x15b0f09c89856fb0
reg_x16_output:	.dword 0x9caf5870a9cd797a
reg_x17_output:	.dword 0xd6d3e21267e590c2
reg_x18_output:	.dword 0x3ea7202aa004aa73
reg_x19_output:	.dword 0xb7ae2f055cc8ccd6
reg_x20_output:	.dword 0x98c6212f5521600d
reg_x21_output:	.dword 0xf94e55c04d8ad0f6
reg_x22_output:	.dword 0xd6306eb9413d6e70
reg_x23_output:	.dword 0xd7f0154683c6af19
reg_x24_output:	.dword 0xacd922f5d2bc5dfc
reg_x25_output:	.dword 0xd0767215507496c9
reg_x26_output:	.dword 0xf43d54da0c328e8d
reg_x27_output:	.dword 0x0034d20ae097f405
reg_x28_output:	.dword 0xd57817317284caff
reg_x29_output:	.dword 0x5c9963a545761868
reg_x30_output:	.dword 0x8baed4f44b6f10f4
reg_x31_output:	.dword 0x8aba446e172bd28a

// Memory Blocks
	.align 8
test_memory:
	.dword 0x4bf69ede3a4990d4, 0x18ea1ab544fa97a5
	.dword 0xe4c83e3ca0cf2a15, 0x8d901680f10c237b
	.dword 0x3022210cac18e7bb, 0x21ca8dc117f5b277
	.dword 0x1dd4734247364122, 0x8322a7c81d323a12
	.dword 0x0664f963f50222fb, 0xc10acbf6a75d4378
	.dword 0x17bd8060be510494, 0xb048c7bae76e4c6a
	.dword 0x0cb0f69e60948d5b, 0xdb07dfb9ffced266
	.dword 0x5c90824defd58ea4, 0x475e4047b1236c04
	.dword 0x99cb290765ad55a9, 0x6ad4811f4d4294a2
	.dword 0x9327dc9199f399d2, 0xef35304eab5a0e43
	.dword 0xd3d30101e1668b37, 0x16d598730cedfdb4
	.dword 0x8075c006cee6c562, 0xa3e83624906b24f0
	.dword 0x0c1ebd831d392a59, 0xea7c90b295b7dfc5
	.dword 0x6c29015ca5dce9da, 0xded76a11e1c5c6b6
	.dword 0xf7c72a960da438e8, 0x6d097a1201e01c23
	.dword 0xfba63f98cda27d86, 0x925a28d37c9167a7
	.dword 0xcd7cafd5ceeaf2c2, 0xa07efc7776bce3c0
	.dword 0x3b8f5a908dc708f4, 0xccefae182e2ea1b5
	.dword 0x0a7faef5c5bc0647, 0xef3219fbc1af87b4
	.dword 0x9d533970e72bab78, 0xc6f87f074fd88d3a
	.dword 0x41d6323bf1d3e0de, 0xb19fc17043b2d9b7
	.dword 0x237fe137f12dafa9, 0xb542a4b756e8a971
	.dword 0xe218eb00f0ec0b6e, 0xc17230d62f251ca8
	.dword 0xd4d0db3c44df2fe2, 0xf9f2b6b5b57f54fa
	.dword 0x4f718031e88996e5, 0x81e027e42daf8508
	.dword 0xd333eba243ffcac2, 0x3493b5845d92d65a
	.dword 0x08a42cd20d7c98b5, 0xe0cfea849e6d497f
	.dword 0x213e17e74da767ad, 0x4157b515b6a6f478
	.dword 0xcf3eae75c822b752, 0x17681356beb44356
	.dword 0x35cafd5a7ed50b48, 0x6ed35752dcaf1f22
	.dword 0xf44683c684bec6b5, 0x5bf8362e3a211efc
	.dword 0xfac0779f7153bc00, 0x10be16998cdd2786
	.dword 0xfc007b04177774dc, 0x4a63528ed0c91c82
	.dword 0xb930972c87a77684, 0x1d81603b3b5e88b9
	.dword 0xc4ab907d3bcf0647, 0x83761635fcb3601e
	.dword 0xc253e7d0b8f43247, 0xb3a07ef96b4a4033
	.dword 0x3d491d191fa6227d, 0xe6d2ef8fc1fbd2ac
	.dword 0x5a1607297c10f5ff, 0x3b43558d88413651
	.dword 0x82cc54d11a1bb085, 0xd65df0421f419228
	.dword 0x852e8b2a6538fc29, 0x576de9272f8336d2
	.dword 0xeb4b1531a6dbc36d, 0x25527f9fe642f235
	.dword 0xe200389b460ce782, 0x01aebbe40c7a795b
	.dword 0x200a03df7eaf96c7, 0xb06cdd361ec90c99
	.dword 0xa0b8899823d6078f, 0xfa4df75a2affb9f3
	.dword 0xe87dfd0d2e609b27, 0x1fd173437844e1bf
	.dword 0x0469840f243dad16, 0x2e47670fe7d8e187
	.dword 0xb19cd205dd4092a6, 0xfe9bf938b8c00933
	.dword 0x9417e045a4ea8ea3, 0xd399430576343e67
	.dword 0x2e1757a60ce8bd62, 0x2740663e8a02f22a
	.dword 0x47f77f530eb63d04, 0xc3b1ca2847224cc7
	.dword 0xa556c4e0fc0215fc, 0x7f27b3ae8012b3f7
	.dword 0x8c5031a1996ca7cd, 0x0b05acdf7e500f3f
	.dword 0xa857613afe289e18, 0x1f326f97b6686e97
	.dword 0xe8c4cd742147b1d5, 0xbc1947810583f74c
	.dword 0xecba834d8b3bbae0, 0x520b1f3ceb843b26
	.dword 0x77f6955a6398d5b7, 0xd386acdbbe9f5dcd
	.dword 0xffa9df4800ada182, 0x4472719294bdac68
	.dword 0x20beeebe7452da53, 0x61ca80aeca268b86
	.dword 0x5b66256a0fa3d3ad, 0xdeef41c6fe73df41
	.dword 0xaf79685a0265974a, 0x3ee1a230d69151a0
	.dword 0x2b9af0899afaac18, 0x038c69b62eff1b3d
	.dword 0x831810be0d1dc985, 0x4301a688f2e63227
	.dword 0xb5d20492587dfafc, 0x558e6473ed060309
	.dword 0x7efc1cce00faf7ae, 0x5ef623536d62188b

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
