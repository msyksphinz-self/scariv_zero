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
	mulhsu x26, x29, x29
	la x31, test_memory+1339
	sub x11, x14, x14
	la x1, test_memory-870
	addi x29, x0, 162
	sd x30, 1646(x1)
	la x28, test_memory+145
	addi x3, x29, 650
	addi x18, x0, -1702
	sraw x22, x22, x18
	sra x16, x3, x25
	addi x30, x0, 1532
	addi x7, x0, 1993
	lb x24, -318(x31)
	addi x17, x0, 1
	addi x8, x0, 1
	mul x10, x20, x13
	addi x11, x0, -1210
	addi x24, x0, 0
	lw x23, 615(x28)
	div x26, x31, x28
	subw x27, x30, x7
	and x4, x17, x17
	sltu x22, x1, x16
	addi x6, x27, 0
	mul x19, x11, x11
	sll x1, x25, x4
	remu x31, x24, x24
	sll x17, x17, 63
	addi x25, x0, -1043
	sll x8, x8, 63
	addi x9, x6, 0
	slti x15, x13, 227
	addi x12, x0, -1
	addi x5, x0, -1
	addi x3, x0, 15
	addi x19, x0, -1880
	remu x26, x12, x23
	sltu x14, x18, x25
	addi x10, x0, 0
	rem x29, x25, x8
	addi x31, x0, 976
	divu x22, x3, x3
	bltu x24, x10, crash_backward
	xor x5, x5, x8
	bne x16, x16, crash_backward
	div x28, x19, x19
	and x21, x24, x5
	addi x25, x0, -253
	addi x3, x0, -1966
	addi x4, x31, 1737
	xor x12, x12, x17
	or x2, x21, x8
	addi x10, x0, -362
	sra x27, x25, x3
	beq x21, x2, crash_forward
	la x23, test_memory+1457
	srlw x19, x5, x5
	and x20, x25, x12
	la x15, test_memory+1400
	addi x26, x0, 1
	remuw x29, x10, x10
	sll x1, x11, x22
	addi x30, x0, -776
	remuw x16, x30, x30
	addi x19, x5, 0
	addi x25, x0, 1
	la x29, test_memory+790
	sll x25, x25, 63
	divu x14, x14, x14
	or x13, x20, x17
	la x8, test_memory-348
	sw x20, 652(x8)
	sd x5, -382(x29)
	addi x28, x0, 1179
	slti x3, x26, -621
	addi x2, x0, -1
	xor x27, x31, x5
	addi x16, x19, 0
	addi x1, x0, -1956
	la x21, test_memory+1371
	mulhu x29, x25, x25
	sw x4, -532(x15)
	addi x3, x0, -952
	lhu x30, -1189(x21)
	lb x7, -588(x23)
	addi x4, x0, 608
	xor x2, x2, x25
	sll x26, x26, 63
	addi x5, x0, 1589
	and x9, x30, x2
	mulh x31, x3, x3
	addi x18, x0, -1
	la x29, test_memory+252
	la x27, test_memory-594
	slli x15, x24, 39
	lh x30, 1500(x27)
	xor x18, x18, x26
	addi x6, x1, -1900
	addi x13, x0, -785
	la x21, test_memory+1759
	sraiw x31, x28, 10
	divu x7, x3, x4
	srlw x12, x27, x25
	divuw x16, x13, x13
	la x17, test_memory+1850
	addi x30, x0, 0
	lbu x20, -1545(x17)
	sub x10, x28, x5
	slli x23, x2, 19
	sllw x16, x6, x6
	addi x27, x0, 1492
	addi x12, x0, 0
	sw x25, -1307(x21)
	sraw x7, x27, x27
	addi x7, x0, 267
	blt x30, x12, crash_forward
	mulhsu x17, x20, x30
	addi x8, x0, -231
	lh x19, 344(x29)
	addi x28, x0, 0
	addi x27, x0, -558
	addi x13, x0, 0
	addi x5, x0, 1164
	and x11, x7, x18
	or x24, x11, x26
	mulh x31, x2, x11
	addi x19, x0, 1228
	and x14, x4, x8
	la x29, test_memory+1704
	addw x16, x7, x5
	la x23, test_memory+2599
	addi x12, x19, 2011
	bge x19, x12, crash_forward
	sh x24, -1721(x23)
	addi x15, x0, 0
	la x12, test_memory+1055
	bltu x13, x15, crash_forward
	la x6, test_memory+1910
	sd x2, -902(x6)
	la x1, test_memory-1056
	sb x4, 1937(x1)
	la x15, test_memory-1364
	la x23, test_memory-884
	or x22, x31, x25
	bltu x22, x9, crash_forward
	add x30, x28, x28
	addi x4, x0, -1104
	la x16, test_memory-586
	la x13, test_memory+1001
	addi x24, x0, 1090
	addi x11, x4, -1553
	lwu x5, -183(x12)
	sd x22, 956(x23)
	sb x24, -257(x13)
	la x14, test_memory-453
	lw x17, -692(x29)
	addi x20, x0, 1034
	la x8, test_memory-1619
	sd x18, 1389(x14)
	addi x21, x0, 0
	la x7, test_memory+414
	bltu x28, x21, crash_backward
	bgeu x11, x4, crash_forward
	div x3, x18, x18
	addi x1, x0, 599
	addi x4, x0, -768
	addi x18, x0, 610
	la x29, test_memory+1814
	sh x31, 1983(x8)
	addiw x21, x21, -1251
	addi x6, x0, 1356
	mulw x10, x27, x20
	div x26, x24, x24
	lhu x19, 260(x7)
	la x14, test_memory+492
	sw x10, 1458(x16)
	sub x25, x23, x18
	sd x28, -894(x29)
	lh x31, 1516(x15)
	sd x31, 436(x14)
	la x13, test_memory+2666
	remuw x9, x1, x4
	addi x22, x0, 683
	la x26, test_memory-963
	addi x10, x0, 1806
	la x16, test_memory+2042
	addi x9, x0, -668
	la x30, test_memory-133
	remu x11, x6, x22
	lb x21, 1920(x26)
	la x31, test_memory+582
	sllw x5, x9, x9
	mulhsu x24, x30, x10
	la x7, test_memory+844
	addi x27, x0, 333
	addi x2, x0, 1483
	subw x3, x18, x2
	addi x26, x0, 1806
	addi x1, x0, -1571
	addi x15, x0, 779
	lw x4, -142(x31)
	addi x11, x0, 1151
	la x28, test_memory+556
	addi x19, x10, 702
	addi x3, x0, -675
	slt x6, x26, x26
	addi x2, x0, -1919
	addi x18, x3, -938
	srlw x5, x7, x25
	sw x11, -1590(x16)
	addi x21, x0, -724
	la x31, test_memory+1243
	bge x10, x19, crash_forward
	sh x25, -683(x31)
	lh x14, -438(x7)
	mul x4, x2, x21
	div x9, x11, x11
	sltu x21, x11, x11
	addi x29, x0, 1250
	div x12, x27, x29
	beq x3, x18, crash_forward
	lwu x23, -1806(x13)
	divuw x8, x1, x15
	addi x6, x0, -397
	addi x5, x0, 409
	addi x31, x0, 12
	addi x3, x0, 1
	addi x22, x0, 361
	bltu x12, x12, crash_forward
	sllw x27, x30, x30
	la x29, test_memory+497
	subw x7, x31, x31
	sw x17, 989(x30)
	sw x21, 311(x29)
	addi x17, x0, -670
	subw x26, x6, x5
	addw x24, x22, x17
	addi x4, x0, -133
	addi x2, x0, -610
	and x1, x21, x7
	addi x21, x0, -1419
	lhu x25, -488(x28)
	sll x3, x3, 63
	sllw x20, x27, x27
	la x9, test_memory-1128
	lwu x11, 2040(x9)
	srlw x18, x21, x21
	addi x10, x0, -973
	addi x8, x0, -1
	div x19, x4, x2
	addi x16, x0, -1646
	mulh x14, x10, x16
	xor x8, x8, x3
	and x12, x21, x8
	or x15, x12, x3
	bgeu x12, x15, crash_backward
	la x7, test_memory-38
	la x30, test_memory+2305
	lb x17, 42(x7)
	la x16, test_memory+931
	remu x31, x28, x11
	la x3, test_memory+1857
	addi x20, x0, 1
	la x10, test_memory-756
	ld x11, -1545(x30)
	lb x18, -727(x16)
	sraiw x21, x9, 21
	sll x20, x20, 63
	sw x17, 812(x10)
	la x27, test_memory+941
	addi x5, x0, -1404
	addi x28, x0, 108
	addi x13, x0, -1
	la x23, test_memory+1175
	addi x8, x0, -1107
	blt x0, x0, crash_backward
	addi x26, x0, 1192
	srl x29, x28, x26
	la x10, test_memory+774
	la x17, test_memory+1223
	la x2, test_memory+139
	mulw x26, x0, x0
	lb x19, -287(x17)
	addi x31, x0, -1961
	la x4, test_memory-1322
	sb x19, -247(x10)
	xor x13, x13, x20
	addi x9, x8, -190
	addi x25, x5, -1124
	and x15, x0, x13
	la x7, test_memory-79
	sw x11, 1866(x4)
	lh x6, 587(x2)
	sw x5, 367(x7)
	mulhu x1, x31, x31
	addi x21, x0, 1
	la x17, test_memory+471
	mulhu x8, x1, x31
	sll x21, x21, 63
	sraw x6, x14, x14
	la x28, test_memory+2433
	ld x19, -55(x17)
	sb x5, -1021(x23)
	subw x16, x19, x19
	la x26, test_memory+2241
	la x25, test_memory+9
	lh x22, -787(x27)
	la x2, test_memory+1514
	lbu x29, -2008(x28)
	addi x4, x0, -626
	andi x5, x19, -7
	sh x5, -1284(x2)
	sw x20, -1305(x26)
	or x24, x15, x20
	sltiu x8, x18, -806
	addi x9, x0, -1579
	bge x24, x15, crash_backward
	la x14, test_memory+2085
	addi x30, x0, -1
	xor x30, x30, x21
	addi x17, x0, 1383
	sra x7, x21, x21
	la x22, test_memory-1468
	la x1, test_memory+719
	addi x28, x17, 544
	and x10, x4, x9
	srl x27, x25, x29
	addi x13, x0, -1491
	and x11, x12, x30
	sb x9, -279(x1)
	addi x2, x0, 1667
	la x6, test_memory-1215
	addi x23, x0, 456
	sw x20, -1489(x14)
	addi x27, x0, -1129
	or x18, x11, x21
	addi x19, x0, 614
	ld x12, -1265(x3)
	addi x24, x0, -340
	addi x9, x0, 1
	divuw x7, x27, x27
	lw x26, 1908(x22)
	xor x16, x2, x24
	bge x18, x11, crash_backward
	ld x31, 431(x25)
	mulh x8, x19, x19
	la x25, test_memory-567
	la x11, test_memory+2295
	sb x9, 1799(x6)
	sllw x16, x28, x3
	addi x18, x0, 740
	addi x5, x0, 1605
	la x1, test_memory+551
	sll x9, x9, 63
	la x30, test_memory-1645
	addi x21, x18, 804
	addi x28, x0, 1
	divw x15, x23, x5
	addi x20, x13, -76
	lbu x27, 1064(x25)
	lbu x14, 2031(x30)
	addi x4, x0, -1
	sb x9, -369(x1)
	bltu x13, x20, crash_forward
	la x2, test_memory+2287
	sll x28, x28, 63
	lwu x22, -1735(x11)
	la x7, test_memory+1150
	addi x12, x0, 1066
	mul x31, x12, x12
	la x30, test_memory-162
	xor x4, x4, x9
	addi x17, x0, -1
	and x10, x14, x4
	sd x12, -470(x7)
	la x11, test_memory+429
	lh x12, 451(x11)
	addi x13, x0, 378
	lwu x3, -1603(x2)
	divu x22, x5, x20
	or x29, x14, x9
	rem x15, x4, x4
	addi x14, x22, 0
	blt x21, x18, crash_backward
	la x1, test_memory+1237
	mulhsu x20, x13, x13
	addi x25, x0, 970
	blt x10, x29, crash_forward
	sh x23, -357(x1)
	addi x29, x0, -1648
	addi x7, x0, 185
	addi x2, x0, -1563
	la x11, test_memory-1327
	add x18, x26, x26
	addi x19, x0, -270
	xor x17, x17, x28
	and x6, x4, x17
	mul x4, x7, x7
	ld x16, 282(x30)
	addi x9, x0, 1
	or x8, x6, x28
	la x31, test_memory+768
	ld x22, 1447(x11)
	addiw x20, x16, 1769
	addi x24, x0, 1023
	subw x21, x2, x2
	sll x9, x9, 63
	sll x26, x19, x24
	addi x13, x0, -1744
	divu x3, x29, x13
	lbu x15, -536(x31)
	la x12, test_memory-331
	lb x10, 905(x12)
	addi x27, x0, 1133
	addi x1, x0, 10
	addi x4, x0, -428
	la x29, test_memory+1737
	addi x12, x0, -1843
	addi x6, x0, -983
	addi x26, x0, 1858
	srl x23, x25, x27
	la x11, test_memory+1421
	addi x30, x0, -1
	sltu x15, x6, x6
	slt x3, x12, x12
	and x18, x1, x4
	addi x17, x0, -1028
	addi x20, x0, -148
	lbu x24, -1725(x29)
	la x19, test_memory+1960
	divw x21, x26, x17
	addi x28, x0, 1
	sll x28, x28, 63
	addi x5, x14, 0
	xor x30, x30, x9
	and x16, x25, x30
	addi x22, x0, 1898
	addi x2, x0, -1
	or x7, x16, x9
	sh x24, -1510(x19)
	srlw x8, x20, x22
	bge x7, x16, crash_backward
	xor x2, x2, x28
	lhu x31, -971(x11)
	and x13, x5, x2
	or x10, x9, x28
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
	sd x7, 56(x1)
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
	sd x20, 160(x1)
	sd x21, 168(x1)
	sd x22, 176(x1)
	sd x23, 184(x1)
	sd x24, 192(x1)
	sd x25, 200(x1)
	sd x26, 208(x1)
	sd x27, 216(x1)
	sd x28, 224(x1)
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
reg_x0_init:	.dword 0xce669d6c6c1a9507
reg_x1_init:	.dword 0xb77211f3dcf875d4
reg_x2_init:	.dword 0x3d124fb108e12f31
reg_x3_init:	.dword 0x9495703a2dc70273
reg_x4_init:	.dword 0xdf7f9828e71fc732
reg_x5_init:	.dword 0xffffffffffff8007
reg_x6_init:	.dword 0xffffffffffffffff
reg_x7_init:	.dword 0x0000000000000007
reg_x8_init:	.dword 0xbfef28579e3e1461
reg_x9_init:	.dword 0x686771631d5ac1b3
reg_x10_init:	.dword 0xce3a6bb7f0847947
reg_x11_init:	.dword 0xffffffffffffffff
reg_x12_init:	.dword 0x78066c0fbb0e299d
reg_x13_init:	.dword 0x0000000000000020
reg_x14_init:	.dword 0xffffffffffffffff
reg_x15_init:	.dword 0xffffffffffffffff
reg_x16_init:	.dword 0xfffffffffffffffe
reg_x17_init:	.dword 0x0b45b78e5c668af0
reg_x18_init:	.dword 0x0000000000000000
reg_x19_init:	.dword 0x629cef19dbb4da5f
reg_x20_init:	.dword 0xffffffffffffffff
reg_x21_init:	.dword 0xe39cac2dd56f2bda
reg_x22_init:	.dword 0x772bb9398db53f3e
reg_x23_init:	.dword 0x0000000000000000
reg_x24_init:	.dword 0x9ff9dd266f36b6bc
reg_x25_init:	.dword 0xacb485b8a3c8e4bd
reg_x26_init:	.dword 0x52a2be452badc478
reg_x27_init:	.dword 0x3af57f3bf364f8f5
reg_x28_init:	.dword 0xffffffffffff8008
reg_x29_init:	.dword 0xd6ed1631fb2167f0
reg_x30_init:	.dword 0x95196f8d288db8ec
reg_x31_init:	.dword 0x0800000000000006

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0xa4f0d65d94f976f7
reg_x1_output:	.dword 0x365b58d8fcf4b274
reg_x2_output:	.dword 0x5f488d533b264d07
reg_x3_output:	.dword 0xc772b180cca4f6d9
reg_x4_output:	.dword 0x6b4164a473d3e297
reg_x5_output:	.dword 0x26f420ae5bd69b95
reg_x6_output:	.dword 0x36759c3694acf5c8
reg_x7_output:	.dword 0x756e573865a4650d
reg_x8_output:	.dword 0x21cbb7dcee398b64
reg_x9_output:	.dword 0x799711f66385b9fb
reg_x10_output:	.dword 0xca9e0ac69fef8745
reg_x11_output:	.dword 0x0875d44ea3910c71
reg_x12_output:	.dword 0x770b06388309e6f7
reg_x13_output:	.dword 0xa8e73811508d4f1e
reg_x14_output:	.dword 0x476f3f7cf1c6829c
reg_x15_output:	.dword 0x6e64e681394eface
reg_x16_output:	.dword 0x39a5611910447810
reg_x17_output:	.dword 0xd12b8eb1e1a16837
reg_x18_output:	.dword 0xbbb77b43533ba44d
reg_x19_output:	.dword 0x81996d19c3c581f1
reg_x20_output:	.dword 0xf6706794e167cf0f
reg_x21_output:	.dword 0x9f353861229b12c6
reg_x22_output:	.dword 0x83f333fb8d086cba
reg_x23_output:	.dword 0x3276877c621a342c
reg_x24_output:	.dword 0x8e69c8f61d801a7b
reg_x25_output:	.dword 0x786604fa5216a10e
reg_x26_output:	.dword 0x663b3efc742d38ae
reg_x27_output:	.dword 0x39bd039df69ef0d2
reg_x28_output:	.dword 0x414d973c6547477f
reg_x29_output:	.dword 0xa191482d2de5fe97
reg_x30_output:	.dword 0xbcddcb8a6c22e9d3
reg_x31_output:	.dword 0x7b131c86adc500be

// Memory Blocks
	.align 8
test_memory:
	.dword 0xd4b469985bf8b268, 0x67b0fffb86c914ac
	.dword 0xac2c2d64e1691f3a, 0x105588d800a742cd
	.dword 0xd2e34ef2c7ba6728, 0xf2a94b3ed81e3edb
	.dword 0xa747773c1572fdd7, 0xaf8bd93fc8fd685f
	.dword 0x57b79065f0bdf1d6, 0x77943022c47ccf78
	.dword 0x76f5e534f3348903, 0xbe9a2705248a41da
	.dword 0x855843bfe87abf2c, 0xf54fb2a6c46ba419
	.dword 0x8ccb176689d28af9, 0xf10a1281d6571b27
	.dword 0x8597ae046ca40d08, 0x83483b1d08a5ca1b
	.dword 0xac2d1c5f39370d59, 0xbd8511a28c4e2833
	.dword 0xf02e75e72bbc6aeb, 0x7fb94cae8d9f331c
	.dword 0xda004b9e928c61a7, 0x51da0e69f0060170
	.dword 0x893aa6564b68ca7d, 0x97de8bd7a23b797f
	.dword 0x1303f01b6ce0b9cc, 0xeda8556db1d03051
	.dword 0x8eac80ee32e52007, 0xb9cf14e6afe8b4eb
	.dword 0x8029c2b9b4745094, 0xb509d456cd5ccbd1
	.dword 0x368b2081c63c92f7, 0x7cfd227fe6905ecc
	.dword 0xbf7234db0974222f, 0x1dd6a8631f8524ed
	.dword 0x933aeb9a71273e60, 0x739404198b1046d1
	.dword 0x5f178acd592334b1, 0x135bfce4050f8325
	.dword 0xce2fd6ed9aaf8177, 0x242e64810b2d976c
	.dword 0xd811c6553ab47093, 0xcda039c0227df0ff
	.dword 0x8cb577ee5d00e017, 0x209ee054a633ea55
	.dword 0x2c3d612bff57092f, 0x228e81efa53a1884
	.dword 0x5db6e73ca702733e, 0xcbc4ec8a6db26d07
	.dword 0xcbaed77f13377547, 0xc8a3820146b02fc1
	.dword 0x42b073313f9ee98e, 0xe5a80ce69e091542
	.dword 0x8bfd026c8376f77e, 0x9bf58e961a2af548
	.dword 0xc13522567cdc17cd, 0xe2535a86d2b7e587
	.dword 0x4b8c428d3b5bb6dd, 0x77b212e2b682bcac
	.dword 0x6db205e7e3241965, 0x652b5a5a66a2419f
	.dword 0x52247a64d13b6750, 0x9f6a4f339cf18b08
	.dword 0x8b595c5c4b6200e5, 0xf7b823a564b85315
	.dword 0x9f5bd8f389e28227, 0x04c96763d69e4379
	.dword 0x305f83d6a0d4187e, 0x381dd67dc9b87db7
	.dword 0x1ea074288f7a0e96, 0xef8dc165a2b0e39f
	.dword 0x58f3bcb4c1b5b286, 0x48bd62517bfae419
	.dword 0x27eab369372dfa35, 0xaedfb3bfb701d021
	.dword 0x769ebc03902289f8, 0x3fb79c5e4a78fc11
	.dword 0xcb628a0c97160180, 0x045f840b05b63126
	.dword 0x54f10e05cad5b2f3, 0xb24ca6387883333c
	.dword 0x258181e09c232857, 0xea84b575325b5edc
	.dword 0x9fab48b2d7a61b37, 0x3d51a446d7d6a378
	.dword 0x607b95a74613c280, 0x3128a73de1535df4
	.dword 0xf1ca0e3443e29aab, 0x1936c4473704d768
	.dword 0x16f8db91adb00c20, 0x2c56833dd4a46c24
	.dword 0x181fdf6960ef93d9, 0x5d5793c6f65f9ef4
	.dword 0x8369ffcaffd15246, 0x5aba7c5e597d9ca4
	.dword 0x1d66be640dc82470, 0x938fa6aae9daf3c6
	.dword 0x46818eefa5f5ab60, 0x7a4a5d19e20284b2
	.dword 0xc8f3a0ec7044e5c1, 0xa24d8dab4a96edcd
	.dword 0x969c10906b623fc4, 0xfb016605c72ff80e
	.dword 0x7475b2fb1b4a3d43, 0xe09e1cd25f03c7be
	.dword 0x5920f1af8c162229, 0x20c97c4616ebd57e
	.dword 0x806b6940e1403d10, 0x5cea01feacd1f38e
	.dword 0xfe263f49410fb82b, 0x6eeba8140291e34b
	.dword 0x3a37639e5c761465, 0xfc5fab66fc203ef9
	.dword 0xf5e130c68ba6b2ca, 0x28a1e33cfa8fbbc2
	.dword 0xb9ff1fab09531026, 0x1e437e112f9a07ff
	.dword 0x3ead828ab7fc96eb, 0xcba437a3c3e1c9b5
	.dword 0x19bd7b31a8772b57, 0xdba05c57f9778161
	.dword 0xd9b5a06a4cc5d5d6, 0x6acb2dbddc8354f8
	.dword 0x6a3306b1812d2fa4, 0xd1127c6cc1920728
	.dword 0xeb85a02ce4ed75b6, 0xb8218b1554239ee4

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
