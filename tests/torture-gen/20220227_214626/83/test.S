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
	addi x26, x0, 0
	addi x2, x0, -997
	addi x13, x0, -755
	addi x22, x0, 0
	addi x3, x0, 1054
	xor x21, x31, x31
	addi x29, x13, -1403
	addi x7, x0, 252
	addi x18, x0, 1457
	mulhsu x19, x8, x8
	la x24, test_memory-596
	xor x28, x30, x30
	addi x9, x0, 222
	xor x10, x28, x28
	addi x8, x7, 1212
	addi x17, x2, -1939
	blt x13, x29, crash_forward
	addi x15, x0, 1
	srlw x5, x17, x17
	lwu x25, 1592(x24)
	bge x17, x2, crash_forward
	sub x14, x9, x9
	addi x11, x0, 684
	addi x24, x21, 0
	la x21, test_memory+1298
	la x7, test_memory+1991
	rem x12, x30, x30
	addi x10, x0, 248
	addw x29, x9, x6
	sll x15, x15, 63
	addw x20, x3, x11
	addi x5, x0, 647
	la x6, test_memory-1883
	sh x31, 1901(x6)
	addi x19, x10, 1554
	addi x4, x0, -1
	la x16, test_memory-810
	xor x4, x4, x15
	lb x1, 1248(x16)
	lw x30, -1282(x21)
	addi x13, x24, 0
	bltu x24, x13, crash_backward
	addi x1, x0, 1398
	bge x10, x19, crash_forward
	and x27, x13, x4
	addi x8, x0, 193
	la x20, test_memory-234
	ld x28, -1311(x7)
	addi x14, x6, 0
	addi x26, x0, -1804
	xor x31, x18, x18
	addi x29, x0, 1276
	lwu x22, 502(x20)
	addi x10, x0, -1415
	divuw x25, x5, x8
	or x23, x27, x15
	sll x12, x29, x29
	addi x3, x0, -721
	addi x13, x0, -380
	addi x11, x0, -1091
	bge x23, x27, crash_backward
	srlw x6, x10, x13
	mulhu x30, x2, x16
	divuw x9, x1, x11
	addi x16, x0, 1044
	divw x2, x3, x3
	la x24, test_memory+1370
	addi x21, x14, 0
	addi x28, x0, 1487
	mulhsu x27, x1, x9
	mulhu x17, x26, x16
	mulhu x31, x6, x25
	and x9, x7, x7
	addi x15, x0, 166
	addi x29, x0, 0
	la x7, test_memory+403
	lw x23, -243(x7)
	bltu x14, x21, crash_forward
	la x9, test_memory+1560
	la x23, test_memory-1424
	addi x26, x21, 0
	ld x19, -818(x24)
	addi x20, x0, 0
	addi x4, x0, 642
	mul x25, x4, x4
	sw x28, -900(x9)
	lw x17, 1424(x23)
	addi x3, x0, 800
	addi x5, x0, 1573
	la x12, test_memory+1151
	rem x2, x28, x3
	addi x30, x0, 1313
	la x24, test_memory-106
	sll x1, x15, x15
	sll x10, x30, x30
	addi x1, x0, 0
	lbu x21, 735(x24)
	addi x4, x0, -1885
	addi x27, x0, 607
	addi x9, x0, 0
	addi x24, x0, 940
	addi x23, x0, 884
	mulhsu x28, x22, x22
	addi x6, x0, -1834
	or x17, x4, x23
	or x22, x6, x6
	addi x30, x0, 722
	sltu x15, x23, x23
	addi x19, x0, 0
	bltu x29, x20, crash_forward
	addi x8, x5, 358
	addi x10, x0, 0
	bne x1, x10, crash_backward
	addi x1, x0, -1378
	mulhu x13, x28, x2
	addi x22, x0, 99
	la x20, test_memory-257
	mulw x18, x1, x1
	addi x31, x26, 0
	addi x29, x0, -1962
	la x10, test_memory+1448
	addi x7, x27, 93
	la x3, test_memory+509
	bne x26, x31, crash_forward
	lbu x2, 240(x3)
	bgeu x5, x8, crash_backward
	lwu x11, -1091(x12)
	addi x14, x0, 1598
	bne x9, x19, crash_backward
	addi x25, x0, 505
	addi x4, x0, -488
	sd x5, -1024(x10)
	addi x17, x0, 890
	divuw x6, x1, x17
	divw x21, x24, x30
	la x13, test_memory+306
	lwu x28, 693(x20)
	addi x15, x22, 55
	la x18, test_memory-964
	sb x27, 1710(x18)
	div x23, x29, x4
	sb x16, 283(x13)
	add x16, x14, x25
	addi x12, x0, 702
	addi x11, x0, -472
	remuw x30, x5, x5
	addi x10, x0, 0
	la x6, test_memory+561
	addi x15, x0, -876
	addi x8, x11, -1147
	addi x28, x0, 1788
	addi x20, x0, -2030
	mulhsu x23, x28, x28
	addi x14, x0, -273
	addi x5, x0, -932
	addi x13, x0, 0
	addi x25, x0, 1
	sh x24, 417(x6)
	addi x9, x0, 259
	or x21, x20, x14
	la x26, test_memory+1660
	rem x22, x12, x9
	add x3, x5, x5
	mulhu x1, x15, x15
	la x17, test_memory-718
	la x31, test_memory-410
	ld x24, 1102(x17)
	la x27, test_memory-588
	sd x30, 514(x31)
	la x16, test_memory+662
	sb x2, 283(x16)
	lbu x4, 1539(x27)
	sll x25, x25, 63
	sb x4, -700(x26)
	addw x21, x14, x14
	addi x13, x3, 315
	addi x7, x0, -1
	xor x7, x7, x25
	lui x16, 485191
	and x19, x2, x7
	la x29, test_memory+1033
	xor x2, x3, x16
	addi x27, x0, -1556
	la x28, test_memory-428
	addi x26, x0, 1
	sll x26, x26, 63
	addi x4, x0, 1823
	or x18, x19, x25
	remu x15, x27, x4
	la x13, test_memory-65
	sltiu x5, x18, 641
	divu x11, x14, x22
	addi x27, x0, 1
	lh x23, 1338(x28)
	addi x31, x0, -1
	lb x3, 92(x13)
	sll x27, x27, 63
	xor x31, x31, x26
	addi x9, x0, -1
	bgeu x19, x18, crash_backward
	la x8, test_memory-576
	addi x30, x0, 1264
	sll x17, x30, x10
	addi x28, x0, -1139
	div x3, x13, x13
	slliw x25, x0, 26
	xor x9, x9, x27
	addi x10, x0, 1
	sll x10, x10, 63
	la x13, test_memory+940
	sw x15, 1212(x8)
	sw x4, -284(x13)
	addi x20, x0, 1726
	addi x5, x0, -1604
	add x1, x30, x20
	addi x23, x0, -1021
	addi x18, x0, 826
	la x7, test_memory-366
	mulhsu x19, x5, x23
	addi x21, x0, -1
	lh x16, 924(x7)
	lb x24, -399(x29)
	and x2, x19, x9
	xor x21, x21, x10
	and x22, x29, x21
	slt x11, x28, x18
	or x4, x2, x27
	and x6, x9, x31
	or x12, x6, x26
	beq x2, x4, crash_forward
	or x14, x22, x10
	blt x22, x14, crash_backward
	ori x22, x27, -320
	la x5, test_memory+1489
	addi x15, x0, 1
	xor x1, x22, x22
	la x26, test_memory+2618
	la x29, test_memory+548
	remw x9, x12, x12
	lbu x27, -525(x5)
	addi x12, x0, -861
	addi x28, x0, -854
	addi x30, x0, 1
	sll x30, x30, 63
	addi x6, x0, 236
	la x1, test_memory-88
	divuw x21, x12, x12
	la x7, test_memory+1726
	la x17, test_memory+1708
	lbu x31, -973(x7)
	sb x2, -1417(x17)
	la x19, test_memory-1430
	lwu x10, 1798(x19)
	la x5, test_memory+2266
	lb x16, -1600(x26)
	addi x3, x6, 2005
	la x7, test_memory+1819
	sh x31, -1469(x7)
	addi x8, x0, -1502
	bltu x3, x6, crash_backward
	la x22, test_memory+1142
	la x12, test_memory+1729
	sll x15, x15, 63
	lbu x9, -822(x22)
	la x13, test_memory-1437
	sub x18, x28, x8
	addi x26, x0, 2023
	addi x3, x0, 656
	lhu x20, 1084(x1)
	sra x28, x26, x26
	la x19, test_memory-1031
	sb x21, 1986(x13)
	addi x27, x0, -688
	addi x17, x0, 253
	srlw x10, x3, x3
	addi x21, x27, -1121
	lbu x11, 3(x29)
	addi x24, x0, -1
	addi x23, x0, -1
	srlw x7, x15, x14
	beq x27, x21, crash_forward
	mulh x18, x17, x17
	lb x31, -1688(x5)
	xor x24, x24, x30
	lwu x16, 2043(x19)
	and x4, x11, x24
	sh x31, -1151(x12)
	addi x16, x0, 1809
	xor x23, x23, x15
	addi x7, x0, -454
	la x10, test_memory+1566
	addi x18, x0, 0
	la x31, test_memory-714
	la x21, test_memory-295
	addi x17, x0, -224
	addi x27, x0, 1
	mulhsu x22, x23, x18
	sll x27, x27, 63
	lhu x26, 1008(x31)
	addi x1, x0, -1
	addi x12, x0, -2037
	ld x13, 959(x21)
	and x14, x24, x23
	sra x22, x9, x9
	sb x25, -730(x10)
	or x25, x9, x30
	addi x19, x7, -575
	mulhsu x11, x17, x12
	or x2, x16, x15
	la x6, test_memory+2223
	la x31, test_memory+66
	addi x3, x0, 0
	xor x1, x1, x27
	la x8, test_memory+2085
	sh x24, 732(x31)
	lw x9, -1831(x6)
	sh x4, -1687(x8)
	and x29, x29, x1
	addi x5, x0, 1286
	divuw x28, x16, x5
	or x20, x29, x27
	bge x20, x29, crash_backward
	la x7, test_memory+1270
	addi x24, x0, 453
	mul x18, x24, x24
	srlw x21, x15, x15
	addi x6, x0, 0
	addi x8, x0, 33
	remu x14, x24, x24
	addi x28, x0, 857
	la x11, test_memory-160
	lhu x27, 702(x11)
	la x19, test_memory-1583
	sll x13, x20, x20
	addi x12, x0, 0
	addi x25, x28, 609
	sh x22, 1875(x19)
	addi x15, x0, 271
	blt x25, x28, crash_forward
	addi x16, x0, -160
	addi x21, x25, 0
	addi x11, x0, 1083
	mulhsu x17, x12, x12
	mulh x20, x8, x15
	la x14, test_memory-897
	addi x29, x0, -20
	addi x24, x0, -1876
	addi x4, x0, -782
	sh x20, -928(x7)
	addi x3, x0, -1192
	divuw x15, x2, x20
	or x10, x16, x3
	addi x30, x24, -1999
	addi x8, x0, 1
	addi x31, x4, -787
	addi x13, x21, 0
	la x28, test_memory-310
	la x9, test_memory+2371
	rem x23, x22, x30
	divuw x18, x26, x30
	la x1, test_memory+2854
	slliw x31, x30, 9
	sll x8, x8, 63
	mulw x2, x29, x29
	la x16, test_memory+1635
	la x24, test_memory-587
	sw x15, 1805(x14)
	lw x26, -1515(x9)
	addi x17, x0, -1
	srlw x30, x14, x14
	addi x25, x0, 24
	addi x5, x0, -1374
	xor x17, x17, x8
	lbu x27, 311(x28)
	and x20, x28, x17
	sw x25, -1998(x1)
	mulhu x19, x11, x25
	addiw x3, x6, -9
	sd x2, 651(x24)
	or x7, x20, x8
	la x10, test_memory-469
	sra x22, x5, x5
	lwu x15, -1627(x16)
	sw x8, 481(x10)
	la x1, test_memory+1523
	la x23, test_memory-1002
	addi x10, x0, 915
	addi x19, x0, -1573
	mulhsu x13, x30, x30
	la x8, test_memory+1542
	sra x24, x15, x7
	la x3, test_memory+1617
	lbu x29, -1259(x3)
	la x28, test_memory-197
	sd x27, 1562(x23)
	lw x16, -1166(x8)
	addi x2, x0, 943
	addw x5, x21, x18
	mulhu x12, x5, x5
	lb x11, -826(x1)
	sd x11, 885(x28)
	addi x25, x0, 1416
	addi x17, x0, 985
	addi x18, x0, 794
	sll x22, x25, x25
	la x4, test_memory+773
	subw x29, x31, x31
	addi x3, x0, -1983
	srl x13, x13, x13
	addi x5, x0, -649
	div x12, x5, x5
	add x27, x19, x18
	addi x8, x9, 0
	remw x20, x10, x10
	addi x1, x0, 731
	sraiw x14, x27, 26
	lh x26, -481(x4)
	slt x11, x14, x14
	addi x15, x0, -1319
	addi x14, x0, 1
	addi x9, x0, -2024
	and x23, x3, x15
	xor x5, x18, x18
	bltu x0, x0, crash_forward
	divw x7, x12, x12
	sll x14, x14, 63
	addi x6, x0, -538
	la x27, test_memory+1667
	la x19, test_memory+2135
	sb x31, -1251(x19)
	addi x16, x0, 603
	addi x21, x17, 1619
	la x20, test_memory-1394
	lw x10, -1355(x27)
	addi x28, x8, 0
	addi x22, x0, -404
	subw x30, x2, x6
	addi x12, x0, -1
	remuw x24, x1, x1
	xor x31, x9, x9
	rem x25, x16, x22
	xor x12, x12, x14
	sh x12, 1868(x20)
	and x29, x22, x12
	or x26, x29, x14
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
	sd x5, 40(x1)
	sd x6, 48(x1)
	sd x7, 56(x1)
	sd x8, 64(x1)
	sd x9, 72(x1)
	sd x10, 80(x1)
	sd x11, 88(x1)
	sd x12, 96(x1)
	sd x13, 104(x1)
	sd x14, 112(x1)
	sd x15, 120(x1)
	sd x16, 128(x1)
	sd x17, 136(x1)
	sd x18, 144(x1)
	sd x21, 168(x1)
	sd x22, 176(x1)
	sd x23, 184(x1)
	sd x24, 192(x1)
	sd x25, 200(x1)
	sd x26, 208(x1)
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
reg_x0_init:	.dword 0x0000000000000009
reg_x1_init:	.dword 0xffffffffffffff85
reg_x2_init:	.dword 0x193f83b741c76004
reg_x3_init:	.dword 0xc540aaeec31b62c4
reg_x4_init:	.dword 0xffffffffffffffff
reg_x5_init:	.dword 0x003aee387f64359f
reg_x6_init:	.dword 0x3b444bb78ca16e6a
reg_x7_init:	.dword 0x6ef5b62dccade378
reg_x8_init:	.dword 0x89653091434567bf
reg_x9_init:	.dword 0xca23f708a53db000
reg_x10_init:	.dword 0xbdfc9c60e383bc73
reg_x11_init:	.dword 0x664ffa7119692183
reg_x12_init:	.dword 0xffffffffffff8002
reg_x13_init:	.dword 0x14fa71c1c4a89fce
reg_x14_init:	.dword 0xffffffffffff8008
reg_x15_init:	.dword 0x26f49c4306dacbfc
reg_x16_init:	.dword 0x5890a99c1e427235
reg_x17_init:	.dword 0xffffffffffff8003
reg_x18_init:	.dword 0x4474078ced8ad001
reg_x19_init:	.dword 0x0000000000000000
reg_x20_init:	.dword 0x63c26b1ada64b628
reg_x21_init:	.dword 0xffffffffffffffff
reg_x22_init:	.dword 0x544ab8fb118288d3
reg_x23_init:	.dword 0x0000000000000020
reg_x24_init:	.dword 0x9b6260d5986666b8
reg_x25_init:	.dword 0xfd0edcb33d717cdb
reg_x26_init:	.dword 0xffffffffffffff86
reg_x27_init:	.dword 0xffffffff80000002
reg_x28_init:	.dword 0x4e63e40d1ccddd7b
reg_x29_init:	.dword 0xffffffffffff8001
reg_x30_init:	.dword 0xffffffffffff8003
reg_x31_init:	.dword 0xffffffff80000000

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0x3614e96c596d619c
reg_x1_output:	.dword 0xb50b00e07c3a08e6
reg_x2_output:	.dword 0xf3ff423cff731ec1
reg_x3_output:	.dword 0x8fa5d7db2d3a603d
reg_x4_output:	.dword 0xa3f6a964558c6acf
reg_x5_output:	.dword 0x608317e19db54bca
reg_x6_output:	.dword 0x8fa48d9013f638c3
reg_x7_output:	.dword 0x1ebf9b782f4dd630
reg_x8_output:	.dword 0x365f4220b25bb405
reg_x9_output:	.dword 0xaf88b7e1f2e85423
reg_x10_output:	.dword 0x7902d6931bac34ca
reg_x11_output:	.dword 0xb5f723b0bc778972
reg_x12_output:	.dword 0xef3b7133823196b9
reg_x13_output:	.dword 0x0999329fcd089a46
reg_x14_output:	.dword 0x6c0e211cdf62d5d0
reg_x15_output:	.dword 0xb6447a9e9fc64cab
reg_x16_output:	.dword 0x12c85b5e8c491589
reg_x17_output:	.dword 0x70b4362f5b305e50
reg_x18_output:	.dword 0x4b4d977ad40b7638
reg_x19_output:	.dword 0x0dfaf7efb84bf28a
reg_x20_output:	.dword 0x983dbf17bc985cb6
reg_x21_output:	.dword 0x4d2383781a5e5c9e
reg_x22_output:	.dword 0xf1e664eeb7a91043
reg_x23_output:	.dword 0xbbc5df64d313ca3f
reg_x24_output:	.dword 0x319bf708dac6d2a8
reg_x25_output:	.dword 0x9d12f4b4ad079255
reg_x26_output:	.dword 0x1937602c5dc6d69c
reg_x27_output:	.dword 0x002a4f5459bc2bff
reg_x28_output:	.dword 0x1d47cc91d6a4b868
reg_x29_output:	.dword 0xf3b2d3f6146d11db
reg_x30_output:	.dword 0xc54f85dc3df95ccd
reg_x31_output:	.dword 0x6ae87f2601051584

// Memory Blocks
	.align 8
test_memory:
	.dword 0xdf5e1a45a2c65a25, 0xb0de819e9a27e75c
	.dword 0x0ac9431a652c4fc7, 0x82d64dd9fae5d68a
	.dword 0x13e93e694824cfb0, 0x3f816ae8549d0d46
	.dword 0x07d48ff900bebe5e, 0x400d20814ffbcd53
	.dword 0xc6625d7897e64cff, 0xf634505c154b70cd
	.dword 0x9979d9fad8aff1cb, 0xf18510bfec643324
	.dword 0x1e2874a1a2b002ad, 0x6accdc59bc260668
	.dword 0xad5fbe99b45ed628, 0x70776b509c52f8c6
	.dword 0xbad73c47e7238e78, 0xa6d989975f6bee52
	.dword 0x0f9d95c1d39df2f7, 0xb5227e81acf8b306
	.dword 0xcea7da80fb69fbc2, 0xb043d99a73b0a90a
	.dword 0x3b64cc555c1df39c, 0xf9c8b8b426899735
	.dword 0xe04565984fee5412, 0x4692db3f24065bd3
	.dword 0x048b0ea5d970bfde, 0x9a0516dc9c7787a8
	.dword 0x20bf368b8ba9bf90, 0x8a880135567c2535
	.dword 0xe73f42fdb427246a, 0xc5cee30761313039
	.dword 0x6d830b8deca3358c, 0x831048806d62817a
	.dword 0x6a73541ad2cb0b50, 0xf0c6c2ce82f832c4
	.dword 0x6988fa870984bcf7, 0x17c3aef6b207bf31
	.dword 0x48c4cbac6db84484, 0x9fa715e657a063ab
	.dword 0x941b338f4b683ce8, 0x266cf9c779de83af
	.dword 0x02ee3cd67d15de5e, 0xd6f1a492854a1653
	.dword 0xe6e39377793ddd18, 0xce53cbed83405f89
	.dword 0x160b7eb20e720e1b, 0xf7349e30666979a5
	.dword 0x5029063fb86df666, 0xe9430cc0bb3e731c
	.dword 0x4f3ab6cc3dc2a859, 0x4480e7a95fad048e
	.dword 0x5166b9a278989355, 0xef859e659a322305
	.dword 0x9d6433a583cc299f, 0xafebba003e94f27f
	.dword 0x25a71f85da948089, 0x3153645a88ffdca9
	.dword 0x513317328a314ed3, 0xbb3590caffcdcfed
	.dword 0x164cc08c450fed4e, 0x656899ed4d3deaae
	.dword 0xf288d15bbbad3dc2, 0x77f068b46ca016d2
	.dword 0x1032de8603749c11, 0x09c178c24eb15980
	.dword 0xb1f56a7e553a3d9b, 0xb4bf4df7d706db2a
	.dword 0x1e4fe6fafdf1a2e4, 0xf8b42f4fa4d2ebcd
	.dword 0x03fe9de9d326ff74, 0x64893ae8dc3f8777
	.dword 0x2a43b5a4d3ccbbfe, 0xe1e327633f4e1f09
	.dword 0x233fc464335c76c4, 0x2cb9466c7de4a93e
	.dword 0x467ba6f2e35d2639, 0x0bc19c9b28ac3feb
	.dword 0x0dac8ea4ac5641e7, 0xd0e6227c11e5cd88
	.dword 0xd0d67a8815521593, 0xdfa482ead69d8eee
	.dword 0x10808fd9268fa29e, 0xe37aeaa481ee6d62
	.dword 0xeff205b99326b3ad, 0x4799bd1ab79274d1
	.dword 0x1da59821fc67068c, 0xbc3b4289130dea5d
	.dword 0x488cb613eae5b04f, 0xd27fa346b196c718
	.dword 0xf49adf1342ba1fba, 0x36bcc45f76b29b0e
	.dword 0x4ba4e3d3849e61e2, 0xe816d95f12a11c88
	.dword 0xa026fe3522bc8d13, 0x242fbf6f3649e78f
	.dword 0x293ff46db82d75f4, 0x140875a486c831af
	.dword 0xe95ebb849bcb12e9, 0xad114696a31775fc
	.dword 0x47034d07443b31b8, 0x941a773105105d5a
	.dword 0x27caa3f45a3d636e, 0x18a08ec9541566f8
	.dword 0x150914fa61914283, 0xe30c8c7047c3151c
	.dword 0x45b575e62e78773c, 0x91319d8ae3efa225
	.dword 0x3e9ac857302a1e50, 0xeed729a1518281ce
	.dword 0xe6ed5bb415c375ce, 0x85b74775116c32af
	.dword 0x7fbb9a5ec59bf43d, 0x0646ef56b48b2409
	.dword 0x5f81f629b4a12e04, 0x3a1e7eb59cd2b3c2
	.dword 0xdbaca808b6c12d0c, 0x4f2e60f9cdd588ae
	.dword 0x8f49370898b01ea3, 0xf154f1903d24cd0f
	.dword 0x8bd4fa8090c07ba3, 0xc3a7eb45ea0a0d5f
	.dword 0xc6350b8596530ed3, 0xdd14f8d7d039bf4c
	.dword 0xc1b759a357d67d8c, 0x4a223ac95678b503
	.dword 0x8cc3d6c91ca4369f, 0xa8d0d677790f00b1

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
