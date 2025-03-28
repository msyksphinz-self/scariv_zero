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
	addi x22, x0, 0
	addi x30, x0, -991
	addi x6, x0, -760
	addi x17, x0, 1519
	slli x19, x22, 58
	addw x23, x3, x17
	addi x24, x0, -1886
	addiw x18, x9, 972
	addi x10, x17, 952
	addi x19, x0, 389
	addi x14, x0, -309
	addi x29, x31, -1868
	addi x1, x0, -314
	addi x7, x0, -1821
	remu x4, x24, x14
	div x15, x30, x6
	subw x5, x29, x24
	la x12, test_memory+1042
	divu x25, x19, x19
	remw x31, x31, x31
	bltu x4, x4, crash_forward
	or x27, x1, x7
	la x13, test_memory+1128
	sh x27, -580(x13)
	la x31, test_memory+2399
	la x11, test_memory+444
	addi x9, x0, 519
	sra x28, x9, x9
	sh x16, 462(x11)
	la x21, test_memory+1405
	lbu x6, -1872(x31)
	slt x18, x19, x19
	addi x25, x0, -487
	addi x27, x0, 524
	addi x20, x0, 0
	remuw x26, x24, x24
	addi x4, x0, 1523
	lwu x3, -474(x12)
	la x30, test_memory+1841
	la x23, test_memory-838
	sb x14, -833(x21)
	addi x1, x0, -1356
	remw x5, x25, x27
	addi x2, x0, 969
	lb x15, -906(x30)
	bge x17, x10, crash_forward
	sll x14, x4, x1
	sh x19, 1770(x23)
	addi x8, x0, 1339
	sraw x16, x2, x8
	addi x2, x0, 0
	la x15, test_memory+1216
	addw x18, x9, x19
	lhu x19, -212(x15)
	la x31, test_memory+2189
	divuw x18, x6, x18
	addi x21, x0, 133
	la x13, test_memory-426
	la x5, test_memory+1098
	sllw x9, x5, x18
	addi x27, x0, 0
	bltu x0, x0, crash_backward
	slt x20, x1, x7
	mulw x19, x21, x8
	subw x11, x6, x6
	addi x30, x0, -25
	sraw x24, x23, x14
	addi x29, x0, 1939
	addi x23, x0, 839
	lw x26, -1645(x31)
	lb x7, -870(x5)
	la x8, test_memory+1863
	add x27, x12, x3
	addi x16, x0, -1999
	addi x6, x0, 1843
	rem x20, x14, x14
	remw x5, x2, x21
	addi x24, x0, 1
	addi x7, x0, -1552
	addi x14, x21, 125
	addi x31, x7, -1060
	la x28, test_memory-1414
	add x25, x16, x6
	sd x29, -1287(x8)
	addi x1, x0, -1066
	divu x15, x30, x30
	addw x22, x13, x13
	blt x0, x0, crash_forward
	sll x24, x24, 63
	la x20, test_memory+201
	addi x4, x0, -1130
	mulhsu x10, x29, x23
	blt x14, x21, crash_forward
	addi x27, x0, 1599
	divw x26, x1, x27
	sd x29, 119(x20)
	addi x9, x0, -1
	xor x9, x9, x24
	divw x3, x4, x4
	la x17, test_memory-1306
	sd x10, 1430(x28)
	sb x26, 1352(x17)
	la x2, test_memory+2336
	ld x12, 466(x13)
	and x19, x14, x9
	or x11, x19, x24
	lh x18, -1316(x2)
	bge x11, x19, crash_forward
	la x10, test_memory-82
	addi x28, x0, 1
	la x27, test_memory+590
	addi x1, x0, -1017
	addi x30, x0, -823
	sll x28, x28, 63
	addi x24, x0, -324
	la x26, test_memory+423
	addi x3, x0, -669
	addi x17, x0, 1944
	addi x22, x0, -1
	xor x22, x22, x28
	addi x4, x0, 0
	mulhsu x16, x3, x17
	addi x5, x0, -922
	and x25, x26, x22
	addi x14, x0, 229
	sraw x8, x1, x1
	addi x20, x0, 0
	addi x18, x0, 1190
	addi x19, x0, -1456
	addi x6, x14, 1436
	lwu x23, 770(x10)
	mulhu x8, x8, x18
	or x15, x25, x28
	sllw x2, x18, x18
	srl x9, x19, x19
	addi x3, x0, 399
	remuw x31, x3, x3
	bgeu x14, x6, crash_backward
	la x2, test_memory-448
	bltu x4, x20, crash_forward
	addi x29, x0, 1475
	beq x25, x15, crash_backward
	lh x12, -411(x26)
	addi x13, x24, -141
	div x21, x1, x1
	la x9, test_memory+706
	rem x17, x13, x15
	mulhsu x8, x16, x16
	sw x1, 98(x27)
	or x11, x30, x5
	addi x16, x0, 1429
	subw x10, x8, x8
	la x22, test_memory+2578
	bgeu x13, x24, crash_forward
	blt x27, x27, crash_backward
	addi x18, x0, -55
	and x7, x29, x16
	la x12, test_memory+2922
	remu x4, x18, x18
	sw x7, -2018(x12)
	lb x28, -1674(x22)
	addi x24, x0, 1
	addi x27, x0, -461
	addi x20, x29, 1320
	sb x29, -152(x9)
	addi x25, x0, 1
	sll x25, x25, 63
	sltiu x30, x1, 489
	addi x31, x17, 0
	addi x1, x31, 0
	sub x21, x27, x27
	addi x18, x0, 303
	lw x19, 764(x2)
	addi x14, x0, 1
	addi x3, x0, -1
	sll x14, x14, 63
	addi x29, x0, 0
	la x23, test_memory+1199
	xor x3, x3, x25
	addi x5, x0, -1
	addi x30, x0, -483
	sub x4, x18, x30
	slti x2, x29, -681
	addi x20, x0, 1
	sll x24, x24, 63
	sll x20, x20, 63
	addi x30, x0, 158
	addi x21, x0, 0
	addi x4, x0, 1027
	addi x26, x0, -1
	and x11, x18, x3
	or x8, x11, x25
	xor x26, x26, x24
	xor x5, x5, x14
	add x19, x30, x4
	addi x9, x0, 1
	lwu x15, -863(x23)
	and x13, x22, x26
	addi x1, x27, 0
	or x10, x3, x24
	and x6, x9, x5
	la x18, test_memory-723
	sltu x25, x30, x30
	sll x9, x9, 63
	or x17, x14, x14
	lhu x30, 1097(x18)
	addi x15, x0, 474
	addi x28, x0, -1
	xor x28, x28, x9
	la x23, test_memory-1435
	and x27, x0, x28
	addi x22, x0, -1
	or x16, x27, x9
	la x25, test_memory+1292
	sw x8, 1847(x23)
	lbu x3, -793(x25)
	bltu x17, x6, crash_backward
	addi x31, x1, 0
	addi x4, x0, 1280
	la x19, test_memory+404
	la x14, test_memory+516
	sltu x17, x19, x19
	mulhsu x24, x0, x0
	xor x22, x22, x20
	addi x2, x0, -1232
	addw x28, x1, x24
	addi x10, x0, 1
	mulh x8, x4, x2
	addi x27, x0, 1370
	or x30, x25, x4
	la x3, test_memory+2072
	sb x30, -176(x19)
	la x16, test_memory-842
	addi x25, x0, -848
	and x7, x22, x22
	mul x5, x27, x25
	addi x30, x0, -42
	mulh x11, x15, x15
	mulw x27, x30, x30
	lh x13, 1670(x16)
	or x12, x7, x20
	la x9, test_memory+1040
	lh x6, 52(x14)
	sll x10, x10, 63
	sll x1, x8, x16
	remw x28, x22, x22
	la x17, test_memory+998
	lh x4, -304(x17)
	lbu x29, -1649(x3)
	addi x2, x0, 1
	addi x30, x0, 1104
	blt x7, x12, crash_forward
	and x14, x0, x27
	la x19, test_memory+2641
	lhu x8, -1809(x19)
	addi x11, x0, 1
	addi x1, x0, 0
	sll x11, x11, 63
	addi x6, x0, -1
	addi x25, x0, 198
	addi x18, x0, -1
	la x4, test_memory+2471
	addi x13, x0, 0
	xor x18, x18, x10
	ld x27, -1487(x4)
	addi x21, x25, 1567
	sll x2, x2, 63
	addi x31, x0, -1
	xor x31, x31, x2
	and x24, x31, x31
	or x5, x30, x2
	sb x2, -620(x9)
	addi x28, x0, 1794
	bltu x5, x24, crash_backward
	srl x17, x30, x28
	addi x14, x0, 326
	la x7, test_memory+2348
	lw x27, -1724(x7)
	la x22, test_memory-1396
	and x23, x25, x18
	lwu x4, 1544(x22)
	or x26, x23, x10
	addi x8, x0, -33
	sll x20, x14, x14
	xor x6, x6, x11
	addi x9, x0, -239
	slt x12, x29, x18
	la x20, test_memory+1635
	addi x5, x0, -1791
	la x14, test_memory+1921
	and x16, x17, x6
	divw x26, x13, x13
	addi x25, x0, 1353
	divu x2, x18, x26
	la x21, test_memory+577
	lh x4, -1519(x20)
	sraw x24, x27, x27
	or x19, x8, x8
	la x22, test_memory-192
	la x31, test_memory+1009
	subw x13, x11, x11
	la x23, test_memory+744
	lb x3, 462(x22)
	la x30, test_memory-1703
	divuw x17, x5, x5
	addi x10, x0, 1498
	addi x1, x10, 592
	addi x4, x0, 1738
	mulhsu x7, x25, x25
	sd x1, -480(x23)
	lbu x18, -414(x21)
	addi x8, x0, 0
	sw x2, 1863(x30)
	addi x13, x0, 0
	addi x2, x0, -1035
	addi x28, x9, -1651
	sw x0, -441(x31)
	la x30, test_memory+607
	addi x22, x0, 393
	addi x12, x31, 0
	sll x29, x5, x5
	addi x26, x2, -50
	bltu x2, x26, crash_backward
	bltu x8, x13, crash_forward
	addi x26, x0, 1843
	la x10, test_memory-947
	or x8, x17, x0
	or x15, x16, x11
	la x18, test_memory+1913
	lhu x27, -1347(x14)
	lwu x17, -247(x30)
	la x21, test_memory+919
	mulhu x24, x1, x21
	bge x28, x9, crash_backward
	addi x20, x4, 41
	la x13, test_memory+2207
	blt x21, x21, crash_backward
	addi x3, x0, 1377
	sb x29, -1602(x18)
	addi x19, x12, 0
	bltu x12, x19, crash_backward
	la x2, test_memory+1736
	div x7, x22, x3
	lw x23, -251(x21)
	addi x1, x0, -704
	lhu x29, 1165(x10)
	la x22, test_memory+1587
	or x25, x26, x1
	mulhsu x15, x9, x9
	lwu x30, -687(x22)
	addi x31, x0, 1793
	srlw x23, x0, x26
	mulhsu x29, x9, x9
	sd x17, -1424(x2)
	remu x14, x23, x23
	addi x4, x0, 1977
	la x26, test_memory+818
	la x8, test_memory+2187
	la x25, test_memory+517
	lb x29, 56(x25)
	la x6, test_memory+1290
	la x30, test_memory-1057
	addi x22, x0, 746
	addi x21, x0, -36
	divuw x23, x22, x22
	la x1, test_memory-904
	la x3, test_memory+1817
	addi x28, x0, 1430
	addi x27, x0, 0
	sw x0, -1219(x8)
	or x11, x23, x15
	addi x15, x0, 0
	sw x19, 150(x26)
	addi x19, x0, 319
	rem x10, x31, x28
	lb x20, -596(x6)
	lwu x17, 1472(x1)
	sraw x12, x4, x19
	lhu x5, -1895(x13)
	remw x7, x21, x21
	addi x23, x0, 1337
	la x6, test_memory+1908
	or x21, x30, x29
	sh x9, 1399(x30)
	add x2, x1, x24
	sllw x25, x17, x17
	sh x22, -992(x6)
	la x26, test_memory+15
	addi x18, x0, -124
	addi x29, x0, -265
	addi x12, x0, -311
	mul x20, x24, x10
	addi x30, x0, -1429
	srl x9, x18, x18
	addi x11, x0, -915
	subw x5, x23, x23
	la x31, test_memory+1916
	lh x28, -1240(x31)
	addi x6, x0, 764
	addi x17, x0, 1091
	sra x21, x30, x11
	lh x16, -1291(x3)
	addi x7, x0, -164
	lhu x19, 689(x26)
	addi x22, x0, 1612
	addi x25, x0, -1239
	addi x24, x24, -1100
	sraw x2, x6, x25
	addi x24, x0, 1
	addi x20, x0, -1791
	addi x18, x0, 1
	sub x13, x29, x7
	mulw x2, x31, x31
	sll x24, x24, 63
	addi x4, x0, -1152
	sraw x14, x17, x22
	addi x1, x0, -407
	divu x10, x4, x1
	mulhu x15, x2, x2
	sll x18, x18, 63
	addi x30, x0, 16
	divw x25, x30, x30
	addi x28, x0, 614
	mul x8, x12, x12
	addi x26, x0, -1
	srai x9, x27, 49
	xor x26, x26, x18
	mulhsu x6, x20, x28
	and x16, x26, x26
	addi x19, x0, -1
	addi x31, x0, 344
	addi x11, x0, -953
	or x21, x3, x18
	xor x19, x19, x24
	remuw x3, x31, x11
	and x23, x31, x19
	or x27, x23, x24
	blt x23, x27, crash_forward
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
	sd x11, 88(x1)
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
	sd x24, 192(x1)
	sd x25, 200(x1)
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
reg_x0_init:	.dword 0x0799598d09110cf7
reg_x1_init:	.dword 0x25ebd32106b995bf
reg_x2_init:	.dword 0x0000000000000000
reg_x3_init:	.dword 0xb93c7356196be301
reg_x4_init:	.dword 0x31a9e6da6f80e13f
reg_x5_init:	.dword 0xfffffffffffffffb
reg_x6_init:	.dword 0xffffffffffffff86
reg_x7_init:	.dword 0xffffffffffffffff
reg_x8_init:	.dword 0x0000000000000000
reg_x9_init:	.dword 0x71d5cef5abe9b046
reg_x10_init:	.dword 0xb35ef824199dfa47
reg_x11_init:	.dword 0x3371229f42db52f2
reg_x12_init:	.dword 0x3e59b62e97c15d46
reg_x13_init:	.dword 0x0000000000000000
reg_x14_init:	.dword 0xb303d781a326af80
reg_x15_init:	.dword 0xd52eb9db41c35bf0
reg_x16_init:	.dword 0xaa5a74e302d5a8a4
reg_x17_init:	.dword 0x0000000000000000
reg_x18_init:	.dword 0xfffffffffffffffe
reg_x19_init:	.dword 0x2c2247acdfb71962
reg_x20_init:	.dword 0xffffffffffffffff
reg_x21_init:	.dword 0xffffffffffffffff
reg_x22_init:	.dword 0x24d8d4cff99efb45
reg_x23_init:	.dword 0xffffffffffffff89
reg_x24_init:	.dword 0xffffffffffffffff
reg_x25_init:	.dword 0xffffffffffffff82
reg_x26_init:	.dword 0xee979a3e00ff1445
reg_x27_init:	.dword 0x46c18c8710933a83
reg_x28_init:	.dword 0x0000000000000000
reg_x29_init:	.dword 0xffffffff80000000
reg_x30_init:	.dword 0x0000000000000000
reg_x31_init:	.dword 0x5abf16a8586143d4

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0x641462776032b70b
reg_x1_output:	.dword 0x48c25275028f7e82
reg_x2_output:	.dword 0x72063b27a2015542
reg_x3_output:	.dword 0x0765c4d93e196435
reg_x4_output:	.dword 0x922035f9449c388c
reg_x5_output:	.dword 0x61e1d9ad02dcded6
reg_x6_output:	.dword 0xf7564f3e9875b2a9
reg_x7_output:	.dword 0x5aa1ce73c15e64bd
reg_x8_output:	.dword 0x9e8552db033d4268
reg_x9_output:	.dword 0xb70190870b7494d6
reg_x10_output:	.dword 0xde389ede8b22cb7d
reg_x11_output:	.dword 0xfe84fa5d52886494
reg_x12_output:	.dword 0x0636ec772c74f798
reg_x13_output:	.dword 0x10ef210bacd5b925
reg_x14_output:	.dword 0xb99843064a9c14b2
reg_x15_output:	.dword 0x7242760f687fdfe7
reg_x16_output:	.dword 0x95a5798e8bb404a9
reg_x17_output:	.dword 0x4cfac14908909a19
reg_x18_output:	.dword 0xf0e3ea55871d120f
reg_x19_output:	.dword 0xf05e374a662fafd5
reg_x20_output:	.dword 0xfeb63cc63c84be3e
reg_x21_output:	.dword 0xbad32fd032cc3e3e
reg_x22_output:	.dword 0x87256994f764dcaf
reg_x23_output:	.dword 0x32fc408e8dd034f5
reg_x24_output:	.dword 0x25f35d2554088f8b
reg_x25_output:	.dword 0xd634c0340d09b6d0
reg_x26_output:	.dword 0xca4adc2ca40bf982
reg_x27_output:	.dword 0x6423f5a6b17d51cd
reg_x28_output:	.dword 0xff768e981a44b8dc
reg_x29_output:	.dword 0x3dbd7790360f4244
reg_x30_output:	.dword 0x894354ad6e4e7fcd
reg_x31_output:	.dword 0x9e69801cd1a1355c

// Memory Blocks
	.align 8
test_memory:
	.dword 0xa2504a6f1fd85e0c, 0xe07839017e253ebf
	.dword 0xe1d11d460e848fa6, 0xbeaf43bea0fdf591
	.dword 0x8f6d97ddb5f5e50e, 0x3bf102274a0eec9d
	.dword 0x3133884e53c31879, 0xebf16321555ff9d1
	.dword 0x073e647d6fb9a468, 0x2ce437a9726900ec
	.dword 0x350a50c0635eef86, 0x264d541943433575
	.dword 0xaf9e6cc85d37e1b3, 0x44db01ae785807ee
	.dword 0xf4148abb144c3660, 0x62b7844381f53249
	.dword 0xb9c2b49ea1dc201d, 0xcf46b8645bb0979b
	.dword 0x98ad23ff4794116f, 0x35110d803cfdeb0f
	.dword 0x2e2d8fc7e0f3bee6, 0xb0ed607bfa03521c
	.dword 0x0126f4734c5aae6f, 0xce8f7a7066d975fa
	.dword 0x02eb3a67bc7de7e6, 0x14b937aba136b851
	.dword 0x6c6a5ea0f32f9aef, 0x22a89afc384c7f33
	.dword 0x2699018e4b9ace06, 0x693d512c6b98cc4c
	.dword 0x53768037f1a26ad3, 0x58f468ce46dd9358
	.dword 0xb8f8fba7ff343bc2, 0x8a81423a0e9283d4
	.dword 0x32a7f2889c55aed3, 0x4eb6fbd5043d39f8
	.dword 0x4014510be4b971ae, 0x13e5de9600670ae3
	.dword 0xbfe71b0acb0a3afa, 0xcf048ec627a6e018
	.dword 0xc72e1470980854ee, 0xbe3505063ca8d629
	.dword 0xcd200bd7ef5cbd27, 0x54b19395d98492b1
	.dword 0x7b08ab737eddedbc, 0x5e2e7bd37a4e8586
	.dword 0xe0a5f42d042fa38f, 0x9d80d80178df892f
	.dword 0x853fc712196835e5, 0x9023dd4a59919693
	.dword 0x5f6420ee00fb5339, 0x1241ba0779677ff3
	.dword 0x9eb8ec334cd3374c, 0x5d75943ceb00e71a
	.dword 0xfefe8d1ee97eae80, 0x0bd06c69281ae2d2
	.dword 0x0f6c8c1d8deb7a66, 0x3102e87ff471079a
	.dword 0x1844026c6789eb95, 0x492a4b301bd9c795
	.dword 0x9809acfdbb2fc4bd, 0x3fdf1b6b83b45dc4
	.dword 0x5c93c9a219ddbafb, 0x7f084026b66db877
	.dword 0x1036226446ec276e, 0x23dd945db2451700
	.dword 0x6318eb346858be09, 0xc5b1375c61d04eaa
	.dword 0x5a6d55c50b385daa, 0xc5c71d38f84aeae9
	.dword 0x7cfcffb6baed4d6b, 0xcdf6a3a324ba9cd2
	.dword 0xacbf9ef6c2f37b38, 0xdd4a2ee010a6adcd
	.dword 0x41f4906666198fa2, 0x328d1312c0c76988
	.dword 0x13f42cb7ac16eaf1, 0x3cf84dbd3aedb32e
	.dword 0x50c7079e7cdbdf7f, 0xef32d385cbb239d8
	.dword 0x84cf7d2748fabd43, 0xd8e2763c9b7f0043
	.dword 0xd1b43162fd5d82ac, 0x0356a71d1c7d2bc3
	.dword 0xc58066488f6546b0, 0xf6a69951951c4e78
	.dword 0x62d94bda7acdb023, 0x8a3088ba7487a0be
	.dword 0xf775ae8515800e4c, 0x3e0028ef3ab0dde9
	.dword 0x38f7a7cd7c26e6b4, 0x1e7e808483dfb832
	.dword 0x901e3527f60c0c41, 0x712db490633017eb
	.dword 0x693ed92a44d89384, 0x34578868475899fa
	.dword 0x1d55aae3366f384e, 0x6cbd95af7cb60184
	.dword 0x82fc7783a18f0889, 0x2fc68093462f90e7
	.dword 0x487fda4872756844, 0xae93ac4ff7537dee
	.dword 0xda536e90a093c30f, 0x631f33f86449f53f
	.dword 0x2994805072de7e88, 0x0c3a2b7603306118
	.dword 0x275cdea9d2800236, 0xcc3f6ccfd555e73a
	.dword 0x219db4d81d13e895, 0x70cf75ab68ed5224
	.dword 0x67548d4dcd3bad71, 0x5c2e19143c57d984
	.dword 0x226ae31ddb9f6d77, 0x7323097c766f7dea
	.dword 0x3fb2e59f30828b08, 0xd0ca7f042a6eebbe
	.dword 0x7f7a5249383d4c50, 0x54d37dfb55801974
	.dword 0x7d5688e35869c697, 0xac7d81a3feda14fd
	.dword 0x225b3ddee1a3aad6, 0x837f8f3ba4e9b480
	.dword 0xac1f6f043f9fc78d, 0xa41ef539a1881e4a
	.dword 0x430a7e4cc05953d3, 0x055c3ad7d7fd5c02
	.dword 0x2d9d9710d06057ae, 0xef8103d1b0bc6d20

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
