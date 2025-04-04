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
	la x23, test_memory-617
	addi x21, x0, -1051
	addi x13, x0, -1305
	sraiw x2, x17, 15
	lhu x4, 1027(x23)
	mulh x29, x13, x13
	xor x18, x7, x7
	sub x26, x2, x2
	srliw x28, x23, 8
	sub x22, x16, x1
	add x25, x29, x29
	sra x12, x27, x6
	addi x24, x0, -1137
	addi x10, x21, -1292
	addi x31, x25, 0
	la x22, test_memory+2716
	sraw x1, x23, x23
	slliw x6, x13, 2
	la x23, test_memory-1353
	la x27, test_memory+1584
	blt x21, x10, crash_forward
	addi x7, x0, 1544
	addi x26, x0, 419
	or x9, x30, x30
	remw x16, x9, x18
	addi x4, x0, -1065
	srl x5, x18, x18
	addi x17, x0, -351
	addi x12, x0, 81
	xori x14, x10, 1333
	addi x8, x31, 0
	mulw x18, x4, x4
	divuw x28, x26, x12
	addi x26, x0, -1333
	or x16, x4, x11
	srliw x30, x23, 21
	rem x3, x17, x17
	mulhu x5, x24, x24
	addi x11, x7, 398
	srli x13, x28, 36
	addi x20, x0, -927
	mulhsu x15, x25, x31
	addi x14, x0, -268
	srl x19, x24, x20
	la x20, test_memory-516
	sd x2, 1212(x20)
	addi x9, x0, -131
	bne x31, x8, crash_forward
	addi x18, x0, 21
	la x7, test_memory+1935
	divuw x3, x27, x8
	sll x13, x28, x18
	addi x10, x0, -466
	addi x1, x0, 341
	addw x12, x4, x26
	addi x5, x0, -1325
	mul x21, x14, x14
	addi x8, x0, 1983
	div x13, x2, x16
	mulhsu x4, x9, x18
	lh x25, -1810(x22)
	and x6, x10, x1
	addi x12, x0, 631
	addi x11, x0, 321
	la x29, test_memory+1963
	addi x15, x5, -195
	div x16, x27, x27
	addi x10, x0, -1985
	sllw x24, x11, x27
	srai x14, x10, 44
	la x1, test_memory+443
	bgeu x15, x5, crash_forward
	addi x21, x0, -119
	addi x19, x0, -1099
	la x13, test_memory+1140
	lh x4, 21(x1)
	addi x28, x26, -15
	la x22, test_memory-1401
	addi x18, x0, -1823
	sh x3, -1037(x7)
	la x4, test_memory+1042
	lbu x16, -1053(x13)
	blt x26, x28, crash_backward
	sw x12, -1943(x29)
	divuw x3, x8, x12
	sw x0, -1484(x27)
	lhu x1, -588(x4)
	lhu x2, 1371(x23)
	addi x7, x0, 1905
	or x20, x11, x19
	addi x13, x0, -1522
	srai x4, x24, 26
	la x27, test_memory-294
	la x31, test_memory+118
	sw x16, 858(x27)
	la x1, test_memory+2316
	mul x23, x5, x5
	or x25, x21, x21
	la x20, test_memory+1560
	addi x26, x0, -110
	lbu x8, -843(x20)
	addi x29, x0, 24
	la x14, test_memory+1655
	divu x16, x13, x13
	la x11, test_memory+2453
	addi x30, x0, -441
	mul x17, x30, x30
	sw x16, -66(x31)
	sb x26, -1616(x11)
	addi x15, x0, -1833
	rem x28, x7, x26
	sltu x9, x10, x18
	addi x2, x29, 893
	addi x5, x0, -942
	lb x12, -1210(x14)
	lwu x19, -1480(x1)
	lwu x6, 1453(x22)
	add x24, x15, x5
	addi x22, x0, -295
	la x11, test_memory-351
	la x25, test_memory-829
	sb x7, 1160(x25)
	divuw x29, x24, x3
	addi x5, x0, -1643
	mul x19, x24, x24
	mulhsu x3, x3, x6
	addi x20, x0, -97
	addi x18, x0, 1521
	mulh x8, x18, x18
	la x16, test_memory+1393
	addi x6, x20, -1459
	addi x28, x0, -163
	la x13, test_memory+916
	slt x23, x22, x28
	addi x26, x0, 772
	addi x17, x26, 1310
	addi x7, x0, -2021
	sll x4, x7, x7
	la x9, test_memory+78
	addi x31, x0, -614
	lhu x10, -1359(x16)
	sraw x15, x5, x31
	sh x29, 438(x9)
	lw x14, -404(x13)
	addi x21, x0, 1
	sll x21, x21, 63
	addi x24, x0, -1
	lh x30, 1273(x11)
	xor x24, x24, x21
	and x27, x2, x24
	or x1, x19, x21
	addw x2, x20, x20
	la x23, test_memory+2077
	addi x3, x0, 1154
	xori x17, x22, -1682
	addi x6, x0, 1869
	addi x29, x0, -290
	remw x11, x24, x8
	addi x5, x0, 239
	addi x12, x0, 1
	addi x7, x0, -347
	divuw x9, x4, x29
	bltu x17, x17, crash_backward
	addi x13, x0, 1264
	addi x27, x0, 906
	addi x10, x3, 1448
	sraiw x14, x0, 26
	sra x22, x29, x29
	addi x16, x0, 1048
	addi x2, x7, -1049
	lhu x30, -2011(x23)
	remw x26, x13, x13
	and x18, x3, x3
	divu x4, x5, x5
	la x25, test_memory+13
	sll x12, x12, 63
	addi x20, x0, -718
	mul x15, x5, x15
	bge x3, x10, crash_backward
	lh x19, 623(x25)
	addi x31, x0, -1
	subw x28, x6, x20
	xor x31, x31, x12
	slt x21, x27, x16
	and x24, x5, x31
	or x8, x24, x12
	beq x24, x8, crash_forward
	la x26, test_memory+1543
	addi x18, x0, -608
	mul x30, x8, x15
	addi x23, x0, -711
	addi x31, x0, 1514
	remuw x5, x18, x18
	andi x13, x12, -1957
	ld x28, -1103(x26)
	mulh x14, x31, x31
	and x5, x26, x26
	addi x12, x23, -1507
	addi x6, x0, 1
	addi x28, x0, 1296
	addi x13, x0, -1944
	subw x18, x28, x13
	remu x9, x0, x28
	addi x20, x0, 1
	blt x23, x12, crash_backward
	or x4, x1, x1
	divuw x27, x15, x1
	addi x25, x0, 1992
	addi x2, x0, 0
	sll x20, x20, 63
	addi x8, x0, -1
	sll x6, x6, 63
	xor x8, x8, x20
	and x16, x6, x8
	addi x17, x0, -1
	addi x22, x25, -911
	la x22, test_memory+605
	addi x27, x0, 1616
	addi x13, x0, -1744
	addi x3, x0, 0
	mulhu x7, x16, x7
	or x15, x13, x20
	la x29, test_memory-1121
	la x1, test_memory-861
	bne x2, x3, crash_backward
	la x18, test_memory+1467
	addi x9, x29, 0
	xor x17, x17, x6
	addi x12, x9, 0
	mulhu x28, x13, x13
	la x30, test_memory-1299
	lhu x21, 1609(x1)
	lw x4, -671(x18)
	la x7, test_memory+291
	bne x9, x12, crash_backward
	ld x14, -445(x22)
	xor x21, x5, x5
	addi x13, x0, 1637
	lw x28, 221(x7)
	and x10, x5, x17
	addi x1, x0, 152
	addi x3, x13, 1270
	xor x11, x31, x25
	or x24, x27, x6
	bge x13, x3, crash_backward
	sh x17, 1487(x30)
	addi x9, x0, 1
	addi x5, x0, -1858
	sll x9, x9, 63
	la x31, test_memory-1188
	subw x17, x15, x15
	addi x26, x0, 1473
	addi x11, x0, -41
	addi x6, x0, 1
	la x20, test_memory+963
	and x15, x16, x24
	addi x22, x0, -1
	lbu x19, 1311(x29)
	xor x22, x22, x9
	addi x25, x0, 1
	mulw x14, x11, x11
	sub x23, x27, x5
	la x29, test_memory-1583
	divu x19, x19, x29
	lhu x16, -303(x20)
	srlw x2, x1, x26
	addi x11, x0, 229
	lwu x18, 1492(x31)
	la x14, test_memory+1695
	mulh x8, x11, x11
	and x4, x8, x22
	sll x6, x6, 63
	srai x30, x17, 52
	addi x3, x0, -1
	ld x10, -1135(x14)
	or x12, x30, x9
	bltu x12, x4, crash_backward
	addi x19, x0, 222
	addi x12, x0, 602
	sll x25, x25, 63
	divuw x23, x24, x0
	la x15, test_memory-1040
	addi x20, x0, 1
	addi x5, x0, -1455
	addi x27, x0, 142
	lhu x17, 1685(x29)
	sh x16, 1136(x15)
	la x1, test_memory+1736
	lwu x16, -1392(x1)
	remu x18, x9, x9
	addi x30, x16, -227
	la x14, test_memory-1283
	addi x22, x19, 465
	xor x23, x19, x30
	sraw x17, x2, x3
	sll x20, x20, 63
	addi x31, x0, -1
	sd x28, 1843(x14)
	addi x7, x0, -1
	addi x8, x0, 1829
	xor x7, x7, x25
	xor x3, x3, x6
	divuw x10, x12, x8
	and x24, x13, x3
	addi x15, x0, -1198
	blt x22, x19, crash_forward
	xor x31, x31, x20
	addi x29, x0, 1423
	divu x4, x27, x27
	addi x26, x5, -1922
	and x2, x26, x31
	sllw x11, x15, x29
	or x13, x24, x6
	or x9, x25, x20
	bgeu x24, x13, crash_backward
	and x21, x10, x7
	or x28, x21, x25
	blt x21, x28, crash_forward
	addi x25, x0, 1087
	addi x20, x0, 1
	la x18, test_memory+557
	sllw x2, x25, x25
	addi x24, x0, 1
	sll x13, x25, x25
	sll x24, x24, 63
	addi x27, x0, -1
	la x4, test_memory-1265
	xor x27, x27, x24
	la x9, test_memory+2362
	addi x1, x0, -1434
	and x30, x27, x27
	div x19, x1, x1
	lhu x22, -1424(x9)
	la x26, test_memory+2438
	addi x11, x0, 1
	la x14, test_memory-12
	lwu x6, 464(x14)
	or x12, x17, x24
	sll x11, x11, 63
	sll x20, x20, 63
	addi x23, x0, -1
	lh x3, 353(x18)
	xor x23, x23, x20
	addi x28, x0, -1
	xor x28, x28, x11
	addi x10, x28, 203
	la x5, test_memory+1609
	sw x31, -1165(x5)
	and x21, x23, x23
	or x8, x21, x20
	lhu x16, 1455(x4)
	ld x29, -1998(x26)
	and x15, x20, x28
	or x17, x8, x11
	bgeu x15, x17, crash_forward
	slti x8, x1, -185
	addi x24, x0, 1640
	or x9, x26, x26
	addi x7, x0, 0
	mulhsu x2, x29, x29
	subw x25, x29, x26
	addi x28, x0, 0
	and x27, x18, x18
	addi x19, x0, -641
	addi x10, x0, 262
	addiw x25, x24, 405
	sub x31, x3, x6
	la x23, test_memory-1360
	sll x26, x10, x10
	la x11, test_memory+1797
	la x8, test_memory+957
	la x18, test_memory-203
	addi x6, x0, 467
	la x22, test_memory+2325
	sb x31, -1726(x11)
	sb x15, -939(x8)
	addi x14, x0, -1456
	bltu x7, x28, crash_backward
	ld x4, -1461(x22)
	sub x12, x19, x14
	ld x21, 923(x18)
	mulhu x18, x2, x2
	la x19, test_memory+2374
	addi x4, x0, 1
	addi x21, x10, 0
	slli x11, x3, 29
	addi x9, x0, 1307
	addi x30, x0, 1
	sll x4, x4, 63
	sll x30, x30, 63
	addi x1, x0, 1
	addi x5, x0, -857
	sllw x29, x24, x5
	la x26, test_memory-1120
	la x13, test_memory-751
	addi x8, x0, -1
	sll x1, x1, 63
	ld x10, -1718(x19)
	mulhu x28, x17, x17
	addi x2, x0, 1092
	xor x8, x8, x4
	addi x14, x21, 0
	sh x24, 1132(x26)
	sd x28, 1271(x13)
	addi x17, x6, 1573
	addi x7, x0, -1
	lhu x20, 1470(x23)
	bge x6, x17, crash_backward
	addi x3, x0, -1
	mulw x27, x9, x2
	and x31, x3, x8
	xor x3, x3, x30
	slli x17, x19, 10
	or x25, x8, x4
	beq x31, x25, crash_forward
	and x16, x0, x3
	xor x7, x7, x1
	and x12, x27, x7
	or x15, x16, x30
	bltu x15, x16, crash_backward
	or x22, x12, x1
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
	sd x14, 112(x1)
	sd x15, 120(x1)
	sd x16, 128(x1)
	sd x17, 136(x1)
	sd x18, 144(x1)
	sd x20, 160(x1)
	sd x21, 168(x1)
	sd x22, 176(x1)
	sd x24, 192(x1)
	sd x25, 200(x1)
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
reg_x0_init:	.dword 0xffffffffffffffff
reg_x1_init:	.dword 0x05b24dde0ebc49ff
reg_x2_init:	.dword 0x45d8ddd49efc9490
reg_x3_init:	.dword 0x9e5d82fba366ef78
reg_x4_init:	.dword 0x0000000000000000
reg_x5_init:	.dword 0x51d8a6923ecea786
reg_x6_init:	.dword 0x8cfd2af7f5d54ed2
reg_x7_init:	.dword 0x0000000000000000
reg_x8_init:	.dword 0x979e9578a03baa18
reg_x9_init:	.dword 0x9d14ea8095b6053a
reg_x10_init:	.dword 0x0000000000000000
reg_x11_init:	.dword 0xffffffffffffff80
reg_x12_init:	.dword 0x7fa44737b92bea5c
reg_x13_init:	.dword 0xffffffff80000003
reg_x14_init:	.dword 0x5f5c143c131b778c
reg_x15_init:	.dword 0x7dc4138e17d6800f
reg_x16_init:	.dword 0xffffffffffffff82
reg_x17_init:	.dword 0xffffffff80000005
reg_x18_init:	.dword 0x041a4b7db29bc881
reg_x19_init:	.dword 0x2fefcd23cba47b51
reg_x20_init:	.dword 0xf6365dd548e4a583
reg_x21_init:	.dword 0x0000000000000001
reg_x22_init:	.dword 0xfcd8efa55fc35b65
reg_x23_init:	.dword 0x0000000000000000
reg_x24_init:	.dword 0xffffffffffff8006
reg_x25_init:	.dword 0xfd2d9e1a0e4f3c8c
reg_x26_init:	.dword 0x1d98ecb29824bd8d
reg_x27_init:	.dword 0x0000000000000000
reg_x28_init:	.dword 0x0000000000000000
reg_x29_init:	.dword 0x926acab033af7f6a
reg_x30_init:	.dword 0xffffffffffffffff
reg_x31_init:	.dword 0x0800000000000003

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0xd4d766c5b23d603c
reg_x1_output:	.dword 0xce1deee30bb3b60c
reg_x2_output:	.dword 0xaab07f5da5ebb30f
reg_x3_output:	.dword 0x0fe7c760812a19fb
reg_x4_output:	.dword 0xd37c2c18c0c41f31
reg_x5_output:	.dword 0xe54552e05aa1bbec
reg_x6_output:	.dword 0x8fcb9639165d8efc
reg_x7_output:	.dword 0xe77ea136376ba1ac
reg_x8_output:	.dword 0xad89393780dcde84
reg_x9_output:	.dword 0xb74c842cd33a70f9
reg_x10_output:	.dword 0xadca69c3ea28f055
reg_x11_output:	.dword 0x208f181e68cdf556
reg_x12_output:	.dword 0x1983c909b6fed95e
reg_x13_output:	.dword 0xee51b2d87270af1f
reg_x14_output:	.dword 0x83fb28365988582b
reg_x15_output:	.dword 0x7fe45cc4edd6bfdc
reg_x16_output:	.dword 0x6e75a0398c860b5a
reg_x17_output:	.dword 0xb1b1384f420ec7d9
reg_x18_output:	.dword 0x3348e1cf33421b47
reg_x19_output:	.dword 0xc5f67b7ec82a88f5
reg_x20_output:	.dword 0xab6301b91c974b09
reg_x21_output:	.dword 0x00f3dfe6fb4e62ba
reg_x22_output:	.dword 0x48cc454deba3a4a2
reg_x23_output:	.dword 0x1ba4acc20833fbae
reg_x24_output:	.dword 0x86dab3379e7d3471
reg_x25_output:	.dword 0x660dbf58f81dabe8
reg_x26_output:	.dword 0x7e076c78b5b287eb
reg_x27_output:	.dword 0xf0b935a6fcfd7ce5
reg_x28_output:	.dword 0x09d211aef5c7e38a
reg_x29_output:	.dword 0xc26f9f3f7d6bd29b
reg_x30_output:	.dword 0xb31eb899697d6404
reg_x31_output:	.dword 0x85d8d86cc43711cf

// Memory Blocks
	.align 8
test_memory:
	.dword 0xad3f35d96fb97ec0, 0x28acf39b9a16d7a3
	.dword 0xdfa0befaadb69585, 0x2dbfd4f655a29672
	.dword 0xae2328b51cc99174, 0x6ab86450ef54abe0
	.dword 0xf6af456fb602b938, 0x2bee79489260442c
	.dword 0x4ff628068449367b, 0x42f8e5a8b8b19ec7
	.dword 0xc39b4ecceaa4fe9b, 0xf927420db5d5882a
	.dword 0x11a7fad46772129d, 0xc4b960ce52fe1ce4
	.dword 0x9446376bf9734a61, 0xa0608b14c32829f2
	.dword 0x6da655e9e86a1f17, 0x0eb4ec5152c5be52
	.dword 0x1ed9e1aa233c28f1, 0xd90bcfcf2f87c1da
	.dword 0x999b5055b106441a, 0x10c194a5f429a545
	.dword 0x70a9f267140890e6, 0x7dd47bd316bf7f8e
	.dword 0xded5e7eaa455c349, 0x93dbb4a54f382c80
	.dword 0xdc501d8937e3758d, 0x01384b5abcca408e
	.dword 0x908e95c23d40723f, 0x9a13de0b451be5df
	.dword 0xcd5582794911296a, 0x8b9b3bc3fc62f6ad
	.dword 0x5979f2b3fbc1c507, 0x9a2151f68bbbe8cf
	.dword 0x1ffb18a3c7e090b3, 0x80b90c1187cb5e93
	.dword 0x965b6be2298aa8a2, 0x109b096c96a770d1
	.dword 0x1bf32bfb278023d3, 0x44964d688e43063c
	.dword 0xb78a072dce142d85, 0x5f194dd65d66cbfb
	.dword 0x791de972be80c1e9, 0x3a5303956de8a377
	.dword 0x2f9937bee16d0218, 0xf7c1e17e288b9976
	.dword 0xe59afb85f4f05346, 0x2180d58296ffba69
	.dword 0x4997c280ac4bbd38, 0x6200b814a01a5801
	.dword 0x5cc236b0bd363bf3, 0x28decdc5aad49407
	.dword 0x5d96b2a1cb2ff8b5, 0xbb6f3f2f4f27446c
	.dword 0x3ed555f4201b9e28, 0x479cab132db8849f
	.dword 0x3e6a5e17799c3bd5, 0xf62c36c3b1c0881e
	.dword 0x817cc75487a96cd6, 0xb087c0c4d8d08250
	.dword 0x67d77a14a1b2b5cf, 0x3c2619afab7fb790
	.dword 0x8161885d7fc64e1f, 0x7cc36759b5b00b8c
	.dword 0x689e3f97abbec851, 0x8d1a1633f65ca0d0
	.dword 0xf5761298d6be4dd8, 0xfdeefcf2b2fa5d9d
	.dword 0x40159fdf307561fb, 0xe3499672b29b69ff
	.dword 0x44c0581a631e600e, 0x81db75d84e83fb1e
	.dword 0xeb4888ed7ff628e2, 0xe92858f5c1efffd3
	.dword 0x07b6cff5378db37e, 0xb4327cf246ae827e
	.dword 0x29c73a0a66d7750e, 0x908519290130d416
	.dword 0xce8292c3b88ed41b, 0x34b1245001f8d481
	.dword 0x969ea840b9c71afc, 0xa9eec7dac532ec25
	.dword 0x5db88723db529d8b, 0x6ad825a180fd8abe
	.dword 0x8e27f2dff78a061c, 0xf15853c238a93f71
	.dword 0x735b9e34d006fdab, 0x1a33b2c13c59be21
	.dword 0xfda1e7f9c064a354, 0xe33d01f55a216602
	.dword 0xce3a201d7d4b8707, 0xbc9cd62545361d6b
	.dword 0x25c698e7f9361b7b, 0x13c75670627796ef
	.dword 0xa1f808857db5d362, 0x3216636d5c6c53ad
	.dword 0x8dcefec42fd05ddf, 0xafbc8c934d5bf6e7
	.dword 0xda587319c38fb634, 0xe82777db7982bed1
	.dword 0xe096aeec3d56fac0, 0x452e9fa316c336ab
	.dword 0x9098180ca2393f27, 0x34d58ad567f87611
	.dword 0x31d19f8532aecdd2, 0xf036e348015c8191
	.dword 0xddead893bfd88c9a, 0x43a00e65b69ba07e
	.dword 0x3585fbf6524878bf, 0x8e3b2c0de366bc03
	.dword 0xc66e5b675d416e1e, 0x9d1f9fba31e41b7a
	.dword 0x483c096839cfada3, 0xa87f87e4087f11fe
	.dword 0x5023b943753ed6fb, 0x042ac7a4878c713e
	.dword 0xc2961b4d6589498e, 0x5d06869eb042d594
	.dword 0xf9c2396b6fa820ac, 0x1da24b1d7ee31f55
	.dword 0xf74297d5e66a3f05, 0xab02127792dead6a
	.dword 0xad751e2187ec1d5e, 0x1a470bbc668e2d1f
	.dword 0x667a0c7b7b315082, 0x2e56d88a1de5133a
	.dword 0xfbd6813191fbfa76, 0x643b783ef5bb124f

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
