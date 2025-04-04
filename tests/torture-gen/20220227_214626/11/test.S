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
	addi x26, x0, -1300
	addi x2, x0, 1
	addi x21, x0, 1209
	bne x0, x0, crash_backward
	or x16, x21, x21
	addi x29, x0, 3
	la x27, test_memory+1501
	addi x3, x0, -394
	divw x24, x26, x26
	addi x25, x0, 1015
	addi x9, x0, -855
	la x30, test_memory+1608
	addi x4, x25, 1663
	and x23, x9, x9
	addi x19, x0, -156
	addi x31, x0, 1824
	addi x5, x0, -1995
	bne x0, x0, crash_forward
	la x28, test_memory+1294
	addi x10, x25, 1309
	la x15, test_memory+1702
	sd x29, -1142(x28)
	sll x26, x7, x7
	addi x11, x0, -1731
	la x13, test_memory+2148
	sw x29, -1548(x30)
	lb x18, -1574(x13)
	mulw x7, x5, x11
	sll x2, x2, 63
	sra x6, x3, x19
	remw x17, x29, x31
	addi x9, x0, 1119
	slli x14, x20, 6
	addi x17, x23, 0
	la x11, test_memory-895
	lbu x22, -1443(x27)
	addi x3, x0, -1955
	mulhu x19, x3, x3
	blt x10, x25, crash_backward
	la x23, test_memory+1824
	mulhsu x31, x24, x24
	addi x5, x17, 0
	sh x10, -1572(x23)
	addi x1, x0, -1
	la x6, test_memory-1344
	addi x28, x0, 1
	lhu x13, 1844(x6)
	addi x18, x0, -1520
	xor x1, x1, x2
	and x20, x28, x1
	lbu x12, -1471(x15)
	sll x28, x28, 63
	or x8, x16, x2
	sllw x4, x9, x18
	lb x7, 1144(x11)
	addi x14, x0, -733
	addi x30, x0, -467
	la x2, test_memory-635
	la x22, test_memory-738
	la x24, test_memory+2058
	sh x9, 1169(x2)
	addi x1, x0, 1
	addi x21, x0, -1
	addi x25, x0, 1679
	sra x5, x30, x25
	remw x7, x14, x14
	sub x8, x24, x24
	la x17, test_memory-1068
	lhu x3, 1714(x17)
	sll x1, x1, 63
	la x4, test_memory-1062
	addi x27, x0, -1
	srlw x26, x8, x22
	sh x14, -1560(x24)
	la x6, test_memory+837
	addi x12, x0, 1449
	xor x27, x27, x1
	xor x21, x21, x28
	and x29, x29, x21
	la x31, test_memory-15
	or x16, x13, x28
	addi x11, x0, -1652
	and x19, x7, x27
	addi x13, x0, -664
	lhu x23, 1236(x22)
	bne x0, x0, crash_forward
	bltu x16, x29, crash_backward
	la x22, test_memory-34
	addi x20, x0, -724
	addi x30, x0, 1908
	la x25, test_memory+1546
	lw x9, -413(x6)
	addi x2, x0, -2040
	sh x5, 445(x31)
	sw x26, 1886(x4)
	la x23, test_memory+2551
	subw x15, x12, x11
	or x10, x19, x1
	remuw x24, x30, x2
	addi x3, x0, 378
	addi x7, x0, 1237
	addi x29, x0, 1
	sltu x18, x13, x20
	bge x10, x19, crash_forward
	lb x14, -1928(x23)
	addi x30, x0, 1446
	la x31, test_memory-505
	divuw x9, x20, x7
	rem x2, x30, x30
	addi x24, x0, 2008
	lb x12, 995(x31)
	addi x6, x28, 0
	addi x2, x0, 1
	div x17, x3, x7
	addi x4, x24, 1524
	addi x15, x6, 0
	blt x4, x24, crash_forward
	lwu x8, 894(x22)
	sllw x11, x14, x14
	sll x29, x29, 63
	la x1, test_memory+3
	addi x27, x0, -279
	addi x26, x0, 575
	sll x2, x2, 63
	la x19, test_memory-745
	and x31, x27, x27
	addi x9, x0, -1
	la x23, test_memory+588
	sub x5, x26, x26
	divu x24, x25, x25
	la x10, test_memory-1017
	sw x15, 1445(x19)
	mulhsu x4, x16, x16
	addi x28, x0, -1
	la x18, test_memory+962
	la x11, test_memory-1247
	la x31, test_memory+1526
	lwu x20, 1193(x10)
	addi x4, x0, -1442
	xor x28, x28, x29
	sra x7, x14, x5
	div x17, x1, x1
	sd x26, -690(x25)
	lhu x24, -1236(x31)
	and x21, x14, x28
	la x20, test_memory-353
	addi x26, x4, -1522
	lbu x3, 618(x20)
	sh x5, -146(x18)
	addiw x8, x13, -566
	la x25, test_memory-20
	lwu x14, 693(x1)
	sb x9, 1825(x11)
	la x24, test_memory+1221
	beq x4, x26, crash_forward
	la x20, test_memory+338
	addi x31, x0, -841
	xor x9, x9, x2
	and x12, x16, x9
	or x30, x6, x2
	addi x27, x0, -824
	addi x17, x31, -1376
	lhu x13, 230(x23)
	lwu x22, 232(x25)
	bltu x6, x15, crash_forward
	addi x5, x27, -514
	addi x6, x0, 1333
	la x7, test_memory+1756
	lw x10, -6(x20)
	la x11, test_memory+150
	sw x21, -1456(x7)
	mulhsu x31, x6, x1
	remu x10, x17, x17
	addi x1, x0, -351
	addi x22, x0, -325
	lh x3, -919(x24)
	addi x15, x0, -761
	or x16, x0, x29
	addi x23, x22, -1845
	lb x19, 89(x11)
	srlw x18, x6, x6
	remu x26, x1, x1
	bltu x16, x21, crash_backward
	addi x14, x0, -100
	la x18, test_memory+2957
	la x29, test_memory+1376
	sllw x25, x5, x12
	lwu x23, -1957(x18)
	slli x16, x4, 52
	lwu x12, -1068(x29)
	addi x9, x0, 1753
	addi x3, x0, 1
	sraw x10, x9, x9
	la x28, test_memory+970
	ld x22, -98(x28)
	sll x19, x16, x16
	addi x24, x0, -1104
	addi x13, x0, -1568
	la x31, test_memory-890
	sll x8, x14, x14
	mulh x4, x15, x15
	la x11, test_memory-576
	blt x27, x5, crash_forward
	add x21, x24, x24
	lw x30, 1256(x11)
	addi x20, x0, 716
	sll x3, x3, 63
	sltu x17, x13, x20
	la x1, test_memory+775
	lb x2, 1270(x31)
	sb x15, -392(x1)
	la x12, test_memory+1878
	addi x9, x3, 0
	addi x20, x0, -1089
	addi x13, x9, 0
	lb x27, -1074(x12)
	addi x7, x0, -1
	srl x10, x0, x22
	la x25, test_memory-423
	la x11, test_memory+1740
	addi x21, x0, 293
	xor x18, x2, x16
	la x4, test_memory-308
	xor x7, x7, x3
	addi x31, x0, 180
	sh x2, 995(x25)
	addi x24, x19, -1521
	addi x29, x0, -644
	la x5, test_memory+2472
	sb x20, 1148(x4)
	srl x25, x26, x26
	addi x17, x0, 797
	addi x16, x0, -626
	addi x10, x0, 1463
	la x15, test_memory+328
	addi x1, x17, 1714
	sll x30, x21, x21
	sw x16, -300(x15)
	sltu x8, x20, x16
	divu x18, x10, x10
	add x27, x31, x12
	lhu x23, -900(x11)
	addi x14, x0, 2018
	addi x22, x0, 972
	div x28, x29, x14
	mulh x2, x31, x31
	and x26, x23, x7
	bgeu x17, x1, crash_backward
	or x6, x26, x3
	sh x23, -1638(x5)
	addi x12, x0, 1822
	sraw x24, x22, x12
	addi x7, x0, 996
	slt x31, x15, x15
	addi x9, x0, 856
	la x4, test_memory+2855
	addi x13, x0, 1
	la x26, test_memory-540
	la x1, test_memory+1961
	addi x18, x7, 1432
	sll x13, x13, 63
	addi x14, x28, 0
	addi x15, x0, 520
	addi x21, x0, -821
	addi x10, x0, -257
	bgeu x7, x18, crash_backward
	addi x22, x0, -898
	la x19, test_memory+1304
	lb x30, 1412(x26)
	sltu x25, x21, x22
	addi x29, x14, 0
	lbu x8, -1806(x1)
	sltiu x18, x9, -1463
	srlw x11, x9, x15
	lh x6, -1961(x4)
	lh x17, -938(x19)
	addi x21, x0, 704
	div x30, x21, x21
	addi x2, x10, -309
	blt x10, x2, crash_backward
	sraw x27, x27, x27
	bltu x14, x29, crash_forward
	la x26, test_memory-6
	ld x1, 278(x26)
	addi x5, x0, -1
	addi x23, x0, -989
	addi x8, x0, 1430
	xor x5, x5, x13
	addi x12, x0, 891
	addi x28, x23, -1242
	addi x10, x0, -29
	addi x14, x0, 1
	la x18, test_memory-1174
	or x1, x6, x28
	la x19, test_memory+1921
	and x16, x7, x5
	sll x14, x14, 63
	la x26, test_memory+1381
	mulh x30, x5, x5
	addi x11, x0, -861
	blt x23, x28, crash_backward
	la x25, test_memory+1555
	addi x15, x0, 1
	la x21, test_memory+1771
	addi x2, x0, 651
	addi x24, x0, -1
	sll x27, x10, x10
	la x23, test_memory-387
	or x20, x16, x13
	or x3, x12, x12
	sw x3, -1493(x19)
	sd x9, -1355(x21)
	la x28, test_memory+95
	addi x7, x0, 1081
	xor x24, x24, x14
	sb x11, 1659(x18)
	la x10, test_memory-1208
	and x17, x19, x24
	or x22, x30, x14
	sll x15, x15, 63
	div x4, x11, x2
	sd x6, -1435(x25)
	lb x29, -958(x26)
	sd x31, 785(x28)
	addi x1, x0, -1
	lh x30, 1271(x23)
	divw x31, x8, x7
	addi x3, x0, -1097
	addiw x13, x24, -193
	addi x26, x0, -1685
	xor x1, x1, x15
	sub x19, x26, x26
	la x21, test_memory+1951
	addi x20, x0, 1638
	sd x15, -1183(x21)
	srl x12, x3, x3
	la x2, test_memory-1310
	lbu x4, 1832(x2)
	la x8, test_memory-65
	or x11, x20, x20
	and x9, x1, x1
	lh x31, 463(x8)
	addi x25, x0, 348
	la x31, test_memory+2998
	addi x30, x0, -890
	la x20, test_memory-628
	divw x16, x1, x1
	addi x7, x0, 1958
	addi x21, x0, -445
	sltu x18, x12, x1
	addi x12, x0, 131
	addi x5, x0, -1582
	sd x19, -2030(x31)
	sb x1, 900(x20)
	la x8, test_memory-777
	sub x29, x25, x30
	blt x14, x14, crash_backward
	lbu x19, 1076(x8)
	remu x2, x7, x7
	sub x16, x13, x13
	addi x26, x12, 1380
	addi x3, x0, -1060
	addi x22, x0, -53
	addi x31, x0, -228
	sraiw x8, x10, 25
	addi x16, x0, -1285
	addi x24, x0, 1
	addi x13, x21, -948
	or x6, x9, x15
	blt x9, x6, crash_backward
	addi x11, x0, -1439
	addi x20, x0, 783
	srl x18, x22, x31
	divuw x19, x16, x16
	bge x13, x21, crash_forward
	divw x4, x3, x11
	addi x12, x0, 651
	addi x29, x0, 1757
	addi x31, x0, -509
	la x9, test_memory+1920
	la x16, test_memory+2254
	lwu x27, 1556(x10)
	remw x6, x25, x25
	addi x19, x0, 1318
	addi x23, x5, -108
	la x10, test_memory-1647
	la x28, test_memory+1769
	mulw x17, x20, x29
	sll x24, x24, 63
	addi x18, x12, 995
	addi x25, x0, -1
	addi x3, x0, 1944
	divw x15, x31, x31
	srl x11, x3, x3
	la x27, test_memory-1030
	xor x25, x25, x24
	lh x22, -1530(x16)
	sw x17, -1628(x9)
	addi x20, x0, 707
	addi x29, x20, 913
	addi x2, x0, 1455
	la x11, test_memory+1387
	la x12, test_memory+492
	sll x6, x10, x10
	sh x22, -1053(x28)
	addi x8, x19, 1430
	la x4, test_memory+511
	lh x21, 53(x4)
	addi x16, x0, -1248
	and x7, x2, x2
	addi x22, x0, 558
	addi x13, x0, 1169
	bltu x5, x23, crash_backward
	bne x0, x0, crash_backward
	addi x6, x0, -1921
	addi x18, x0, -1026
	la x4, test_memory-830
	sw x2, -711(x11)
	srl x1, x13, x13
	and x14, x31, x25
	and x28, x22, x6
	divu x15, x18, x18
	sd x17, 228(x12)
	mulw x29, x16, x6
	slti x17, x28, 1636
	lhu x26, 1941(x10)
	lbu x7, 1720(x4)
	addi x22, x0, 1
	la x19, test_memory+1264
	addi x17, x0, -368
	addi x31, x18, -2030
	addi x11, x17, -1919
	la x29, test_memory+2212
	sll x22, x22, 63
	addi x3, x0, 418
	la x4, test_memory-360
	remw x1, x19, x19
	addi x28, x0, -1
	lbu x20, -278(x19)
	bge x31, x18, crash_backward
	or x30, x14, x24
	lhu x7, 1306(x4)
	xor x28, x28, x22
	and x15, x12, x28
	lwu x5, -1256(x29)
	blt x14, x30, crash_forward
	sb x7, 1325(x27)
	addi x30, x0, 1397
	or x6, x10, x22
	addi x13, x0, 603
	slliw x21, x27, 14
	mul x9, x16, x3
	addi x23, x0, -678
	beq x15, x6, crash_backward
	la x10, test_memory+1013
	addi x7, x0, -331
	sh x28, -327(x10)
	divw x12, x13, x23
	xor x5, x30, x7
	addi x2, x0, 1035
	sllw x8, x2, x2
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
	sd x11, 88(x1)
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
reg_x0_init:	.dword 0x0800000000000007
reg_x1_init:	.dword 0x0000000000000000
reg_x2_init:	.dword 0xe807c8b910806996
reg_x3_init:	.dword 0xffffffffffff8009
reg_x4_init:	.dword 0xbca4f3d0911b917f
reg_x5_init:	.dword 0xa3a3e7fa19bd2978
reg_x6_init:	.dword 0x5617cc1c5a229bb8
reg_x7_init:	.dword 0xffffffffffffffff
reg_x8_init:	.dword 0xffffffffffffffff
reg_x9_init:	.dword 0x0800000000000009
reg_x10_init:	.dword 0x190f970650fe7d1a
reg_x11_init:	.dword 0x9c5a82a9e4ded88e
reg_x12_init:	.dword 0xffffffff80000002
reg_x13_init:	.dword 0xc27a94b203b023ff
reg_x14_init:	.dword 0xffffffffffffffff
reg_x15_init:	.dword 0xffffffffffffff84
reg_x16_init:	.dword 0x05888ae272f2ee8c
reg_x17_init:	.dword 0xffffffffffff8002
reg_x18_init:	.dword 0x012e4afa9fab6658
reg_x19_init:	.dword 0xffffffffffffffff
reg_x20_init:	.dword 0x6a87230459c64bdb
reg_x21_init:	.dword 0xffffffffffffff87
reg_x22_init:	.dword 0x0000000000000002
reg_x23_init:	.dword 0x9e1516965d5febe6
reg_x24_init:	.dword 0xffffffffffffffff
reg_x25_init:	.dword 0x0000000000000000
reg_x26_init:	.dword 0xc126d9f18441c2d3
reg_x27_init:	.dword 0xffffffffffffff89
reg_x28_init:	.dword 0x0ea7dbbc40897f35
reg_x29_init:	.dword 0x04bae66ffe8efb66
reg_x30_init:	.dword 0x0000000000000000
reg_x31_init:	.dword 0x7bb99601c13d5e4c

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0xe020e5600887814f
reg_x1_output:	.dword 0x2a07e2e0d44d03bd
reg_x2_output:	.dword 0xa4bf042e08bf65f6
reg_x3_output:	.dword 0x92cacb6d0c5aa89a
reg_x4_output:	.dword 0x64054498ecc4bf2e
reg_x5_output:	.dword 0x632bd58bbd1aa396
reg_x6_output:	.dword 0x45d601d2358c3275
reg_x7_output:	.dword 0xa0dddc42b88135d2
reg_x8_output:	.dword 0xd112c3b8083145b2
reg_x9_output:	.dword 0x6933bd548610d284
reg_x10_output:	.dword 0x9551964593aed399
reg_x11_output:	.dword 0xfd6bbfd5458dc3f9
reg_x12_output:	.dword 0xaf4be44bc27fe252
reg_x13_output:	.dword 0xfc324ffb9fd89cdc
reg_x14_output:	.dword 0xfa53c960d624c05d
reg_x15_output:	.dword 0x8b74243be927f9b8
reg_x16_output:	.dword 0x64780f1713e28baf
reg_x17_output:	.dword 0xc6851f95745e56bb
reg_x18_output:	.dword 0x90ce497046d18721
reg_x19_output:	.dword 0x6f228525cfc0fdbc
reg_x20_output:	.dword 0xeeddc690ddb0e20a
reg_x21_output:	.dword 0x292c51067421507e
reg_x22_output:	.dword 0xd69d45b5093cd62a
reg_x23_output:	.dword 0x0a5aca5418d9f335
reg_x24_output:	.dword 0x6920a962d42e3fc9
reg_x25_output:	.dword 0xedf2a28be5159b4a
reg_x26_output:	.dword 0xbe3318e376d9141f
reg_x27_output:	.dword 0x49cb361ba1ed865b
reg_x28_output:	.dword 0xc9ed44ed87d159f6
reg_x29_output:	.dword 0x8b1fc235ad49dd85
reg_x30_output:	.dword 0xda1ec3a46754888d
reg_x31_output:	.dword 0xafdda3e70b4e88e5

// Memory Blocks
	.align 8
test_memory:
	.dword 0x3d5cb7c1c6af70bf, 0xa1aef468a7c3375a
	.dword 0xb3f7371345b71464, 0x1c2216b3ba8d9e90
	.dword 0x893a242740ed0ff7, 0xc4440a59ae41373a
	.dword 0x68756f42694e7a79, 0xc70c9793be37f99e
	.dword 0x2893f29715565f94, 0x6258a89766dbde56
	.dword 0x51c75db647ab3802, 0x4b20642c5f012754
	.dword 0x2e42e440ad81042f, 0xe85bdd7f10adb526
	.dword 0xe065a3e5bb2fed1d, 0xdde26d35daa9ec7a
	.dword 0x8950f5881b198f87, 0xc2be07c4fefbefe5
	.dword 0xc1f61dbec7f55549, 0x0c2d25003d3631df
	.dword 0xf96a1081fa3e80fe, 0xf7230cf12e8ea312
	.dword 0x1d053c22ff04cfea, 0x66bf9dea8d4400d3
	.dword 0xdcc08f79b70ad61a, 0x7434dfde652b07f0
	.dword 0xf7a02f64de2b78c9, 0x8d21f8ec88958fab
	.dword 0x040f8f6ef6b22b06, 0x0dd0573c9761d106
	.dword 0xd619e1ce50e7d092, 0xee39240ffe205e41
	.dword 0xe4a51292ced06b0e, 0x58865410e5238ea1
	.dword 0x3e84c21bc533f555, 0x6723e8f16b336272
	.dword 0xd39df2cc67cf1126, 0x3cab383259cd234d
	.dword 0x14ab5dfe1d2e6b06, 0xa23b4b40e186449e
	.dword 0x70bda435a181f864, 0x266eacc9c09e4860
	.dword 0xb191cc9924e373fd, 0xb95037486443ac2a
	.dword 0x0a8bc79e535dbc82, 0x2db5b8da4acc226f
	.dword 0x30c9e90619b8f977, 0x2780805cda609c01
	.dword 0x90a18d08cbe9aa5d, 0x6db127b678a1e5d7
	.dword 0xad245cd13f3f0413, 0x883d2f6f6cd2df0f
	.dword 0x9c50e62b454f4078, 0x096a3f84b3618b35
	.dword 0x0d887a7b7366c455, 0xfa5c217ea77884c5
	.dword 0x330f88f11f293f7a, 0x07bfc7c249d693ee
	.dword 0x91fce7fa32622b26, 0x3f4ef622fbc26d98
	.dword 0x294fc1f7cff44aab, 0x468d5fbe0dccdea8
	.dword 0x882b193380ae1252, 0xd7d94e055473e782
	.dword 0x77b11712aac3187b, 0x41f7251aa4dd8bcf
	.dword 0x6de79a86c008f508, 0x70e0596242095a80
	.dword 0x67b2b9c7c81832fc, 0x5213aa51bb43f211
	.dword 0x4f892b438a58385e, 0xec2db68be7980512
	.dword 0x3851c9d39b074863, 0x4e6e3d2dabaca2e2
	.dword 0x5f18a82f4bbe03cb, 0x323fa0683838c8bd
	.dword 0xbe3d67a2fe000b8b, 0x3c1b7d4edb307ef9
	.dword 0x98a3c6017b61a9ab, 0xc3806cf14550068c
	.dword 0x8e8a96d7cce4a471, 0xc85a42a8fceddad1
	.dword 0xc73c9be600ac9fbf, 0xb07f5bb356448b8b
	.dword 0x7611f0cb744db0b9, 0xd6fad401acf1b329
	.dword 0x656ffdff88fe07aa, 0x3a04b45042778d4b
	.dword 0x5ae12706381dd428, 0x59066d775662f185
	.dword 0xa33ca7e25016c775, 0xdb1b34ff0e8fb662
	.dword 0x286a55c855c6d927, 0xf56116f72521c0aa
	.dword 0x52d5371523c0320b, 0xe868d1081e6942e7
	.dword 0x125b268190e26147, 0xca5fcac5d74cf126
	.dword 0x9cb6f596396f3fbe, 0x4170bf49653d2cfa
	.dword 0x4d45c25c2b0025b7, 0xb48cebfb9f5f6dc5
	.dword 0x22df7455c2e656c0, 0xc998d8b3ddd1693a
	.dword 0x578594b0c1cbc7d0, 0x14150d03ebd7c01d
	.dword 0xaa2af5b90d17a3ab, 0x800c46cf3cc4334d
	.dword 0x1009dd8e10ec318a, 0xff96061cd59ba504
	.dword 0x7825a8185aca01fa, 0x16d582323f446a5c
	.dword 0x23f014371f3e8604, 0x304a5bdc2a89b114
	.dword 0x52d9b03e9ac2748d, 0xdac9a10d30c8fd94
	.dword 0xcf1819a2f14ea200, 0xb8caf5a785eb052e
	.dword 0x776403ee8f742e29, 0x971ef59f429968a6
	.dword 0x871c3afb752f2c64, 0xc4e1243cacb712f3
	.dword 0xeb5a145cfc7929f6, 0xe0c8fcc018394047
	.dword 0xeb57041efe1336ba, 0x3622f82a6fdb714d
	.dword 0x444a48b0f45553ff, 0xdef39c587c08ceb1

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
