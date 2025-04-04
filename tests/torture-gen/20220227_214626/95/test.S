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
	remuw x31, x25, x25
	addi x28, x15, -1615
	addi x10, x0, 1
	addi x25, x0, 1
	addi x6, x0, -1611
	sll x25, x25, 63
	addi x5, x0, 1275
	addi x23, x0, -1718
	addi x15, x0, 1
	addi x7, x0, -1244
	addi x21, x0, -1655
	addi x4, x0, -1
	sll x15, x15, 63
	addi x12, x0, -1
	mulw x26, x6, x6
	sll x10, x10, 63
	xor x4, x4, x25
	addi x17, x0, -1
	and x9, x7, x4
	la x8, test_memory-335
	srl x19, x5, x23
	or x29, x8, x25
	la x13, test_memory+1877
	la x24, test_memory+2345
	addi x22, x0, 1876
	bgeu x9, x29, crash_forward
	sllw x18, x7, x7
	srlw x1, x21, x22
	la x3, test_memory+1279
	xor x12, x12, x15
	addi x18, x0, 1
	xor x17, x17, x10
	la x22, test_memory+743
	sw x14, -1657(x24)
	la x2, test_memory+965
	and x30, x0, x17
	la x26, test_memory+4
	lbu x28, 233(x26)
	sb x11, -171(x2)
	la x4, test_memory-396
	lwu x14, 1131(x8)
	ld x11, -1189(x13)
	addi x9, x0, -1741
	or x20, x30, x10
	addi x28, x0, 1
	sll x18, x18, 63
	addi x7, x0, -1
	la x14, test_memory-875
	and x16, x0, x12
	xor x7, x7, x18
	addi x31, x0, 821
	sll x28, x28, 63
	sh x31, -975(x3)
	and x1, x18, x7
	or x27, x10, x15
	addi x2, x0, 2033
	or x8, x2, x2
	mulhu x29, x9, x9
	addi x6, x0, 1833
	addi x19, x31, 1138
	sb x5, 862(x4)
	addi x21, x0, -188
	sltu x5, x21, x21
	and x26, x6, x6
	addi x9, x0, 0
	la x6, test_memory-1212
	xor x10, x0, x27
	lw x25, -275(x22)
	addi x8, x0, 0
	addi x29, x0, 809
	addi x22, x0, 1142
	sub x17, x16, x16
	addi x11, x0, -1
	addi x12, x0, -1085
	addi x21, x0, -980
	sraw x10, x22, x22
	addi x15, x0, 1
	or x23, x27, x18
	la x9, test_memory-1251
	la x8, test_memory+1198
	sllw x22, x31, x9
	sll x15, x15, 63
	sw x21, 1731(x14)
	mul x30, x29, x12
	lhu x17, 1913(x9)
	addi x20, x0, -1
	bltu x23, x1, crash_forward
	la x4, test_memory-272
	addi x12, x0, 84
	addi x16, x21, -1494
	addi x9, x0, 1358
	sw x23, -1050(x8)
	addi x23, x0, 1836
	lb x25, 579(x4)
	remuw x29, x27, x27
	xor x11, x11, x28
	mulh x18, x12, x23
	and x24, x18, x11
	addi x18, x0, 0
	or x13, x24, x28
	xor x20, x20, x15
	addi x4, x0, 0
	beq x24, x13, crash_backward
	la x12, test_memory+398
	addi x21, x0, -1718
	la x3, test_memory+1001
	blt x19, x31, crash_backward
	la x26, test_memory+1129
	lhu x27, 1356(x6)
	sd x11, 130(x12)
	sh x11, -979(x26)
	addi x29, x0, 1
	addi x6, x0, 1531
	and x5, x22, x20
	mulhsu x25, x21, x21
	la x1, test_memory+2360
	sll x29, x29, 63
	addi x19, x0, -1289
	addi x10, x0, -1951
	addi x26, x0, -917
	addw x14, x9, x9
	mulw x22, x10, x10
	sb x19, -218(x3)
	bltu x18, x4, crash_backward
	sllw x11, x19, x19
	lh x7, -1338(x1)
	or x2, x11, x15
	addi x28, x0, 437
	divu x31, x6, x28
	addi x8, x0, -1
	xor x8, x8, x29
	and x16, x26, x8
	sllw x27, x11, x11
	or x23, x16, x29
	la x12, test_memory-961
	beq x16, x23, crash_backward
	addi x13, x0, 272
	addi x30, x0, 232
	addi x14, x0, 995
	and x24, x26, x13
	addi x5, x0, -808
	la x7, test_memory+1768
	addi x25, x0, 637
	divuw x9, x10, x10
	lh x21, -1142(x7)
	mul x16, x14, x14
	sll x28, x22, x29
	la x21, test_memory+2769
	addi x1, x0, -1301
	and x8, x5, x1
	sltiu x11, x31, -844
	remu x2, x19, x19
	addi x6, x0, 1853
	addi x22, x0, 1096
	sb x22, 970(x12)
	sll x18, x22, x22
	mulh x20, x16, x16
	addi x17, x30, 712
	addi x26, x0, -608
	lb x9, -2022(x21)
	mulh x31, x25, x25
	addw x10, x23, x22
	srai x27, x4, 47
	addi x3, x0, 1
	remw x24, x26, x26
	sll x3, x3, 63
	addi x23, x0, -1
	xor x23, x23, x3
	and x29, x4, x23
	slt x4, x6, x6
	or x15, x29, x3
	la x12, test_memory-1651
	lw x13, 1671(x12)
	mulhu x7, x28, x7
	addi x22, x0, -304
	srai x27, x18, 15
	la x16, test_memory+1366
	xori x4, x24, -109
	lhu x2, -1172(x16)
	bge x15, x29, crash_backward
	rem x5, x5, x8
	la x26, test_memory+1142
	div x30, x12, x4
	la x29, test_memory-457
	addi x24, x0, 1389
	add x13, x31, x31
	addi x8, x0, -371
	sllw x31, x8, x8
	mulhsu x9, x24, x24
	addi x19, x0, 1542
	la x28, test_memory+2352
	sd x13, -1744(x28)
	la x17, test_memory+1082
	la x15, test_memory-661
	sd x4, 1417(x29)
	lb x10, -528(x26)
	addi x12, x0, -51
	addi x3, x0, -1406
	sh x10, -516(x17)
	la x25, test_memory-430
	lb x4, 1445(x15)
	divuw x27, x9, x9
	sltu x14, x22, x19
	la x23, test_memory+2659
	addi x8, x0, 1563
	addi x18, x0, 1
	la x2, test_memory+2562
	addi x24, x8, 0
	addi x29, x0, -1952
	addi x10, x24, 0
	or x5, x3, x3
	bne x24, x10, crash_forward
	srlw x21, x8, x14
	addi x28, x0, -1054
	addi x6, x12, -1949
	xor x13, x8, x8
	sll x18, x18, 63
	blt x9, x9, crash_forward
	remu x13, x26, x5
	lb x7, -2025(x23)
	addi x16, x0, -1018
	addi x17, x16, -230
	la x14, test_memory+278
	bltu x12, x6, crash_backward
	la x22, test_memory+2024
	slt x31, x10, x27
	addi x11, x0, -1
	xor x7, x0, x0
	la x21, test_memory+1981
	lw x8, -1457(x21)
	remu x5, x30, x30
	xor x11, x11, x18
	or x9, x24, x24
	and x20, x1, x11
	sb x4, -1866(x2)
	addi x24, x0, -559
	rem x10, x12, x12
	sd x8, 606(x25)
	la x19, test_memory-1042
	lwu x27, -1720(x22)
	lbu x15, 49(x14)
	sll x13, x23, x23
	or x1, x7, x18
	addi x8, x0, -335
	la x30, test_memory-19
	sw x10, 1362(x19)
	addi x4, x0, 801
	remw x3, x24, x4
	sw x6, 67(x30)
	sra x16, x8, x8
	addi x23, x0, 1535
	la x1, test_memory+1705
	mulhu x9, x31, x31
	la x4, test_memory-535
	addi x17, x0, -808
	la x2, test_memory-145
	remuw x26, x29, x28
	addi x27, x0, -1322
	addw x7, x24, x24
	addi x21, x17, -319
	sh x6, 857(x2)
	la x12, test_memory+2532
	slli x16, x10, 58
	addi x13, x0, 751
	or x29, x16, x16
	la x25, test_memory-1383
	la x9, test_memory+1200
	la x19, test_memory+1487
	or x20, x13, x13
	lw x3, -1936(x12)
	la x30, test_memory+2105
	la x11, test_memory-258
	lw x15, 1359(x4)
	addi x14, x0, 0
	mulhsu x5, x23, x23
	srl x6, x28, x28
	mul x31, x8, x27
	lh x22, 1945(x25)
	sb x18, -659(x19)
	lbu x26, -590(x9)
	addi x28, x0, 802
	lw x10, -1553(x1)
	sh x8, 414(x11)
	sltiu x4, x7, 1752
	la x12, test_memory-593
	addi x9, x0, 90
	la x19, test_memory-669
	sllw x20, x4, x4
	addi x23, x0, 281
	addi x26, x0, -1541
	addi x24, x0, 0
	la x10, test_memory+280
	addi x31, x28, 0
	remw x16, x29, x5
	addi x5, x0, -1466
	sh x3, -1735(x30)
	remw x18, x28, x28
	bne x0, x0, crash_backward
	mulhu x6, x26, x21
	sh x29, 723(x12)
	bltu x14, x24, crash_forward
	addi x1, x9, 1993
	blt x1, x9, crash_forward
	remw x18, x11, x0
	la x25, test_memory+1657
	lbu x13, -1037(x25)
	sub x17, x23, x23
	addi x4, x0, -876
	addi x15, x0, 1226
	lwu x7, 88(x10)
	addi x3, x31, 0
	srai x21, x27, 19
	lwu x27, 1273(x19)
	bne x0, x0, crash_forward
	la x24, test_memory+1748
	bne x25, x25, crash_backward
	la x22, test_memory-1649
	rem x6, x4, x4
	addi x9, x0, 129
	la x14, test_memory+825
	sra x12, x9, x9
	sub x2, x26, x26
	lw x1, -1440(x24)
	remw x11, x5, x15
	addi x28, x0, -664
	addi x20, x0, 1105
	remu x18, x29, x30
	addi x4, x0, -446
	mulhu x30, x28, x20
	addi x26, x0, -514
	srliw x6, x7, 31
	addi x12, x0, 1300
	slti x17, x23, 1363
	srli x31, x21, 43
	addi x2, x0, -113
	sb x23, -517(x14)
	la x11, test_memory+130
	la x10, test_memory-1118
	la x8, test_memory+1566
	sb x13, 1676(x10)
	lb x29, 1669(x22)
	sh x27, -1544(x8)
	la x16, test_memory-349
	bne x0, x0, crash_forward
	la x5, test_memory+960
	srlw x25, x24, x24
	mulhsu x7, x4, x2
	lw x9, -236(x5)
	addi x31, x0, 1480
	la x1, test_memory-1065
	lb x30, 1133(x1)
	addi x18, x0, 396
	addi x8, x0, 422
	ori x20, x18, 1559
	la x10, test_memory+1696
	addi x24, x0, -954
	la x30, test_memory-462
	srlw x1, x26, x19
	mulhu x5, x23, x23
	la x25, test_memory+1875
	sd x20, -1672(x10)
	slt x23, x7, x13
	addi x20, x0, 1
	la x5, test_memory+1990
	rem x28, x18, x18
	remu x14, x8, x8
	ld x4, 1070(x30)
	remu x29, x31, x24
	sd x23, -1654(x5)
	addi x1, x14, 0
	la x22, test_memory-988
	la x28, test_memory+494
	remuw x18, x16, x14
	remu x27, x12, x4
	sb x7, -1366(x25)
	addi x24, x0, 835
	sll x20, x20, 63
	addi x31, x0, -1756
	lw x14, -254(x28)
	addi x2, x0, -1
	addi x29, x0, -639
	lh x9, 1792(x22)
	addi x17, x1, 0
	sltu x21, x12, x12
	addi x8, x29, -137
	xor x2, x2, x20
	la x5, test_memory+1676
	sh x12, 811(x16)
	and x6, x18, x2
	addi x15, x0, 1394
	addw x30, x24, x24
	sb x31, -684(x5)
	sraiw x3, x19, 4
	addi x21, x0, 1
	srl x10, x31, x31
	addi x12, x0, 337
	addi x4, x12, 1534
	mulh x19, x26, x15
	la x25, test_memory-1377
	lw x13, 330(x11)
	sll x21, x21, 63
	addi x27, x0, 1
	beq x12, x4, crash_backward
	sll x27, x27, 63
	addi x14, x0, -1
	xor x14, x14, x21
	la x24, test_memory+1448
	or x7, x22, x20
	addi x26, x0, 0
	addi x12, x0, 296
	and x5, x5, x14
	sd x0, 1897(x25)
	la x29, test_memory+53
	blt x2, x2, crash_backward
	sw x20, -588(x24)
	addi x23, x0, -1
	and x13, x12, x12
	la x22, test_memory+411
	or x3, x4, x21
	ld x4, 171(x29)
	ld x9, 445(x22)
	la x16, test_memory-1666
	xor x23, x23, x27
	addi x31, x0, 0
	blt x26, x31, crash_forward
	and x28, x22, x23
	or x18, x28, x27
	bge x18, x28, crash_forward
	srlw x30, x9, x9
	la x15, test_memory+795
	lwu x19, 1866(x16)
	sd x27, -595(x15)
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
	sd x17, 136(x1)
	sd x18, 144(x1)
	sd x19, 152(x1)
	sd x20, 160(x1)
	sd x21, 168(x1)
	sd x23, 184(x1)
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
reg_x0_init:	.dword 0x7e627b6e098db899
reg_x1_init:	.dword 0xeee26ae1737fe8c5
reg_x2_init:	.dword 0xffffffffffff8009
reg_x3_init:	.dword 0xffffffffffffff80
reg_x4_init:	.dword 0x0000000000000006
reg_x5_init:	.dword 0x15bf889cc433fee3
reg_x6_init:	.dword 0x49a70110c9ef0a0d
reg_x7_init:	.dword 0xffffffffffffff81
reg_x8_init:	.dword 0xffffffff80000006
reg_x9_init:	.dword 0x2d170d3c28b80e40
reg_x10_init:	.dword 0xa0be0158aa880748
reg_x11_init:	.dword 0x93e2babf4e4a7617
reg_x12_init:	.dword 0x13109edf68817444
reg_x13_init:	.dword 0xffffffffffff8005
reg_x14_init:	.dword 0x0800000000000003
reg_x15_init:	.dword 0xffffffff80000006
reg_x16_init:	.dword 0x0000000000000000
reg_x17_init:	.dword 0x44726c61b7b59fc0
reg_x18_init:	.dword 0xffffffff80000004
reg_x19_init:	.dword 0xe33cfc6afbf4b28e
reg_x20_init:	.dword 0xffffffffffffffef
reg_x21_init:	.dword 0xf0684c5e1fe207c6
reg_x22_init:	.dword 0x0b8d5e6d4352e606
reg_x23_init:	.dword 0x7444716325ba98e8
reg_x24_init:	.dword 0xc3fb9407c2cf7682
reg_x25_init:	.dword 0xffffffffffff8007
reg_x26_init:	.dword 0x0000000000000001
reg_x27_init:	.dword 0xffffffff80000004
reg_x28_init:	.dword 0xc9ed9f8579b7f81f
reg_x29_init:	.dword 0xa31fd090d8ec2488
reg_x30_init:	.dword 0x80b966e252a7a2c5
reg_x31_init:	.dword 0xc9735bfb303faeae

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0x9b2fba60c4b9985d
reg_x1_output:	.dword 0xb0b3d4bbb1768ffa
reg_x2_output:	.dword 0x53332c9333ff89cf
reg_x3_output:	.dword 0x0896ee0e15049fc4
reg_x4_output:	.dword 0xccf60003d329f439
reg_x5_output:	.dword 0x27f71e5c887d49d2
reg_x6_output:	.dword 0xc781a0ced59b5979
reg_x7_output:	.dword 0x3e4e4270c5b81479
reg_x8_output:	.dword 0xf040e5fcc252b6cf
reg_x9_output:	.dword 0x61f06bb376e4ce38
reg_x10_output:	.dword 0x47a4893a836e347b
reg_x11_output:	.dword 0xb7ae00ffdb81fffc
reg_x12_output:	.dword 0x176ae5cd5936aba5
reg_x13_output:	.dword 0x6f3698bf70d1bf9f
reg_x14_output:	.dword 0x2b3032c243c3267c
reg_x15_output:	.dword 0xfc06e035066aa6b1
reg_x16_output:	.dword 0x448bac697591bea0
reg_x17_output:	.dword 0xf47d24176d1af17b
reg_x18_output:	.dword 0xaf5161035f657dc4
reg_x19_output:	.dword 0xc6554e5f8d300a40
reg_x20_output:	.dword 0x5fd794b8a88f248f
reg_x21_output:	.dword 0xe2866d64f99504c6
reg_x22_output:	.dword 0x4f99f0cfd8c0fbc3
reg_x23_output:	.dword 0x5f8918259b5ece14
reg_x24_output:	.dword 0x7b83f219e7ec13a0
reg_x25_output:	.dword 0x29af43e66d85147c
reg_x26_output:	.dword 0x4dcf4aaf47a7958a
reg_x27_output:	.dword 0x52ab5efc4ef32bdb
reg_x28_output:	.dword 0xa2fa2add1e890be9
reg_x29_output:	.dword 0xa4edc4eb120c721f
reg_x30_output:	.dword 0x7924a55c52dec450
reg_x31_output:	.dword 0x5a5cdfb04873f809

// Memory Blocks
	.align 8
test_memory:
	.dword 0xa263a2c605abafe0, 0x595d8a5b009f7233
	.dword 0x288b184542d665ee, 0x1c6688e12cb9b654
	.dword 0x0ad8758cd6732ce3, 0xf0b3292ea7d948c3
	.dword 0x67017e0d732b2d64, 0x655661827bd3be39
	.dword 0x36bb0160114133b2, 0x0630fff4df3ef5da
	.dword 0x840e2708bad6a352, 0x1b62bf5b5cbd6f76
	.dword 0x390a415ecf1980f0, 0x76f7554f32c3420b
	.dword 0x95cc5bc63d2eb67f, 0x0d0dcd8781d5768e
	.dword 0x71b4f81ecf39f5a5, 0x67c9c670971dcaea
	.dword 0xfd37af817816dc56, 0x154362f816492148
	.dword 0xf837aa27b96d3fbe, 0x1ba405a508471f91
	.dword 0xa89f22acce04c164, 0xcbeb28eeb8e5c330
	.dword 0x2d0f6876dbda128c, 0x07b7e8c9ababed1c
	.dword 0xa36a15713cba89dc, 0x1f291183e5022a15
	.dword 0x89cb6afd0150ef41, 0xcaaec7d0efe93b2d
	.dword 0x7d990a276bd8a213, 0xbec61e23ce722289
	.dword 0x36c77b1cdb5a7d76, 0xce482b3ecc23b869
	.dword 0x38ac37dec0a91f04, 0x387b760ca1b60c65
	.dword 0x04d92e31e18873a8, 0x63afcaaeb14c16f8
	.dword 0xb2d9ecd9aec6aecc, 0x0119ccd44dd87f42
	.dword 0x2879f00775cb0fb6, 0x1c24db4cf7e27909
	.dword 0xfcbec10f0f81192f, 0x6bc718e079abff00
	.dword 0x7b37dd5c93cd1f65, 0xf8ccae5a950aed4c
	.dword 0xa0f198a8e4215012, 0xbdcc99ec0a5ac043
	.dword 0x17776e694f9898dc, 0xcdca9fafaa04fb76
	.dword 0xa8257685896f0ffe, 0x22af2f88ad7a7cf1
	.dword 0xd9cff151ee05c328, 0xddf75433115840c0
	.dword 0x0fc31eba0d1a10a4, 0x418bff992d1658b5
	.dword 0xb28cd4b76fb6eeb9, 0x45d1486565481c69
	.dword 0x7c24890a07e8c554, 0x99f36cd4f060d57f
	.dword 0xb91dc227fda2bde3, 0x4580aed51b606c2f
	.dword 0x2adc237219cead84, 0x9bbc5d48efffd802
	.dword 0xa27f88a7c46efd5f, 0xdb089ea9392d58da
	.dword 0x8cb1e49ee74c354f, 0xa289d0d29124bc35
	.dword 0x92e7d732721e0cc7, 0x66ff921ad67032b2
	.dword 0x7a402e7641ba25f3, 0x9afcc7a74ee279d3
	.dword 0x423dc730b7d0d71d, 0x476934fa19635e03
	.dword 0xa95a808af662a652, 0x1ccc78ccd573d8db
	.dword 0x12293705e79f5b44, 0x6d8b832499df4fa0
	.dword 0xe4a7faaa9a89cb72, 0x323ed8a13763b610
	.dword 0x03c2f48504c9c486, 0xf4d937142072995d
	.dword 0x8a1baf528cc7b8fd, 0xdabb6f5330c95779
	.dword 0x722fb77862c4130c, 0xaa4b884e86bf0694
	.dword 0x0034c6364e5651c2, 0x93727f65010ad0e2
	.dword 0x16afec1b3dde5469, 0x44c539f416adc8a1
	.dword 0x25306eba49347832, 0xd6527c303fd7785a
	.dword 0x21ee4d9d8e8b6c10, 0xc858f935264cb366
	.dword 0x3697a27b1240dee3, 0x8cc5d05f364c6ab3
	.dword 0x259750a6b6886bd9, 0x2f8d0bd7d66689c8
	.dword 0x52d2b7c738ae6911, 0xe8f2f470b1752006
	.dword 0x20835dcc8d667c80, 0xfef64eb4ca285a30
	.dword 0x81acc420be741b18, 0xf578d53af79a102c
	.dword 0x3efddc1dc0395626, 0xd8c4843c6665eb0a
	.dword 0x23f0cebf679a9afb, 0x70e18a63860f6745
	.dword 0xc7f30b996e6c48ce, 0x7f19f2eba74f3749
	.dword 0xc58ad30c288940e0, 0x37455ce78175ca35
	.dword 0x3f0eafb56bffd4e1, 0xf54853dce3a8fae1
	.dword 0x90d693261db4b792, 0x91d81d964e9f2b22
	.dword 0xfb1589d897b1d3ab, 0x994d1136e4da4f4c
	.dword 0x0d063a60a1512cfe, 0x415acb919e89adf8
	.dword 0x4f03a3e141d22fdb, 0x2026d4b893615806
	.dword 0x64cacfc245ea12b6, 0xfdab8ad354229ce5
	.dword 0xebb96a9fb6c62e07, 0x58de66331780ff11
	.dword 0x2da87883b7016e71, 0x71edeaa60ec36cdd

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
