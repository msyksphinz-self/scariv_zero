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
	la x17, test_memory+717
	la x9, test_memory-388
	la x8, test_memory+362
	addi x2, x0, -1278
	mulhu x27, x23, x11
	addi x25, x0, -757
	addi x20, x2, -76
	lwu x18, -541(x17)
	bgeu x20, x2, crash_forward
	addi x19, x0, -1718
	la x21, test_memory+415
	addi x4, x0, 491
	lwu x26, 453(x21)
	sllw x12, x5, x5
	la x16, test_memory+761
	mul x7, x4, x4
	addi x30, x0, 0
	mulh x6, x30, x20
	addi x14, x0, 0
	lwu x1, 326(x8)
	sll x15, x25, x25
	addi x6, x0, -97
	mulw x5, x9, x9
	addw x12, x6, x6
	lw x11, 468(x9)
	addi x24, x0, -1381
	addi x21, x0, -723
	divu x10, x19, x19
	addi x23, x0, -659
	la x5, test_memory-514
	la x27, test_memory+983
	addi x8, x0, -618
	la x15, test_memory+811
	la x3, test_memory+449
	sra x26, x2, x25
	lbu x9, -768(x27)
	or x2, x11, x26
	addi x11, x0, 1119
	addi x29, x24, -779
	addi x26, x0, 0
	lbu x31, -407(x16)
	la x6, test_memory+1785
	sh x0, -1255(x6)
	lhu x12, 1048(x5)
	la x17, test_memory+1702
	addi x13, x0, 1195
	or x4, x21, x21
	lw x7, -714(x17)
	mulh x22, x23, x13
	addi x16, x0, -100
	addi x9, x0, -801
	addi x31, x0, 893
	addi x27, x0, 0
	addi x19, x0, 1457
	rem x6, x12, x12
	slt x18, x8, x8
	addi x24, x0, -1516
	addi x30, x0, 0
	divw x29, x24, x24
	bltu x27, x30, crash_backward
	sd x7, -89(x3)
	subw x28, x11, x11
	la x12, test_memory-1527
	ld x25, -603(x15)
	remu x17, x21, x24
	addi x4, x0, 1907
	addi x20, x0, -2006
	addi x1, x20, -78
	addi x2, x0, 0
	mulw x14, x9, x19
	addi x7, x0, 1116
	add x5, x31, x7
	sllw x21, x16, x4
	bge x1, x20, crash_backward
	ld x10, 1959(x12)
	rem x30, x5, x0
	divw x17, x27, x9
	la x16, test_memory+2771
	la x9, test_memory+471
	add x5, x2, x2
	slliw x6, x18, 16
	la x19, test_memory+955
	rem x22, x28, x21
	lh x26, 13(x19)
	la x31, test_memory-694
	addi x11, x0, 564
	addi x14, x0, -774
	la x15, test_memory+1088
	la x17, test_memory+1718
	addi x28, x0, -2002
	lh x2, -365(x9)
	la x25, test_memory-424
	addi x20, x0, 466
	la x3, test_memory+889
	addw x30, x4, x0
	la x13, test_memory-697
	addi x9, x0, 282
	slt x24, x12, x12
	addi x12, x0, -714
	xori x26, x30, -593
	sd x24, -1302(x17)
	sw x21, -788(x15)
	sb x22, -743(x3)
	la x2, test_memory+1575
	sw x26, 769(x13)
	addi x24, x0, 730
	la x27, test_memory+1396
	addi x17, x0, 236
	and x3, x17, x17
	lbu x30, -938(x2)
	addi x22, x0, -640
	addi x19, x0, 411
	sub x26, x6, x5
	div x29, x11, x14
	or x5, x9, x22
	ld x7, -612(x27)
	sra x21, x20, x12
	addi x21, x0, 943
	la x26, test_memory-389
	sd x6, -1843(x16)
	divuw x2, x31, x23
	sraw x15, x24, x24
	srli x29, x3, 24
	sh x4, 613(x26)
	addi x20, x0, -1676
	sw x22, 1016(x25)
	divuw x6, x19, x19
	addi x1, x0, -695
	addi x4, x0, 1
	addi x2, x0, -528
	addw x27, x21, x20
	sd x0, 1286(x31)
	la x3, test_memory+960
	addi x5, x0, -1305
	addi x11, x0, -788
	addi x30, x0, 408
	la x14, test_memory-1363
	sll x4, x4, 63
	sb x20, -698(x3)
	addi x12, x0, 0
	or x22, x5, x5
	addi x21, x0, 0
	sub x9, x11, x30
	addi x27, x0, 1
	sltu x17, x30, x10
	srai x20, x13, 40
	addi x15, x0, -12
	mulw x18, x28, x1
	ld x13, 1779(x14)
	addi x23, x0, -1
	addi x25, x0, 1915
	la x29, test_memory+130
	addi x26, x0, 917
	blt x12, x21, crash_forward
	sll x27, x27, 63
	addi x9, x0, 328
	addi x11, x0, -1109
	addi x18, x0, 539
	xor x16, x15, x26
	la x31, test_memory-723
	xor x23, x23, x4
	addi x1, x0, -448
	addi x22, x1, -1719
	addi x19, x0, -1
	addi x14, x0, 384
	and x8, x8, x23
	or x10, x8, x4
	lw x3, 314(x29)
	sb x18, 1167(x31)
	divuw x28, x9, x14
	addi x13, x0, 0
	slt x5, x11, x11
	la x29, test_memory+8
	sraw x12, x18, x18
	la x23, test_memory+630
	sub x5, x30, x30
	lhu x16, 694(x29)
	addi x20, x18, 777
	mulh x29, x7, x7
	addi x8, x0, -243
	bltu x11, x11, crash_backward
	slt x28, x8, x8
	addi x4, x0, -30
	addi x8, x0, 1618
	sltu x28, x8, x8
	xor x19, x19, x27
	la x21, test_memory+2075
	sb x3, -264(x23)
	mulhu x3, x4, x4
	la x22, test_memory-77
	add x5, x21, x10
	and x6, x17, x19
	lb x1, 875(x22)
	sraw x24, x2, x25
	addi x1, x0, -1516
	or x7, x6, x27
	sra x5, x1, x1
	addi x30, x0, 0
	bltu x13, x30, crash_backward
	addi x5, x0, 1
	la x23, test_memory+2935
	sb x14, -1465(x21)
	la x8, test_memory-1761
	addi x22, x0, -1145
	addi x3, x22, -1159
	la x16, test_memory+614
	bge x7, x6, crash_backward
	lbu x4, -1984(x23)
	bge x18, x20, crash_forward
	addiw x17, x28, 815
	addi x14, x0, -1182
	addi x24, x0, 190
	lbu x12, 404(x16)
	la x30, test_memory-274
	ld x21, 530(x30)
	lbu x28, 1776(x8)
	remu x23, x4, x4
	div x18, x21, x21
	addi x18, x0, 1235
	sll x5, x5, 63
	addi x3, x0, 1442
	sltu x16, x19, x19
	addi x28, x0, 1
	addi x13, x0, -1
	mulh x4, x6, x26
	sll x28, x28, 63
	addi x12, x0, -1
	addi x20, x0, -1171
	addi x17, x0, 1240
	sra x4, x3, x3
	addi x16, x13, 0
	addi x6, x17, 1197
	divuw x30, x18, x18
	remu x29, x21, x21
	remw x7, x20, x20
	xor x13, x13, x5
	and x1, x0, x13
	addi x22, x0, -475
	mulhsu x21, x3, x22
	addi x11, x0, 1151
	addi x27, x16, 0
	addi x15, x0, 1
	mulhsu x2, x24, x24
	la x19, test_memory-1796
	and x10, x14, x11
	xor x12, x12, x28
	sd x28, 2020(x19)
	bne x16, x27, crash_backward
	and x23, x27, x12
	sll x15, x15, 63
	or x25, x27, x5
	addi x9, x0, -1
	addi x18, x0, 1435
	add x4, x19, x19
	divu x25, x4, x4
	addi x13, x18, 1778
	addi x1, x0, -1331
	addi x20, x0, -1284
	sltu x24, x10, x22
	xor x9, x9, x15
	la x30, test_memory+1169
	srlw x17, x28, x25
	addi x16, x0, 1821
	div x11, x12, x12
	addi x2, x0, -1343
	sll x5, x1, x1
	la x29, test_memory+2001
	addi x4, x0, 852
	and x31, x14, x9
	addi x17, x0, -1700
	addi x21, x2, -1201
	or x8, x9, x28
	beq x23, x8, crash_forward
	addi x7, x0, 1305
	bge x18, x13, crash_forward
	sltiu x22, x28, 1374
	srl x25, x4, x7
	lw x14, -1625(x29)
	addi x6, x0, 1421
	addi x10, x0, 351
	addi x29, x0, 1439
	la x13, test_memory+688
	sraw x18, x29, x29
	la x7, test_memory+2729
	addi x24, x17, -1239
	addw x4, x28, x28
	blt x17, x24, crash_backward
	or x26, x31, x15
	addi x1, x0, -152
	addi x8, x0, 1020
	sb x23, -737(x30)
	addi x4, x0, -902
	addi x5, x0, -629
	slti x3, x20, 1321
	srliw x22, x4, 28
	sltu x11, x1, x5
	addi x12, x0, -1195
	subw x27, x20, x6
	la x24, test_memory-1535
	mulhsu x23, x8, x12
	bltu x26, x31, crash_forward
	lw x25, 1615(x24)
	lw x14, -368(x13)
	la x17, test_memory-982
	addi x29, x0, -1636
	sd x16, 1566(x17)
	la x3, test_memory+2268
	la x11, test_memory-1335
	sub x18, x4, x29
	sw x21, -1888(x3)
	lwu x28, -1861(x7)
	addi x20, x0, 1
	or x1, x24, x24
	addi x31, x0, -163
	sra x17, x31, x31
	mulh x13, x0, x0
	addi x27, x0, -556
	lh x8, 1489(x11)
	addi x30, x0, -1957
	addi x24, x0, 799
	addi x4, x0, 578
	ori x29, x3, -1871
	addi x22, x27, -252
	addi x23, x0, 1
	sll x20, x20, 63
	addi x14, x0, 1547
	or x2, x30, x14
	lui x6, 795134
	addi x26, x24, 1468
	sub x18, x4, x4
	addi x28, x0, -1795
	addi x9, x0, -1
	addi x29, x28, -757
	sll x23, x23, 63
	addi x15, x0, -1
	addi x3, x0, -361
	addi x11, x0, 1
	sll x11, x11, 63
	xor x15, x15, x23
	mulhsu x14, x4, x4
	and x21, x8, x15
	sraw x7, x3, x3
	la x2, test_memory+1456
	addi x8, x0, -1976
	sw x18, -728(x2)
	addi x28, x0, -258
	srl x19, x16, x10
	addi x14, x0, 741
	xor x9, x9, x20
	divuw x2, x28, x28
	addi x1, x0, -1
	and x25, x31, x9
	mulhu x24, x31, x19
	addi x10, x0, -636
	or x5, x21, x23
	la x19, test_memory+2581
	or x12, x28, x20
	addi x17, x8, -966
	la x30, test_memory-1168
	lb x2, -2033(x19)
	and x16, x10, x10
	xor x3, x14, x14
	la x24, test_memory-22
	beq x25, x12, crash_backward
	la x23, test_memory-44
	addi x29, x0, -804
	bge x17, x8, crash_backward
	or x28, x31, x31
	xor x1, x1, x11
	addi x16, x0, -146
	addi x8, x0, -374
	addi x20, x0, -1220
	addi x12, x16, -469
	la x14, test_memory-52
	sd x27, 662(x24)
	mulhu x6, x6, x6
	lw x3, 788(x23)
	lwu x5, 764(x14)
	blt x16, x12, crash_backward
	slt x7, x29, x29
	divw x25, x3, x3
	addi x9, x0, -1019
	la x19, test_memory+1631
	sraw x2, x31, x10
	divuw x15, x9, x9
	sh x18, -1323(x19)
	la x22, test_memory+2339
	addi x26, x0, -1080
	ld x27, 1856(x30)
	mulhu x18, x21, x16
	sh x26, -1645(x22)
	slt x30, x20, x12
	slliw x29, x28, 16
	addi x16, x0, 1312
	divuw x17, x8, x20
	addi x27, x0, 650
	addi x14, x0, -770
	addi x15, x0, -1266
	addi x6, x0, 1
	sllw x23, x16, x14
	rem x18, x13, x9
	addi x9, x0, -1460
	addi x4, x26, -583
	sub x3, x12, x12
	addi x19, x27, 1475
	srlw x5, x15, x9
	addi x10, x0, 545
	bltu x26, x4, crash_forward
	sll x6, x6, 63
	addi x28, x0, -1
	and x31, x5, x1
	addi x25, x0, -376
	xor x28, x28, x6
	and x12, x1, x28
	addi x24, x0, -1183
	remw x7, x25, x24
	or x13, x31, x11
	addi x21, x10, 856
	beq x10, x21, crash_backward
	or x22, x11, x6
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
reg_x0_init:	.dword 0x239c922365786f2e
reg_x1_init:	.dword 0xffffffffffffff86
reg_x2_init:	.dword 0x8676e4083d622020
reg_x3_init:	.dword 0x0000000000000000
reg_x4_init:	.dword 0xffffffffffff8005
reg_x5_init:	.dword 0xae8ccf5abee5b33d
reg_x6_init:	.dword 0xffffffffffff8001
reg_x7_init:	.dword 0xc491cf7650a7e8ee
reg_x8_init:	.dword 0x1e47a71a29741955
reg_x9_init:	.dword 0xa40e72c3e0d55ffa
reg_x10_init:	.dword 0x98d35676771a575e
reg_x11_init:	.dword 0xffffffffffffffff
reg_x12_init:	.dword 0x5a3629feba4f7a39
reg_x13_init:	.dword 0xb56f47615452b4a5
reg_x14_init:	.dword 0x0000000000000008
reg_x15_init:	.dword 0xffffffffffffffff
reg_x16_init:	.dword 0xffffffffffffffff
reg_x17_init:	.dword 0xffffffffffff8006
reg_x18_init:	.dword 0xfab64d7f8485af73
reg_x19_init:	.dword 0xffffffffffffffff
reg_x20_init:	.dword 0x7b52a9a7fec4c5d5
reg_x21_init:	.dword 0xffffffffffff8004
reg_x22_init:	.dword 0xffffffffffffffff
reg_x23_init:	.dword 0xffffffff80000008
reg_x24_init:	.dword 0x0800000000000000
reg_x25_init:	.dword 0x3ed66843452f17a8
reg_x26_init:	.dword 0xffffffffffffffff
reg_x27_init:	.dword 0x96f30ff5d5e59120
reg_x28_init:	.dword 0x4da0026ed20fc819
reg_x29_init:	.dword 0xa747d790483dd4ad
reg_x30_init:	.dword 0x73d64670b231dc2e
reg_x31_init:	.dword 0xffffffffffffff86

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0x6d5e596484afe08c
reg_x1_output:	.dword 0xec36b75020e561ec
reg_x2_output:	.dword 0xded010efa532d98d
reg_x3_output:	.dword 0x4d3029fd92f7afa0
reg_x4_output:	.dword 0x8de228cc66ba7f8d
reg_x5_output:	.dword 0x40683945d727820b
reg_x6_output:	.dword 0xdb413f9969ab11e4
reg_x7_output:	.dword 0x0f25bace107dba06
reg_x8_output:	.dword 0x05a6e4eb89febfd4
reg_x9_output:	.dword 0x645fed51c379dacf
reg_x10_output:	.dword 0x02faab660b085311
reg_x11_output:	.dword 0x7d83aad825132230
reg_x12_output:	.dword 0x98a9c80167577e83
reg_x13_output:	.dword 0x621d0a26a3f07ee0
reg_x14_output:	.dword 0xec08d2ad7dccd549
reg_x15_output:	.dword 0x34f523789ebf0928
reg_x16_output:	.dword 0x44b87c1b4947ae01
reg_x17_output:	.dword 0x1dfaec6e8ee4e1c9
reg_x18_output:	.dword 0x213f4cd746387646
reg_x19_output:	.dword 0x76495f438a489b1c
reg_x20_output:	.dword 0xc697c19c35063a79
reg_x21_output:	.dword 0xe60c6144afc3907b
reg_x22_output:	.dword 0x6f9358e321de65c4
reg_x23_output:	.dword 0xda291c804a57cfdf
reg_x24_output:	.dword 0x55e865bbde71fe5c
reg_x25_output:	.dword 0xe4a5c0ba8da879ca
reg_x26_output:	.dword 0x35c9bbe14893e205
reg_x27_output:	.dword 0x3a17dfa83cbdbb67
reg_x28_output:	.dword 0x3344890875dfc6db
reg_x29_output:	.dword 0xff1fd855310bc6ef
reg_x30_output:	.dword 0x4f91ef78d0ca044e
reg_x31_output:	.dword 0x9e6b05e915466e4d

// Memory Blocks
	.align 8
test_memory:
	.dword 0xd94f35df4af4686d, 0x011da58d24014404
	.dword 0x7e68a06273a49d68, 0x8c20a7a6dfb66650
	.dword 0x3eb046f3b3fce34f, 0xf3dee04d76cc588b
	.dword 0x63db7cea65602220, 0xc0c04af86cd58ed2
	.dword 0x9c369dcf657697ff, 0x28695576a8ca8fe8
	.dword 0x3a08537536d8a7c7, 0x45af6626c8a9d159
	.dword 0x979aa94c69b98bc1, 0xca93116093f6b1e2
	.dword 0x787180f5bd43f0b2, 0xc7a3b2323a433610
	.dword 0x889b3c1a34f6bd1a, 0xca375a513f866b26
	.dword 0x7c81af76cd7088bb, 0x4a1d4d4d37bb9443
	.dword 0xcb6eb33be5fc8857, 0x87207b05cc6485c4
	.dword 0x1e58e497301bf1be, 0xa212ad5cab4bd2e6
	.dword 0xb8c26c8ba0731c07, 0xf3705d2e8489b1b0
	.dword 0xd3bce0069531e01d, 0x9e38627de098b90f
	.dword 0xe8c28d331182fd7d, 0xcf91f3f17475dd42
	.dword 0xa446ca0c7406873d, 0x668ea97e73994e78
	.dword 0xdbe418329c179d4f, 0x39fd7664dc4c1db6
	.dword 0xbb2831ffb6ddf607, 0x681ece5ea4b8cbfe
	.dword 0x016b54dd5e2ffbda, 0x0c596a17345327ad
	.dword 0xd4215cd0c8528367, 0x15125ed888161c24
	.dword 0x58e8855b3cef5dbb, 0x66c27d8876dc57ab
	.dword 0x1a82e381196c4ad0, 0xdc8e2cd4a002eb91
	.dword 0x9924ed2769601057, 0x594432acdfd34a97
	.dword 0x5254a1a47f7bb8b7, 0x00fb20f29524498d
	.dword 0xdc3a27925c1a3e54, 0xd2cc596f5878063d
	.dword 0x4cfbf3e4d9092714, 0x5ea6dd04e8d6d888
	.dword 0x4dcdce3e1a40d41e, 0xdc235a295405b1cf
	.dword 0xbbfb4681416b89e4, 0xc7e62e91b0b88e94
	.dword 0x3dab6fa3b2867463, 0xacb3502cf847de60
	.dword 0x6da4f3c9bad82ba9, 0x57235153a47a05e6
	.dword 0x4636d590452c7c97, 0x5627f43f0b605f68
	.dword 0xe0db72a49efd79e8, 0xfa8201ba09595d59
	.dword 0xeb709b9e962e1971, 0x9b315718463fb343
	.dword 0xe638d50d567ae1aa, 0x88035f6750e8a8ea
	.dword 0x348715c81d096b6c, 0x04f36be45991fbb2
	.dword 0xb637968dcfc7bbfc, 0xdc539fb09301f23d
	.dword 0x472d86cfc1d8bb47, 0x71ec62c529228658
	.dword 0x7d36bac9ee5b4a6f, 0xe1ab9023650ac917
	.dword 0xf933a6d3fbadbe86, 0x285bd34e7ff7e53d
	.dword 0xdf733bf7b327c398, 0xdf6fe8faf2e963e2
	.dword 0xa21779c2d060ebee, 0xed74b707c5aa974f
	.dword 0x6050c9602fba6f91, 0x1e786faba84d502c
	.dword 0x338b75e24a46e00c, 0xc1e433f00bb840dc
	.dword 0xe98bd5e06d92d476, 0xc128e95e2b2db328
	.dword 0xc52afa46547dd1af, 0xab7736f71fd5741a
	.dword 0xe82ef66a5382f2e9, 0xa9c5dd68e29f1a2b
	.dword 0x4cd7155c92c5166a, 0x62e8de812e8009a0
	.dword 0x966590833b2a928f, 0x6caf27ddc762db30
	.dword 0x32759b65b610b713, 0xd423b4e6e75408ea
	.dword 0x1285d8c658df9e91, 0x976a5bfdc5d20555
	.dword 0xcb0c8cf4034b1447, 0x1e7fbaf502e520d8
	.dword 0xd4ec215f5095921c, 0x08a6f6bf8b05e15c
	.dword 0x8c73cd6f3df69ae3, 0x29c7426b801eb02f
	.dword 0xef8178915295f4e1, 0xb0a6614f3160022b
	.dword 0xf8172991eca1888c, 0xf40c9880ed6c5e17
	.dword 0x4307972fe31be795, 0xd4b1c389e2d3e54c
	.dword 0xd082adedf95dc029, 0x739a805b982d429b
	.dword 0x7f841f280024c072, 0xdb87a6833194236d
	.dword 0x2ab34d6604aeae63, 0x47897d998b339f2c
	.dword 0x566529f3b107b7b5, 0xbbeb67009a0530e2
	.dword 0x5165d7b15d9f3e2c, 0x78c3eecbdb53271e
	.dword 0xbe3927272ba6a41e, 0x61c077fd5b17ae1e
	.dword 0x3dde3fdc75f1dd35, 0x3c82f7f5df3fd82a
	.dword 0x89140ae6a349c773, 0xc15b7527946c483d

.align 8
loop_count: .word 0x40

RVTEST_DATA_END
