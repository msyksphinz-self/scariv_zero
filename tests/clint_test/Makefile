COMMON_DIR = ../riscv-tests/benchmarks/common

CFLAGS_COMMON =

CFLAGS_COMMON += -I./
CFLAGS_COMMON += -I./../riscv-tests/env
CFLAGS_COMMON += -I./../riscv-tests/benchmarks/common
CFLAGS_COMMON += -DPREALLOCATE=1
CFLAGS_COMMON += -mcmodel=medany
CFLAGS_COMMON += -static
CFLAGS_COMMON += -std=gnu99
CFLAGS_COMMON += -O2
CFLAGS_COMMON += -ffast-math
CFLAGS_COMMON += -fno-common
CFLAGS_COMMON += -fno-builtin-printf
CFLAGS_COMMON += -fno-tree-loop-distribute-patterns

CFLAGS_RV64 += -march=rv64imc
CFLAGS_RV64 += -mabi=lp64
CFLAGS_RV64 += $(CFLAGS_COMMON)

CFLAGS_RV32 += -march=rv32imafdc
CFLAGS_RV32 += -mabi=ilp32d
CFLAGS_RV32 += $(CFLAGS_COMMON)

SRC_FILES += test.c
SRC_FILES += handlers.S

all: build_rv32 build_rv64

build_rv64:
	riscv64-unknown-elf-gcc $(CFLAGS_RV64) -o test_rv64.elf $(SRC_FILES) $(COMMON_DIR)/syscalls.c $(COMMON_DIR)/crt.S -static -nostdlib -nostartfiles -lm -lgcc -T $(COMMON_DIR)/test.ld
	riscv64-unknown-elf-objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data test_rv64.elf > test_rv64.dump

build_rv32:
	riscv32-unknown-elf-gcc $(CFLAGS_RV32) -o test_rv32.elf $(SRC_FILES) $(COMMON_DIR)/syscalls.c $(COMMON_DIR)/crt.S -static -nostdlib -nostartfiles -lm -lgcc -T $(COMMON_DIR)/test.ld
	riscv32-unknown-elf-objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data test_rv32.elf > test_rv32.dump
