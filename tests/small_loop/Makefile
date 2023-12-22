COMMON_DIR = ../riscv-tests/benchmarks/common

CFLAGS += -I./../riscv-tests/env
CFLAGS += -I./../riscv-tests/benchmarks/common
CFLAGS += -march=rv64imc
CFLAGS += -mabi=lp64
CFLAGS += -DPREALLOCATE=1
CFLAGS += -mcmodel=medany
CFLAGS += -static
CFLAGS += -std=gnu99
CFLAGS += -O2
CFLAGS += -ffast-math
CFLAGS += -fno-common
CFLAGS += -fno-builtin-printf
CFLAGS += -fno-tree-loop-distribute-patterns

SRC_FILES += test.c
SRC_FILES += branch_count.S

all:
	riscv64-unknown-elf-gcc $(CFLAGS) -o test.elf $(SRC_FILES) $(COMMON_DIR)/syscalls.c $(COMMON_DIR)/crt.S -static -nostdlib -nostartfiles -lm -lgcc -T $(COMMON_DIR)/test.ld
	riscv64-unknown-elf-objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data test.elf > test.dump
