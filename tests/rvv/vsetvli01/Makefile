COMMON_DIR = ../../riscv-tests/benchmarks/common

CFLAGS += -I./../../riscv-tests/env
 CFLAGS += -I./../../riscv-tests/benchmarks/common
# CFLAGS += -I$(HOME)/riscv_rvv/lib/gcc/riscv64-unknown-elf/12.0.1/include/
CFLAGS += -march=rv64gcv
CFLAGS += -mabi=lp64d
CFLAGS += -DPREALLOCATE=1
CFLAGS += -mcmodel=medany
CFLAGS += -static
# CFLAGS += -std=gnu99
CFLAGS += -O3
CFLAGS += -ffast-math
CFLAGS += -fno-common
CFLAGS += -fno-builtin-printf
CFLAGS += -fno-tree-loop-distribute-patterns

SRC_FILES += test.c

all:
	riscv64-unknown-elf-gcc $(CFLAGS) -o test.elf $(SRC_FILES) $(COMMON_DIR)/syscalls.c $(COMMON_DIR)/crt.S -static -nostdlib -nostartfiles -lm -lgcc -T $(COMMON_DIR)/test.ld
	riscv64-unknown-elf-objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data test.elf > test.dump
