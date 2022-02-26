.PHONY: compile dump

CFLAGS =
CFLAGS += -I./../../../common
CFLAGS += -DPREALLOCATE=1
CFLAGS += -mcmodel=medany
CFLAGS += -static
CFLAGS += -std=gnu99
CFLAGS += -march=rv64g
CFLAGS += -O2
CFLAGS += -ffast-math
CFLAGS += -fno-common
CFLAGS += -fno-builtin-printf
CFLAGS += -static
CFLAGS += -nostdlib
CFLAGS += -nostartfiles
CFLAGS += -lm
CFLAGS += -lgcc
CFLAGS += -T ./../../../common/test.ld

all: compile dump

compile: test.hex
test.hex: test.elf
	../../../../tools/elf2hex/elf2hex $^ 32 > test.hex
test.elf: test.S
	riscv64-unknown-elf-gcc $(CFLAGS) -o $@ $^

dump:
	riscv64-unknown-elf-objdump -D test.elf > test.dmp
