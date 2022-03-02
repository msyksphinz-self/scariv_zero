.PHONY: compile dump

REPO_HOME = `git rev-parse --show-toplevel`

CFLAGS =
CFLAGS += -I$(REPO_HOME)/tests/common
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
CFLAGS += -T$(REPO_HOME)/tests/common/test.ld

all: compile dump

compile: test.hex
test.hex: test.elf
	$(REPO_HOME)/tools/elf2hex/elf2hex $^ 32 > test.hex
test.elf: test.S
	riscv64-unknown-elf-gcc $(CFLAGS) -o $@ $^

clean:
	rm -rf test.elf	test.dmp

dump:
	riscv64-unknown-elf-objdump -D test.elf > test.dmp
