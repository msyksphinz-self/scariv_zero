VERILATOR_HOME ?= /usr/local/share/verilator

CFLAGS += -iquote $(VERILATOR_HOME)/include/vltstd/
CFLAGS += -g
CFLAGS += -O0
CFLAGS += -fPIC
CFLAGS += -std=c++2a
CFLAGS += -iquote $(abspath riscv-isa-sim)
CFLAGS += -I$(abspath riscv-isa-sim)
CFLAGS += -iquote $(abspath riscv-isa-sim)/riscv
# CFLAGS += -iquote $(abspath riscv-isa-sim)/softfloat/
# CFLAGS += -I$(abspath riscv-isa-sim)/fesvr/
CFLAGS += -iquote $(abspath ../cpp/)

HAVE_INT128 := yes
HAVE_DLOPEN := yes

include riscv-isa-sim/riscv.mk

riscv_cc := $(patsubst %.cc, riscv-isa-sim/%.cc, $(riscv_srcs))
riscv_objs := $(patsubst %.cc, %.o, $(riscv_cc))
riscv_objs += spike_dpi.o

CLEAN_FILES += libspike_dpi.a
CLEAN_FILES += spike_dpi.o

spike_dpi.o: spike_dpi.cpp
	g++ $(CFLAGS) $^ -c -o $@

libspike_dpi.a: $(riscv_objs)
	ar rcs $@ $^
