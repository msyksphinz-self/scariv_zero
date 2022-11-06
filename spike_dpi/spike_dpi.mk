VERILATOR_HOME = /usr/local/share/verilator
CFLAGS += -I$(VERILATOR_HOME)/include/vltstd/
CFLAGS += -I$(abspath riscv-isa-sim)/riscv
CFLAGS += -I$(abspath riscv-isa-sim)
CFLAGS += -I$(abspath riscv-isa-sim)/softfloat/
CFLAGS += -I$(abspath riscv-isa-sim)/fesvr/
CFLAGS += -I$(abspath ../cpp/)

HAVE_INT128 := yes
HAVE_DLOPEN := yes

include riscv-isa-sim/riscv.mk

riscv_cc := $(patsubst %.cc, riscv-isa-sim/%.cc, $(riscv_srcs))
riscv_objs := $(patsubst %.cc, %.o, $(riscv_cc))
riscv_objs += spike_dpi.o

CLEAN_FILES += libspike_dpi.a
CLEAN_FILES += spike_dpi.o

spike_dpi.o: spike_dpi.cpp
	g++ $^ -c -o $@ $(CFLAGS)

libspike_dpi.a: $(riscv_objs)
	ar rcs $@ $^
