.PHONY: riscv_isa_sim

CFLAGS += -g
CFLAGS += -I$(abspath riscv-isa-sim)/riscv
CFLAGS += -I$(abspath riscv-isa-sim)
CFLAGS += -I$(abspath riscv-isa-sim)/softfloat/
CFLAGS += -I$(abspath riscv-isa-sim)/fesvr/
CFLAGS += -L$(abspath riscv-isa-sim)
CFLAGS += -lriscv

all: libspike_dpi.so

libspike_dpi.so: riscv_isa_sim
	g++ -shared -fPIC $(CFLAGS) spike_dpi.cpp -o $@

riscv_isa_sim: riscv-isa-sim/Makefile
	make -C riscv-isa-sim -j$(shell nproc)

riscv-isa-sim/Makefile:
	cd riscv-isa-sim && ./configure --enable-commitlog=yes
