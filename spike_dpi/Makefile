.PHONY: riscv_isa_sim riscv-isa-sim-makefile

VERILATOR_HOME = /usr/local/share/verilator

ifeq ($(VERILATOR),1)
	CFLAGS += -DVERILATOR
endif

CFLAGS += -g
CFLAGS += -I$(abspath riscv-isa-sim)/riscv
CFLAGS += -I$(abspath riscv-isa-sim)
CFLAGS += -I$(abspath riscv-isa-sim)/softfloat/
CFLAGS += -I$(abspath riscv-isa-sim)/fesvr/
CFLAGS += $(abspath riscv-isa-sim)/libspike_main.a
CFLAGS += $(abspath riscv-isa-sim)/libriscv.a
CFLAGS += $(abspath riscv-isa-sim)/libdisasm.a
CFLAGS += $(abspath riscv-isa-sim)/libsoftfloat.a
CFLAGS += $(abspath riscv-isa-sim)/libfesvr.a
CFLAGS += $(abspath riscv-isa-sim)/libfdt.a
CFLAGS += -I$(VERILATOR_HOME)/include/vltstd/
# CFLAGS += -lriscv

EXE_CFLAGS += -g
EXE_CFLAGS += -Wl,--export-dynamic
EXE_CFLAGS += -Wl,-rpath,/usr/local/lib
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/riscv
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/softfloat/
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/fesvr/
EXE_CFLAGS += $(abspath riscv-isa-sim)/libspike_main.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libriscv.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libdisasm.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libsoftfloat.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libfesvr.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libfdt.a
EXE_CFLAGS += -lpthread
EXE_CFLAGS += -ldl
EXE_CFLAGS += -lpthread
EXE_CFLAGS += -DSIM_MAIN
EXE_CFLAGS += -I$(VERILATOR_HOME)/include/vltstd/

all: libspike_dpi.so spike_main

libspike_dpi.so: spike_dpi.cpp riscv_isa_sim
	g++ -shared -fPIC $(CFLAGS) spike_dpi.cpp -o $@

# spike_main: riscv_isa_sim spike_dpi.o
spike_main: spike_dpi.o libspike_dpi.so
	g++ -o $@ spike_dpi.o $(EXE_CFLAGS)

spike_dpi.o: spike_dpi.cpp
	g++ $^ -c -o $@ $(EXE_CFLAGS)

riscv_isa_sim: riscv-isa-sim-makefile
	make -C riscv-isa-sim -j$(shell nproc)
	touch -f riscv-isa-sim-makefile

clean:
	rm -rf riscv-isa-sim-makefile
