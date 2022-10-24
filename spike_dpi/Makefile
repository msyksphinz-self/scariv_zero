.PHONY: riscv_isa_sim

# VERILATOR_HOME = /usr/local/share/verilator
VERILATOR_HOME = /home/kimura/usr/share/verilator

ifeq ($(VERILATOR),1)
	CFLAGS += -DVERILATOR
endif

VCS_HOME = /dev/shm/shioya/opt/synopsys/vcs/S-2021.09

CFLAGS += -g
CFLAGS += --std=c++17
CFLAGS += -I$(abspath riscv-isa-sim)/riscv
CFLAGS += -I$(abspath riscv-isa-sim)
CFLAGS += -I$(abspath riscv-isa-sim)/softfloat/
CFLAGS += -I$(abspath riscv-isa-sim)/fesvr/
CFLAGS += -I$(abspath ../cpp/)
CFLAGS += $(abspath riscv-isa-sim)/libspike_main.a
CFLAGS += $(abspath riscv-isa-sim)/libriscv.a
CFLAGS += $(abspath riscv-isa-sim)/libdisasm.a
CFLAGS += $(abspath riscv-isa-sim)/libsoftfloat.a
CFLAGS += $(abspath riscv-isa-sim)/libfesvr.a
CFLAGS += $(abspath riscv-isa-sim)/libfdt.a
CFLAGS += -I$(VERILATOR_HOME)/include/vltstd/
CFLAGS += -I$(VCS_HOME)/include/

# CFLAGS += -lriscv

EXE_CFLAGS += -g
EXE_CFLAGS += --std=c++17
# EXE_CFLAGS += -Wl,--export-dynamic
EXE_CFLAGS += -Wl,-rpath,/usr/local/lib
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/riscv
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/softfloat/
EXE_CFLAGS += -I$(abspath riscv-isa-sim)/fesvr/
EXE_CFLAGS += -I$(abspath ../cpp/)
EXE_CFLAGS += $(abspath riscv-isa-sim)/libspike_main.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libriscv.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libdisasm.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libsoftfloat.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libfesvr.a
EXE_CFLAGS += $(abspath riscv-isa-sim)/libfdt.a
EXE_CFLAGS += -lpthread
EXE_CFLAGS += -ldl
EXE_CFLAGS += -DSIM_MAIN
EXE_CFLAGS += -I$(VERILATOR_HOME)/include/vltstd/
EXE_CFLAGS += -I$(VCS_HOME)/include/
EXE_CFLAGS += -ldl
EXE_CFLAGS += -lpthread

all: riscv-isa-sim-makefile libserialdevice.so Makefile
	$(MAKE) spike_dpi.o
	$(MAKE) libspike_dpi_exe.so
	$(MAKE) spike_main

libspike_dpi_exe.so: spike_dpi.cpp riscv-isa-sim-makefile
	g++ -shared -fPIC $(EXE_CFLAGS) spike_dpi.cpp -o $@

libserialdevice.so: serialdevice.cc
	g++ -o $@ -fPIC -shared $^ -I./riscv-isa-sim/riscv -I./riscv-isa-sim -I./riscv-isa-sim/softfloat -I./riscv-isa-sim/fesvr

spike_main: spike_dpi_exe.o libspike_dpi.a
	g++ -L. -Wl,--export-dynamic -o $@ $^ $(EXE_CFLAGS)

spike_dpi_exe.o: spike_dpi.cpp
	g++ $^ -c -o $@ $(EXE_CFLAGS)

include spike_dpi.mk

riscv-isa-sim-makefile:
	@if [ ! -e $@ ]; then \
		cd riscv-isa-sim && ./configure --enable-commitlog --without-boost --without-boost-asio --without-boost-regex; \
	fi
	touch -f $@
	make -C riscv-isa-sim -j$(shell nproc)

CLEAN_FILES += riscv-isa-sim-makefile

clean:
	rm -rf $(CLEAN_FILES)
