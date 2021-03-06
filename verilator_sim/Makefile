NPROCS = $(shell nproc)

VERILATOR_OPTS =
VERILATOR_OPTS += --exe
VERILATOR_OPTS += --build
VERILATOR_OPTS += -output-split 15000
VERILATOR_OPTS += -threads 4
VERILATOR_OPTS += ../cpp/tb_msrh.cpp
VERILATOR_OPTS += ../cpp/tb_new_elf_loader.cpp
VERILATOR_OPTS += ../cpp/tb_debug_tick.cpp
VERILATOR_OPTS += ../cpp/memory_block.cpp
VERILATOR_OPTS += ../cpp/mem_body.cpp
VERILATOR_OPTS += -CFLAGS "-g"
VERILATOR_OPTS += -LDFLAGS "-lelf"
VERILATOR_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi)
VERILATOR_OPTS += -LDFLAGS "-L"$(abspath ../spike_dpi/riscv-isa-sim/)
VERILATOR_OPTS += -LDFLAGS "-L"$(abspath ../spike_dpi)
VERILATOR_OPTS += -LDFLAGS "-lspike_dpi"
VERILATOR_OPTS += -LDFLAGS "-lriscv"
VERILATOR_OPTS += -LDFLAGS "-lsoftfloat"
VERILATOR_OPTS += -LDFLAGS "-ldisasm"
VERILATOR_OPTS += -LDFLAGS "-lfesvr"
VERILATOR_OPTS += -LDFLAGS "-lfdt"
VERILATOR_OPTS += -LDFLAGS "-ldl"
VERILATOR_OPTS += -LDFLAGS "-lpthread"
VERILATOR_OPTS += --cc
VERILATOR_OPTS += -I../src
VERILATOR_OPTS += -I../tb
VERILATOR_OPTS += --trace-fst
VERILATOR_OPTS += --trace-params
VERILATOR_OPTS += --trace-structs
VERILATOR_OPTS += --trace-underscore
VERILATOR_OPTS += --unroll-count 1024
VERILATOR_OPTS += -j $(NPROCS)
VERILATOR_OPTS += +define+SIMULATION

TOP      = msrh_tb

.PHONY: rv32_standard rv64_standard rv32_big rv64_big rv32_small rv64_small

all: rv32_standard rv64_standard rv32_big rv64_big rv32_small rv64_small

DECODE_FILES  =
DECODE_FILES += ../src/decoder_cat.sv
DECODE_FILES += ../src/decoder_inst_ctrl.sv
DECODE_FILES += ../src/decoder_reg.sv

../src/decoder_cat.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb cat
../src/decoder_inst_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb inst_ctrl
../src/decoder_reg.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb reg

FILELIST = sim_filelist.f

CXX=clang++
LD=lld

rv32_standard: $(DECODE_FILES) $(FILELIST) libspike_dpi.so
	OBJCACHE=ccache verilator --top-module $(TOP) -o ../$(TOP)_rv32_standard --Mdir obj_dir_rv32_standard $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv ../src/msrh_standard_conf_pkg.sv -f $(FILELIST)

rv64_standard: $(DECODE_FILES) $(FILELIST) libspike_dpi.so
	OBJCACHE=ccache verilator --top-module $(TOP) -o ../$(TOP)_rv64_standard --Mdir obj_dir_rv64_standard $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv ../src/msrh_standard_conf_pkg.sv  -f $(FILELIST)

rv32_big: $(DECODE_FILES) $(FILELIST) libspike_dpi.so
	OBJCACHE=ccache verilator --top-module $(TOP) -o ../$(TOP)_rv32_big --Mdir obj_dir_rv32_big $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv ../src/msrh_big_conf_pkg.sv -f $(FILELIST)

rv64_big: $(DECODE_FILES) $(FILELIST) libspike_dpi.so
	OBJCACHE=ccache verilator --top-module $(TOP) -o ../$(TOP)_rv64_big --Mdir obj_dir_rv64_big $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv ../src/msrh_big_conf_pkg.sv  -f $(FILELIST)

rv32_small: $(DECODE_FILES) $(FILELIST) libspike_dpi.so
	OBJCACHE=ccache verilator --top-module $(TOP) -o ../$(TOP)_rv32_small --Mdir obj_dir_rv32_small $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv ../src/msrh_small_conf_pkg.sv -f $(FILELIST)

rv64_small: $(DECODE_FILES) $(FILELIST) libspike_dpi.so
	OBJCACHE=ccache verilator --top-module $(TOP) -o ../$(TOP)_rv64_small --Mdir obj_dir_rv64_small $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv ../src/msrh_small_conf_pkg.sv  -f $(FILELIST)

libspike_dpi.so:
	$(MAKE) -C ../spike_dpi
	ln -s ../spike_dpi/$@ .

$(FILELIST): ../src/filelist.f filelist.f
	cat $^ > $@

clean:
	rm -rf obj_dir_rv* $(TOP)_rv* $(DECODE_FILES) libspike_dpi.so
