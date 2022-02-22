NPROCS = $(shell nproc)

DEBUG = on

BINARY_SUFFIX = ""
ifeq ($(DEBUG),on)
	BINARY_SUFFIX = -debug
endif

VERILATOR_OPTS =
VERILATOR_OPTS += --exe
# VERILATOR_OPTS += -output-split 15000
# VERILATOR_OPTS += -threads 4
VERILATOR_OPTS += -MAKEFLAGS "OBJCACHE=ccache CXX=clang++ LINK=clang++"
VERILATOR_OPTS += ../cpp/tb_msrh.cpp
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
VERILATOR_OPTS += -I../src/fpnew/src/common_cells/include
VERILATOR_OPTS += -I../tb
ifeq ($(LINT),on)
	VERILATOR_OPTS += --lint-only
else
	VERILATOR_OPTS += --build
endif
ifeq ($(VERI_DEBUG),on)
	VERILATOR_OPTS += --debug
endif
ifeq ($(DEBUG),on)
	VERILATOR_OPTS += --trace-fst
	VERILATOR_OPTS += --trace-params
	VERILATOR_OPTS += --trace-structs
	VERILATOR_OPTS += --trace-underscore
	VERILATOR_OPTS += -CFLAGS "-DVL_DEBUG"
	VERILATOR_OPTS += -CFLAGS "-DDUMP_FST"
	VERILATOR_OPTS += +define+MONITOR
endif
VERILATOR_OPTS += --unroll-count 1024
VERILATOR_OPTS += -j $(NPROCS)
VERILATOR_OPTS += +define+SIMULATION
VERILATOR_OPTS += --compiler clang
VERILATOR_OPTS += -Wno-BLKANDNBLK
VERILATOR_OPTS += -Wno-fatal

VERILATOR_OPTS_RV64 += ../cpp/tb_elf_loader.cpp
VERILATOR_OPTS_RV64 += -CFLAGS "-DRV_XLEN=64"
VERILATOR_OPTS_RV64 += +define+RV64

VERILATOR_OPTS_RV32 += ../cpp/tb_elf32_loader.cpp
VERILATOR_OPTS_RV32 += -CFLAGS "-DRV_XLEN=32"
VERILATOR_OPTS_RV32 += +define+RV32

TOP      = msrh_tb

.PHONY: rv32_standard rv64_standard rv32_big rv64_big rv32_small rv64_small rv32_giant rv64_giant rv32_tiny rv64_tiny

all: rv32_standard rv64_standard rv32_big rv32_giant rv64_big rv32_small rv64_small rv32_tiny rv64_tiny

DECODE_FILES  =
DECODE_FILES += ../src/decoder_inst_cat.sv
DECODE_FILES += ../src/decoder_alu_ctrl.sv
DECODE_FILES += ../src/decoder_lsu_ctrl.sv
DECODE_FILES += ../src/decoder_bru_ctrl.sv
DECODE_FILES += ../src/decoder_csu_ctrl.sv
DECODE_FILES += ../src/decoder_fpu_ctrl.sv
DECODE_FILES += ../src/decoder_reg.sv
DECODE_FILES += ../src/pma_map.sv

build_decode_v: $(DECODE_FILES)

RV_XLEN = 64

../src/decoder_inst_cat.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb inst_cat $(RV_XLEN)
../src/decoder_alu_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb alu_ctrl $(RV_XLEN)
../src/decoder_lsu_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb lsu_ctrl $(RV_XLEN)
../src/decoder_bru_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb bru_ctrl $(RV_XLEN)
../src/decoder_csu_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb csu_ctrl $(RV_XLEN)
../src/decoder_fpu_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb fpu_ctrl $(RV_XLEN)
../src/decoder_reg.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb reg $(RV_XLEN)
../src/pma_map.sv: ../src/pma_memory_map.json ../scripts/build_memory_map.rb
	cd ../src && ../scripts/build_memory_map.rb $< $(RV_XLEN)

FILELIST = sim_filelist.f

.config_design_rv32: ../src/riscv_decoder.json
	make -B RV_XLEN=32 $(DECODE_FILES)
	rm -rf .config_design_*
	touch .config_design_rv32

.config_design_rv64: ../src/riscv_decoder.json
	make -B RV_XLEN=64 $(DECODE_FILES)
	rm -rf .config_design_*
	touch .config_design_rv64

rv32_build: $(FILELIST) .config_design_rv32
	verilator --top-module $(TOP) -o ../$(TOP)_rv32_$(CONF)$(BINARY_SUFFIX) --Mdir obj_dir_rv32_$(CONF)$(BINARY_SUFFIX) $(VERILATOR_OPTS) $(VERILATOR_OPTS_RV32) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv ../src/msrh_$(CONF)_conf_pkg.sv -f $(FILELIST)

rv64_build: $(FILELIST) .config_design_rv64
	verilator --top-module $(TOP) -o ../$(TOP)_rv64_$(CONF)$(BINARY_SUFFIX) --Mdir obj_dir_rv64_$(CONF)$(BINARY_SUFFIX) $(VERILATOR_OPTS) $(VERILATOR_OPTS_RV64) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv ../src/msrh_$(CONF)_conf_pkg.sv  -f $(FILELIST)

rv32_tiny: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny

rv32_small: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=small

rv32_standard: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=standard

rv32_big: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=big

rv32_giant: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=giant


rv64_tiny: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny

rv64_small: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=small

rv64_standard: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=standard

rv64_big: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=big

rv64_giant: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=giant

regression: rv32_tiny_test rv32_small_test rv32_standard_test rv32_big_test rv32_giant_test \
	rv64_tiny_test rv64_small_test rv64_standard_test rv64_big_test rv64_giant_test

rv32_tiny_test:
	$(MAKE) rv32_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32_tiny rv32-tests.json log_rv32_tiny $(shell nproc) 2>&1 | tee rv32_tiny.log

rv32_small_test:
	$(MAKE) rv32_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32_small rv32-tests.json log_rv32_small $(shell nproc) 2>&1 | tee rv32_small.log

rv32_standard_test:
	$(MAKE) rv32_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32_standard rv32-tests.json log_rv32_standard $(shell nproc) 2>&1 | tee rv32_standard.log

rv32_big_test:
	$(MAKE) rv32_big DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32_big rv32-tests.json log_rv32_big $(shell nproc) 2>&1 | tee rv32_big.log

rv32_giant_test:
	$(MAKE) rv32_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32_giant rv32-tests.json log_rv32_giant $(shell nproc) 2>&1 | tee rv32_giant.log

rv64_tiny_test:
	$(MAKE) rv64_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_tiny rv64-tests.json log_rv64_tiny $(shell nproc) 2>&1 | tee rv64_tiny.log

rv64_small_test:
	$(MAKE) rv64_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_small rv64-tests.json log_rv64_small $(shell nproc) 2>&1 | tee rv64_small.log

rv64_standard_test:
	$(MAKE) rv64_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_standard rv64-tests.json log_rv64_standard $(shell nproc) 2>&1 | tee rv64_standard.log

rv64_big_test:
	$(MAKE) rv64_big DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_big rv64-tests.json log_rv64_big $(shell nproc) 2>&1 | tee rv64_big.log

rv64_giant_test:
	$(MAKE) rv64_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_giant rv64-tests.json log_rv64_giant $(shell nproc) 2>&1 | tee rv64_giant.log

rv64_tiny_benchmarks:
	$(MAKE) rv64_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_tiny rv64-bench.json log_rv64_tiny $(shell nproc) 2>&1 | tee rv64_tiny.log

rv64_small_benchmarks:
	$(MAKE) rv64_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_small rv64-bench.json log_rv64_small $(shell nproc) 2>&1 | tee rv64_small.log

rv64_standard_benchmarks:
	$(MAKE) rv64_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_standard rv64-bench.json log_rv64_standard $(shell nproc) 2>&1 | tee rv64_standard.log

rv64_big_benchmarks:
	$(MAKE) rv64_big DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_big rv64-bench.json log_rv64_big $(shell nproc) 2>&1 | tee rv64_big.log

rv64_giant_benchmarks:
	$(MAKE) rv64_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64_giant rv64-bench.json log_rv64_giant $(shell nproc) 2>&1 | tee rv64_giant.log

../spike_dpi/libspike_dpi.so:
	$(MAKE) -C ../spike_dpi
	ln -sf ../spike_dpi/$@ .

$(FILELIST): ../src/fpnew.vf ../src/filelist.f filelist.f
	echo "../tb/sim_pkg.sv" > $@
	cat $^ >> $@

clean:
	rm -rf obj_dir_rv* $(TOP)_rv* $(DECODE_FILES) .config_design_*
