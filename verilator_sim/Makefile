NPROCS = $(shell nproc)
ifeq ($(shell uname), Darwin)
	NPROCS = $(shell sysctl -n hw.logicalcpu)
endif

RV_XLEN = 64
RV_FLEN = 64
RV_AMO  = 1
RV_BITMANIP = 0

DEBUG = on

VERILATOR_OPTS =
VERILATOR_OPTS += --exe
# VERILATOR_OPTS += -threads 4
VERILATOR_OPTS += -MAKEFLAGS "OBJCACHE=ccache CXX=clang++ LINK=clang++"
VERILATOR_OPTS += $(abspath ../cpp/tb_scariv.cpp)
VERILATOR_OPTS += $(abspath ../cpp/tb_debug_tick.cpp)
VERILATOR_OPTS += $(abspath ../cpp/memory_block.cpp)
VERILATOR_OPTS += $(abspath ../cpp/mem_body.cpp)
VERILATOR_OPTS += $(abspath ../cpp/kanata.cpp)

# VERILATOR_OPTS += -CFLAGS "-g"
# VERILATOR_OPTS += -LDFLAGS "-lelf"
VERILATOR_OPTS += -O3
VERILATOR_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi/riscv-isa-sim/)
VERILATOR_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi/riscv-isa-sim/riscv)
VERILATOR_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi/riscv-isa-sim/softfloat/)
VERILATOR_OPTS += -CFLAGS "-I"$(abspath ../cpp)
VERILATOR_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi)
VERILATOR_OPTS += -LDFLAGS "-L"$(abspath ../spike_dpi/riscv-isa-sim/)
# VERILATOR_OPTS += -LDFLAGS "-L"$(abspath .)
# VERILATOR_OPTS += -LDFLAGS "-lspike_dpi"
# VERILATOR_OPTS += -LDFLAGS "-lriscv"
VERILATOR_OPTS += $(abspath ../spike_dpi/libspike_dpi.a)
VERILATOR_OPTS += $(abspath ./libsoftfloat.a)
# VERILATOR_OPTS += -LDFLAGS "-lsoftfloat"
VERILATOR_OPTS += -LDFLAGS "-ldisasm"
VERILATOR_OPTS += -LDFLAGS "-lfesvr"
VERILATOR_OPTS += -LDFLAGS "-lfdt"
VERILATOR_OPTS += -LDFLAGS "-ldl"
VERILATOR_OPTS += -LDFLAGS "-lpthread"
VERILATOR_OPTS += -LDFLAGS "-L"$(abspath .)
VERILATOR_OPTS += -LDFLAGS "-Wl,--export-dynamic"
# VERILATOR_OPTS += $(abspath ../spike_dpi/spike_dpi.cpp)
VERILATOR_OPTS += $(abspath ../spike_dpi/gshare_model.cpp)
VERILATOR_OPTS += $(abspath ../spike_dpi/ras_model.cpp)
VERILATOR_OPTS += --cc
VERILATOR_OPTS += -I../src
VERILATOR_OPTS += -I../src/fpnew/src/common_cells/include
VERILATOR_OPTS += -I../tb
VERILATOR_OPTS += -I${VERILATOR_HOME}/include/vltstd

VERILATOR_OPTS += +define+RV_AMO=$(RV_AMO)
ifeq ($(findstring "b",$(ISA)),"b")
	VERILATOR_OPTS += +define+RV_BITMANIP=1
endif
ifeq ($(findstring "v",$(ISA)),"v")
	VERILATOR_OPTS += +define+RV_VECTOR=1
endif


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
endif
VERILATOR_OPTS += +define+MONITOR
VERILATOR_OPTS += --unroll-count 1024
VERILATOR_OPTS += -j $(NPROCS)
VERILATOR_OPTS += +define+SIMULATION
VERILATOR_OPTS += --compiler clang
VERILATOR_OPTS += -Wno-BLKANDNBLK
# VERILATOR_OPTS += -Wno-fatal
VERILATOR_OPTS += -Wno-LITENDIAN
VERILATOR_OPTS += -Wno-WIDTH
VERILATOR_OPTS += -CFLAGS "-DRV_XLEN=$(RV_XLEN) -DRV_FLEN=$(RV_FLEN) -DISA=\"$(ISA)\""

VERILATOR_OPTS += ../cpp/tb_elf_loader.cpp

VERILATOR_OPTS_RV64 += +define+RV64

VERILATOR_OPTS_RV32 += -CFLAGS "-DRV_XLEN=32"
VERILATOR_OPTS_RV32 += +define+RV32

TOP      = scariv_tb

.PHONY: rv32_standard rv64_standard rv32_big rv64_big rv32_small rv64_small rv32_giant rv64_giant rv32_tiny rv64_tiny

all: rv32_standard rv64_standard rv32_big rv32_giant rv64_big rv32_small rv64_small rv32_tiny rv64_tiny

DECODE_FILES  =
DECODE_FILES += ../src/decoder_inst_cat.sv
DECODE_FILES += ../src/decoder_alu_ctrl.sv
DECODE_FILES += ../src/decoder_lsu_ctrl.sv
DECODE_FILES += ../src/decoder_bru_ctrl.sv
DECODE_FILES += ../src/decoder_csu_ctrl.sv
DECODE_FILES += ../src/decoder_fpu_ctrl.sv
DECODE_FILES += ../src/decoder_vec_ctrl.sv
DECODE_FILES += ../src/decoder_reg.sv
DECODE_FILES += ../src/pma_map.sv

DECODE_JSONS = ../src/riscv_decoder.json
DECODE_JSONS = ../src/riscv_rvv_decoder.json
DECODE_JSONS = ../src/b_ext.json
DECODE_JSONS = ../src/zicond_ext.json

build_decode_v: build_espresso
	$(MAKE) $(DECODE_FILES)

build_espresso:
	$(MAKE) -C ../tools/espresso-logic/espresso-src

../src/decoder_inst_cat.sv: $(DECODE_JSONS)
	cd ../src && ./build_decoder.rb inst_cat $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/decoder_alu_ctrl.sv: $(DECODE_JSONS)
	cd ../src && ./build_decoder.rb alu_ctrl $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/decoder_lsu_ctrl.sv: $(DECODE_JSONS)
	cd ../src && ./build_decoder.rb lsu_ctrl $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/decoder_bru_ctrl.sv: $(DECODE_JSONS)
	cd ../src && ./build_decoder.rb bru_ctrl $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/decoder_csu_ctrl.sv: $(DECODE_JSONS)
	cd ../src && ./build_decoder.rb csu_ctrl $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/decoder_fpu_ctrl.sv: $(DECODE_JSONS)
	cd ../src && ./build_decoder.rb fpu_ctrl $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/decoder_vec_ctrl.sv: ../src/riscv_rvv_decoder.json
	cd ../src && ./build_decoder.rb vec_ctrl $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/decoder_reg.sv: $(DECODE_JSONS)
	cd ../src && ./build_decoder.rb reg $(RV_XLEN) $(RV_FLEN) $(ISA)
../src/pma_map.sv: ../src/pma_memory_map.json ../scripts/build_memory_map.rb
	cd ../src && ../scripts/build_memory_map.rb $< $(RV_XLEN)

FILELIST = sim_filelist.f

.config_design_xlen32_flen$(RV_FLEN): $(DECODE_JSONS) ../src/pma_memory_map.json
	make -B RV_XLEN=32 RV_FLEN=$(RV_FLEN) ISA=$(ISA) build_decode_v > /dev/null 2>&1
	rm -rf .config_design_*
	touch $@

.config_design_xlen64_flen$(RV_FLEN): $(DECODE_JSONS) ../src/pma_memory_map.json
	make -B RV_XLEN=64 RV_FLEN=$(RV_FLEN) ISA=$(ISA) build_decode_v > /dev/null 2>&1
	rm -rf .config_design_*
	touch $@

.dts_xlen$(RV_XLEN)_flen$(RV_FLEN)_$(ISA):
	make -B XLEN=$(RV_XLEN) EXT=$(ISA) -C ../dts
	rm -rf .dts_xlen*
	touch $@

.tests_build_done:
	cd ../tests/ && \
	./build_tests.sh
	touch $@

rv32_build: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN) .dts_xlen32_flen$(RV_FLEN)_$(ISA)
	verilator --top-module $(TOP) \
		-o ../$(TOP)_rv32$(ISA)_$(CONF) \
		--Mdir obj_dir_rv32$(ISA)_$(CONF) \
		$(VERILATOR_OPTS) \
		$(VERILATOR_OPTS_RV32) \
		../src/riscv_common_pkg.sv \
		../src/riscv_fpu_$(ISA)_pkg.sv \
		../src/riscv32_pkg.sv \
		../src/scariv_$(CONF)_conf_pkg.sv \
		-f $(FILELIST)

# \
#		2>&1 | tee build_rv32$(ISA)_$(CONF).log

rv64_build: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN) .dts_xlen64_flen$(RV_FLEN)_$(ISA)
	verilator --top-module $(TOP) \
		-o ../$(TOP)_rv64$(ISA)_$(CONF) \
		--Mdir obj_dir_rv64$(ISA)_$(CONF) \
		$(VERILATOR_OPTS) \
		$(VERILATOR_OPTS_RV64) \
		../src/riscv_common_pkg.sv \
		../src/riscv_fpu_$(ISA)_pkg.sv \
		../src/riscv64_pkg.sv \
		../src/scariv_$(CONF)_conf_pkg.sv \
		-f $(FILELIST)

# \
#		2>&1 | tee build_rv64$(ISA)_$(CONF).log

include conf_tiny.mk
include conf_small.mk
include conf_standard.mk
include conf_big.mk
include conf_giant.mk
include regression.mk

regression:
	$(MAKE) rv32imc_regress
	$(MAKE) rv32imfc_regress
	$(MAKE) rv32imfdc_regress
	$(MAKE) rv64imc_regress
	$(MAKE) rv64imfc_regress
	$(MAKE) rv64imfdc_regress

rv64_aapg_test: gen_aapg
	$(MAKE) rv64_tiny_aapg rv64_small_aapg rv64_standard_aapg rv64_big_aapg rv64_giant_aapg
gen_aapg:
	cd ../tests/aapg/ && aapg gen --num_programs 100 && $(MAKE) -C work build objdump XLEN=64 ISA=rv64imfd ABI=lp64d -j$(NPROCS)

../spike_dpi/libspike_dpi.so:
	$(MAKE) -C ../spike_dpi
	ln -sf ../spike_dpi/$@ .

$(FILELIST): ../src/fpnew.vf ../src/filelist.vf filelist.f
	echo "../tb/sim_pkg.sv" > $@
	cat $^ >> $@

clean:
	rm -rf obj_dir_rv* $(TOP)_rv* $(DECODE_FILES) .config_design_* sim_rv* .dts_xlen*
	$(MAKE) -C ../dts clean
