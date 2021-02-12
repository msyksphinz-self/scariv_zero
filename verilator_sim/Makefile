VERILATOR_OPTS =
VERILATOR_OPTS += --exe
VERILATOR_OPTS += ../cpp/tb_mrh.cpp
VERILATOR_OPTS += ../cpp/tb_new_elf_loader.cpp
VERILATOR_OPTS += ../cpp/tb_debug_tick.cpp
VERILATOR_OPTS += ../cpp/memory_block.cpp
VERILATOR_OPTS += ../cpp/mem_body.cpp
VERILATOR_OPTS += -CFLAGS "-g"
VERILATOR_OPTS += -LDFLAGS "-lelf"
VERILATOR_OPTS += --cc
VERILATOR_OPTS += -I../src
VERILATOR_OPTS += --trace-fst
VERILATOR_OPTS += --trace-params
VERILATOR_OPTS += --trace-structs
VERILATOR_OPTS += --trace-underscore
VERILATOR_OPTS += --unroll-count 1024
VERILATOR_OPTS += -j $(shell nproc)

TOP      = mrh_tb
FILELIST = filelist.f

.PHONY: rv32 rv64

all: rv32 rv64

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


rv32: $(DECODE_FILES)
	verilator --top-module $(TOP) -o ../$(TOP)_rv32 --Mdir obj_dir_riscv32 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv -f $(FILELIST) -xml-only
	xml2stems obj_dir_riscv32/Vmrh_tb.xml obj_dir_riscv32/Vmrh_tb.stems
	verilator --top-module $(TOP) -o ../$(TOP)_rv32 --Mdir obj_dir_riscv32 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv -f $(FILELIST)
	$(MAKE) -C obj_dir_riscv32 -f V$(TOP).mk

rv64: $(DECODE_FILES)
	verilator --top-module $(TOP) -o ../$(TOP)_rv64 --Mdir obj_dir_riscv64 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv -f $(FILELIST) -xml-only
	xml2stems obj_dir_riscv64/Vmrh_tb.xml obj_dir_riscv64/Vmrh_tb.stems
	verilator --top-module $(TOP) -o ../$(TOP)_rv64 --Mdir obj_dir_riscv64 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv -f $(FILELIST)
	$(MAKE) -C obj_dir_riscv64 -f V$(TOP).mk

clean:
	rm -rf obj_dir_riscv32 obj_dir_riscv64 $(TOP)_rv32 $(TOP)_rv64 $(DECODE_FILES)
