VERILATOR_OPTS =
VERILATOR_OPTS += --exe
VERILATOR_OPTS += ../cpp/tb_mrh.cpp
VERILATOR_OPTS += ../cpp/tb_elf_loader.cpp
VERILATOR_OPTS += ../cpp/memory_block.cpp
VERILATOR_OPTS += ../cpp/mem_body.cpp
VERILATOR_OPTS += -LDFLAGS "-lbfd"
VERILATOR_OPTS += --cc
VERILATOR_OPTS += -I../src
VERILATOR_OPTS += --trace-fst
VERILATOR_OPTS += --trace-params
VERILATOR_OPTS += --trace-structs
VERILATOR_OPTS += --trace-underscore

TOP      = mrh_tb
FILELIST = filelist.f

all:
	verilator --top-module $(TOP) -o ../$(TOP)_rv32 --Mdir obj_dir_riscv32 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv -f $(FILELIST)
	verilator --top-module $(TOP) -o ../$(TOP)_rv64 --Mdir obj_dir_riscv64 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv -f $(FILELIST)
	$(MAKE) -C obj_dir_riscv32 -f V$(TOP).mk
	$(MAKE) -C obj_dir_riscv64 -f V$(TOP).mk

clean:
	rm -rf obj_dir_riscv32 obj_dir_riscv64 $(TOP)_rv32 $(TOP)_rv64
