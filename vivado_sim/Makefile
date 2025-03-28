all: sim_vivado

RV_AMO  = 1

PATH_INC += ../src
PATH_INC += ../src/fpnew/src/common_cells/include
PATH_INC += ../tb

DEFINE += SIMULATION
DEFINE += RV_AMO=$(RV_AMO)
DEFINE += RV64
DEFINE += XSIM

XVLOG_ARGS += --sv
XVLOG_ARGS += $(addprefix -i , $(PATH_INC))
XVLOG_ARGS += $(addprefix -d , $(DEFINE))

XELAB_ARGS += --timescale 1ns/1ps
XELAB_ARGS += --mt off

XSIM_ARGS  += -t sim_vivado.tcl

CPP_FILELIST += ../cpp/tb_elf_loader.cpp
CPP_FILELIST += ../cpp/tb_debug_tick.cpp
CPP_FILELIST += ../cpp/mem_body.cpp
CPP_FILELIST += ../cpp/memory_block.cpp

XSC_ARGS += --cppversion 14
XSC_ARGS += $(CPP_FILELIST)
XSC_ARGS += -gcc_compile_options "-I../spike_dpi/"
XSC_ARGS += --gcc_link_options "-L/usr/lib64 -lelf -I/usr/include/x86_64-linux-gnu/"

DUMP=off


ifneq ($(strip $(DUMP)), off)
  XELAB_ARGS += -debug all
endif

ifeq ($(strip $(DUMP)), wdb)
  XSIM_ARGS += -wdb out.wdb
endif
XSIM_ARGS  += --testplusarg "ELF=${ELF}"

ifeq ($(strip $(PRE_COMPILE)), on)
  XELAB_ARGS += -L libcell=$(PATH_VIVADO_LIB)
endif

XELAB_ARGS += -O0

# XELAB_ARGS += -sv_lib dpi
# XELAB_ARGS += --lib elf

XSC   := xsc
XVLOG := xvlog
XELAB := xelab
XSIM  := xsim

DECODE_FILES  =
DECODE_FILES += ../src/decoder_inst_cat.sv
DECODE_FILES += ../src/decoder_alu_ctrl.sv
DECODE_FILES += ../src/decoder_lsu_ctrl.sv
DECODE_FILES += ../src/decoder_bru_ctrl.sv
DECODE_FILES += ../src/decoder_csu_ctrl.sv
DECODE_FILES += ../src/decoder_reg.sv

build_decode_v: $(DECODE_FILES)

../src/decoder_inst_cat.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb inst_cat
../src/decoder_alu_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb alu_ctrl
../src/decoder_lsu_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb lsu_ctrl
../src/decoder_bru_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb bru_ctrl
../src/decoder_csu_ctrl.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb csu_ctrl
../src/decoder_reg.sv: ../src/riscv_decoder.json
	cd ../src && ./build_decoder.rb reg

FILELIST = sim_filelist.f

sim_vivado: $(DECODE_FILES) $(FILELIST)
	$(XSC) $(XSC_ARGS) | tee sim.log
	$(XVLOG) $(XVLOG_ARGS) \
		../src/riscv_fpu_imafdc_pkg.sv \
		../src/riscv64_pkg.sv \
		../configs/scariv_standard_conf_pkg.sv \
		-f $(FILELIST) $(FILE_TEST) $(FILE_SRC) | tee -a sim.log
	$(XELAB) $(XELAB_ARGS) tb | tee -a sim.log
	DUMP_TYPE=$(DUMP) $(XSIM) $(XSIM_ARGS) "work.tb" | tee -a sim.log

$(FILELIST): ../src/fpnew.vf ../src/filelist.vf filelist.vf
	echo "../tb/sim_pkg.sv" > $@
	echo "../src/riscv_common_pkg.sv" >> $@
	cat $^ >> $@

gui_vivado:
	$(XSIM) -g work.tb --wdb out.wdb

lib_vivado: pre_vivado
	-mv $(PATH_VIVADO_LIB) $(PATH_VIVADO_LIB)_$(TIME_CURRENT)
	mkdir   $(PATH_VIVADO_LIB)
	$(XVLOG) -work libcell=$(PATH_VIVADO_LIB) $(XVLOG_ARGS) -f filelist.f

clean:
	rm -rf *.vcd *.wdb *.log *.pb *.jou xsim.dir *.str .Xil dpi.so
