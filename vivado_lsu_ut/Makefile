all: sim_vivado

PATH_INC += ../src

DEFINE += SIMULATION
DEFINE += RV64
DEFINE += RV_XLEN=64

XVLOG_ARGS += --sv
XVLOG_ARGS += $(addprefix -i , $(PATH_INC))
XVLOG_ARGS += $(addprefix -d , $(DEFINE))

XELAB_ARGS += --timescale 1ns/1ps
XELAB_ARGS += --mt off

XSIM_ARGS  += -t sim_vivado.tcl

ELF_LOADER += ../cpp/tb_elf_loader.cpp

CPP_FILELIST += ../cpp/tb_debug_tick.cpp
CPP_FILELIST += ../cpp/mem_body.cpp
CPP_FILELIST += ../cpp/memory_block.cpp
CPP_FILELIST += ../spike_dpi/spike_dpi.cpp

INC_DIR += $(abspath ../spike_dpi/riscv-isa-sim/riscv/)
INC_DIR += $(abspath ../spike_dpi/riscv-isa-sim/)
INC_DIR += $(abspath ../spike_dpi/riscv-isa-sim/fesvr/)
INC_DIR += $(abspath ../spike_dpi/riscv-isa-sim/softfloat/)
INC_DIR += /usr/include/
INC_DIR += /usr/include/x86_64-linux-gnu/

INC2_DIR += $(abspath ../spike_dpi/riscv-isa-sim/riscv/)
INC2_DIR += $(abspath ../spike_dpi/riscv-isa-sim/)
INC2_DIR += $(abspath ../spike_dpi/riscv-isa-sim/softfloat/)
INC2_DIR += /usr/include/
INC2_DIR += /usr/include/x86_64-linux-gnu/

XSC_ARGS += -mt off
XSC_ARGS += -v 1
XSC_ARGS += -compile
XSC_ARGS += --cppversion 14
XSC_ARGS += $(CPP_FILELIST)
XSC_ARGS += -gcc_link_options "-L/usr/lib64 -lelf $(addprefix -I, $(INC_DIR))"
XSC_ARGS += $(addprefix -gcc_compile_options "-I, $(addsuffix ", $(INC_DIR)))
XSC_ARGS += $(addprefix -gcc_compile_options "-D, $(addsuffix ", $(DEFINE)))

XSC2_ARGS += -mt off
XSC2_ARGS += -v
XSC2_ARGS += -compile
XSC2_ARGS += --cppversion 14
XSC2_ARGS += $(ELF_LOADER)
XSC2_ARGS += -gcc_link_options "-L/usr/lib64 -lelf $(addprefix -I, $(INC_DIR))"
XSC2_ARGS += $(addprefix -gcc_compile_options "-I, $(addsuffix ", $(INC2_DIR)))
XSC2_ARGS += $(addprefix -gcc_compile_options "-D, $(addsuffix ", $(DEFINE)))

XSC_LINK_ARGS += -shared
XSC_LINK_ARGS += -gcc_link_options "-L/usr/lib64 $(addprefix -L, $(INC_DIR)) -lelf -lriscv -lsoftfloat -ldisasm -lfesvr -lfdt -ldl -lpthread $(addprefix -I, $(INC_DIR))"
XSC_LINK_ARGS += -v 1


DUMP=off


ifneq ($(strip $(DUMP)), off)
  XELAB_ARGS += -debug all
endif

ifeq ($(strip $(DUMP)), wdb)
  XSIM_ARGS += -wdb out.wdb
endif
XSIM_ARGS  += --testplusarg "ELF=$(ELF)"

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
	$(XSC) $(XSC2_ARGS) | tee sim.log
	$(XSC) $(XSC_ARGS) | tee -a sim.log
	$(XSC) $(XSC_LINK_ARGS) | tee -a sim.log
	$(XVLOG) $(XVLOG_ARGS) ../src/riscv64_pkg.sv ../src/msrh_standard_conf_pkg.sv -f $(FILELIST) $(FILE_TEST) $(FILE_SRC) | tee -a sim.log
	$(XELAB) $(XELAB_ARGS) tb | tee -a sim.log
	DUMP_TYPE=$(DUMP) $(XSIM) $(XSIM_ARGS) "work.tb" | tee -a sim.log


$(FILELIST): ../src/filelist.f filelist.f
	cat $^ > $@

gui_vivado:
	vivado -mode gui -source ./wdb_view.tcl

#	$(XSIM) -g work.tb --wdb out.wdb

lib_vivado: pre_vivado
	-mv $(PATH_VIVADO_LIB) $(PATH_VIVADO_LIB)_$(TIME_CURRENT)
	mkdir   $(PATH_VIVADO_LIB)
	$(XVLOG) -work libcell=$(PATH_VIVADO_LIB) $(XVLOG_ARGS) -f filelist.f

clean:
	rm -rf *.vcd *.wdb *.log *.pb *.jou xsim.dir *.str .Xil dpi.so
