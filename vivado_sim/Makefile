PATH_INC += ../src

XVLOG_ARGS += --sv
XVLOG_ARGS += $(addprefix -i , $(PATH_INC))
XVLOG_ARGS += $(addprefix -d , $(DEFINE))

XELAB_ARGS += --timescale 1ns/1ps
XELAB_ARGS += --mt off

XSIM_ARGS  += -t sim_vivado.tcl

ifneq ($(strip $(DUMP)), off)
  XELAB_ARGS += -debug all
endif

ifeq ($(strip $(DUMP)), wdb)
  XSIM_ARGS += -wdb out.wdb
endif

ifeq ($(strip $(PRE_COMPILE)), on)
  XELAB_ARGS += -L libcell=$(PATH_VIVADO_LIB)
endif

PATH_VIVADO_LIB := /storage/eda/libs/$(ID)/pezy/vivado

XVLOG := xvlog
XELAB := xelab
XSIM  := xsim

sim_vivado:
	$(XVLOG) $(XVLOG_ARGS) -f filelist.f $(FILE_TEST) $(FILE_SRC) | tee -a sim.log
	$(XELAB) $(XELAB_ARGS) tb | tee -a sim.log
	$(XSIM) $(XSIM_ARGS) "work.tb" | tee -a sim.log

lib_vivado: pre_vivado
	-mv $(PATH_VIVADO_LIB) $(PATH_VIVADO_LIB)_$(TIME_CURRENT)
	mkdir   $(PATH_VIVADO_LIB)
	$(XVLOG) -work libcell=$(PATH_VIVADO_LIB) $(XVLOG_ARGS) -f filelist.f

clean:
	rm -rf *.vcd *.wdb *.log *.pb *.jou xsim.dir *.str
