.PHONY: filelist

all: filelist
	vivado -mode tcl -log synth.log -source synth.tcl

filelist:
	$(MAKE) -B filelist.tcl

filelist.tcl:
	echo "add_files -norecurse " $(shell sed 's/\r\n/ /g' < ../src/fpnew.vf) $(shell sed 's/\r\n/ /g' < ../src/filelist.f) > $@
