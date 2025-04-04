.PHONY: filelist

export CORES = $(shell nproc)

all: filelist
	vivado -mode tcl -log synth.log -source ../synth.tcl

filelist:
	$(MAKE) -B filelist.tcl

filelist.tcl:
	echo "add_files -norecurse " $(shell sed 's|^|../|g' ../../src/fpnew.vf | sed 's/\r\n/ /g') $(shell sed 's|^|../|g' ../../src/filelist.vf | sed 's/\r\n/ /g') > $@

clean:
	rm -rf *.log *.rpt *.pb *.jou *.xpr *.dcp .Xil
