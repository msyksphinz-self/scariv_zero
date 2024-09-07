all: NaxRiscv.v
	$(MAKE) vivado

NaxRiscv.v:
	gunzip -c NaxRiscv.v.gz > NaxRiscv.v

vivado:
	vivado -mode tcl -log synth.log -source ./synth.tcl

clean:
	rm -rf *.log *.rpt *.txt *.jou *.pb *.synth.v NaxRiscv.v *.xpr *.dcp
