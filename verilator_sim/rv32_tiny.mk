rv32imc_tiny: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imc

rv32imfc_tiny: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imfc

rv32imfdc_tiny: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imfdc

rv32imc_tiny_test:
	$(MAKE) rv32imc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imc_tiny rv32-tests.json log_rv32_tiny $(NPROCS) 2>&1 | tee rv32_tiny_test.log

rv32imfc_tiny_test:
	$(MAKE) rv32imfc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfc_tiny rv32-tests.json log_rv32_tiny $(NPROCS) 2>&1 | tee rv32_tiny_test.log

rv32imfdc_tiny_test:
	$(MAKE) rv32imfdc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfdc_tiny rv32-tests.json log_rv32_tiny $(NPROCS) 2>&1 | tee rv32_tiny_test.log
