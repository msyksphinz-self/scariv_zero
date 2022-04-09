rv32imc_regress: $(FILELIST)
	$(MAKE) .config_design_xlen32_flen0 RV_FLEN=0
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) -j$(NPROC) rv32imc_tiny_test rv32imc_small_test rv32imc_standard_test rv32imc_big_test rv32imc_giant_test DEBUG=off RV_FLEN=0
