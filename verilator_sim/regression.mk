rv32imc_regress: $(FILELIST)
	$(MAKE) .config_design_xlen32_flen0 RV_FLEN=0
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) -j$(NPROC) rv32imc_tiny_test rv32imc_small_test rv32imc_standard_test rv32imc_big_test rv32imc_giant_test DEBUG=off RV_FLEN=0

rv32imfc_regress: $(FILELIST)
	$(MAKE) .config_design_xlen32_flen32 RV_FLEN=32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) -j$(NPROC) rv32imfc_tiny_test rv32imfc_small_test rv32imfc_standard_test rv32imfc_big_test rv32imfc_giant_test DEBUG=off RV_FLEN=32

rv32imfdc_regress: $(FILELIST)
	$(MAKE) .config_design_xlen32_flen64 RV_FLEN=64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) -j$(NPROC) rv32imfdc_tiny_test rv32imfdc_small_test rv32imfdc_standard_test rv32imfdc_big_test rv32imfdc_giant_test DEBUG=off RV_FLEN=64

rv64imc_regress: $(FILELIST)
	$(MAKE) .config_design_xlen64_flen0 RV_FLEN=0
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) -j$(NPROC) rv64imc_tiny_test rv64imc_small_test rv64imc_standard_test rv64imc_big_test rv64imc_giant_test DEBUG=off RV_FLEN=0

rv64imfc_regress: $(FILELIST)
	$(MAKE) .config_design_xlen32_flen32 RV_FLEN=32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) -j$(NPROC) rv64imfc_tiny_test rv64imfc_small_test rv64imfc_standard_test rv64imfc_big_test rv64imfc_giant_test DEBUG=off RV_FLEN=32

rv64imfdc_regress: $(FILELIST)
	$(MAKE) .config_design_xlen32_flen64 RV_FLEN=64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) -j$(NPROC) rv64imfdc_tiny_test rv64imfdc_small_test rv64imfdc_standard_test rv64imfdc_big_test rv64imfdc_giant_test DEBUG=off RV_FLEN=64
