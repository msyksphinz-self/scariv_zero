DIR = $(shell date +"%y%m%d_%H%M")
NUM_GEN = 100
CONFIG_YAML = config_priv_m.yaml

gen_tests:
	mkdir -p $(DIR)
	cd $(DIR) && cp -r ../work/common/ . && cd ../
	aapg gen --config_file configs/$(CONFIG_YAML) --setup_dir $(DIR) --output_dir $(DIR)/asm --num_programs $(NUM_GEN)
	mkdir -p $(DIR)/bin/
	mkdir -p $(DIR)/objdump
	mkdir -p $(DIR)/log
	$(MAKE) -C $(DIR) ISA=$(ISA) ABI=$(ABI) SPIKE_ISA=$(ISA)
