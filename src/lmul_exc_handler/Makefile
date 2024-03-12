all: lmul_exc_rom.S
	riscv64-unknown-elf-gcc -march=rv64imafdcv lmul_exc_rom.S -c -o lmul_exc_rom.o
	riscv64-unknown-elf-ld lmul_exc_rom.o -o lmul_exc_rom.elf -Tlink.ld
	objcopy -I elf64-little  -O binary --only-section .text lmul_exc_rom.elf lmul_exc_rom.bin
	./bin2hex.py --bit-width 128 lmul_exc_rom.bin lmul_exc_rom_w16.hex
	./bin2hex.py --bit-width 256 lmul_exc_rom.bin lmul_exc_rom_w32.hex
	./bin2hex.py --bit-width 512 lmul_exc_rom.bin lmul_exc_rom_w64.hex
	riscv64-unknown-elf-objcopy -I binary -O elf64-little lmul_exc_rom.bin lmul_exc_rom.bin.o
	cat lmul_exc_rom.bin| hexdump -v -e '"0x" 1/1 "%02X" ",\n"' > lmul_exc_rom.txt
