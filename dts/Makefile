XLEN = 64
EXT = imac
SVMODE = svxx

ifeq ($(XLEN), 64)
	SVMODE = sv39
else
	SVMODE = sv32
endif

build: dts_skelenton.dts bootrom.S
	riscv64-unknown-elf-as bootrom.S -o bootrom.o
	riscv64-unknown-elf-ld bootrom.o -o bootrom.elf -Tlink.ld
	objcopy -I elf64-little  -O binary --only-section .text bootrom.elf bootrom.bin
	sed 's/|XLEN|/$(XLEN)/g' dts_skelenton.dts | \
		sed 's/|EXTENSION|/$(EXT)/g' | \
		sed 's/|SVMODE|/$(SVMODE)/g' > rv$(XLEN)$(EXT).dts
	dd if=/dev/zero of=dummy.bin bs=80 count=1
	dtc -@ -O dtb rv$(XLEN)$(EXT).dts -o rv$(XLEN)$(EXT).dtb
	cat bootrom.bin rv$(XLEN)$(EXT).dtb dummy.bin > bootrom.img
	objcopy -I binary -O verilog --verilog-data-width 16 bootrom.img bootrom.hex

clean:
	rm -rf bootrom.verilog
	rm -rf bootrom.srec
	rm -rf bootrom.o
	rm -rf bootrom.img
	rm -rf bootrom.elf
	rm -rf bootrom.dump
	rm -rf bootrom.bin
	rm -rf bootrom.hex
	rm -rf dts_skelenton_tmp.dts
	rm -rf *.dtb
