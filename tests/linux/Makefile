image: Image
	./../../dts/bin2hex.py --bit-width 128 $^ $@_w16.hex
	./../../dts/bin2hex.py --bit-width 256 $^ $@_w32.hex
	./../../dts/bin2hex.py --bit-width 512 $^ $@_w64.hex


spike_rootfs: spike_rootfs.cpio
	./../../dts/bin2hex.py --bit-width 128 $^ $@_w16.hex
	./../../dts/bin2hex.py --bit-width 256 $^ $@_w32.hex
	./../../dts/bin2hex.py --bit-width 512 $^ $@_w64.hex

hifive_rootfs: hifive_rootfs.cpio
	./../../dts/bin2hex.py --bit-width 128 $^ $@_w16.hex
	./../../dts/bin2hex.py --bit-width 256 $^ $@_w32.hex
	./../../dts/bin2hex.py --bit-width 512 $^ $@_w64.hex
