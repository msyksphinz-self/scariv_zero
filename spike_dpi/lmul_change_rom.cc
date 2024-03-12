// See LICENSE for license details.
#ifndef _RISCV_LMUL_CHANGE_ROM_H
#define _RISCV_LMUL_CHANGE_ROM_H

#include <riscv/mmio_plugin.h>

#include "abstract_device.h"
#include "mmu.h"

class lmul_change_rom_t : public abstract_device_t {
  FILE *lmul_change_log_fp;
  char ram[0x1000];
 public:
  lmul_change_rom_t(std::string name);
  bool load(reg_t addr, size_t len, uint8_t* bytes);
  bool store(reg_t addr, size_t len, const uint8_t* bytes);
 private:
  uint8_t DATA[1024] =
  {
#include "lmul_exc_rom.txt"
  };
};

lmul_change_rom_t::lmul_change_rom_t(std::string name)
{
  lmul_change_log_fp = fopen ("spike_lmul_change.log", "w");
  memcpy(ram, DATA, sizeof(DATA));
  std::cerr << "lmul_change_rom: " << name << " loaded\n";
}

bool lmul_change_rom_t::load(reg_t addr, size_t len, uint8_t* bytes)
{
  memcpy(bytes, &ram[addr], len);
  return true;
}

bool lmul_change_rom_t::store(reg_t addr, size_t len, const uint8_t* bytes)
{
  memcpy(&ram[addr], bytes, len);
  return true;
}

static mmio_plugin_registration_t<lmul_change_rom_t> lmul_change_rom_mmio_plugin_registration("lmul_change_rom");

#endif // _RISCV_LMUL_CHANGE_ROM_H
