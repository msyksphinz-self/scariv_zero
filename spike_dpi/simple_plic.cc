// See LICENSE for license details.
#ifndef _RISCV_SIMPLEPLIC_H
#define _RISCV_SIMPLEPLIC_H

#include <riscv/mmio_plugin.h>

#include "abstract_device.h"
#include "mmu.h"

class simpleplic_t : public abstract_device_t {
 public:
  simpleplic_t(std::string name);
  bool load(reg_t addr, size_t len, uint8_t* bytes);
  bool store(reg_t addr, size_t len, const uint8_t* bytes);
 private:
};

simpleplic_t::simpleplic_t(std::string name)
{
  std::cerr << "simpleplic: " << name << " loaded\n";
}

bool simpleplic_t::load(reg_t addr, size_t len, uint8_t* bytes)
{
  std::cerr << "simple PLIC_t::load called : addr = " << std::hex << addr << '\n';
  switch (addr) {
    default : bytes[0] = 0x00; break;
  }

  return true;
}

bool simpleplic_t::store(reg_t addr, size_t len, const uint8_t* bytes)
{
  std::cerr << "simple PLIC_t::store called : addr = " << std::hex << addr << '\n';

  return true;
}

static mmio_plugin_registration_t<simpleplic_t> simpleplic_mmio_plugin_registration("simpleplic");

#endif // _RISCV_SIMPLEPLIC_H
