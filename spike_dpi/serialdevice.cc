// See LICENSE for license details.
#ifndef _RISCV_SERIALDEVICE_H
#define _RISCV_SERIALDEVICE_H

#include <riscv/mmio_plugin.h>

#include "abstract_device.h"
#include "mmu.h"

class sim_t;
class bus_t;

void register_mmio_plugin(const char* name_cstr,
                          const mmio_plugin_t* mmio_plugin);

class serialdevice_t : public abstract_device_t {
 public:
  serialdevice_t(std::string name);
  bool load(reg_t addr, size_t len, uint8_t* bytes);
  bool store(reg_t addr, size_t len, const uint8_t* bytes);
 private:
};


serialdevice_t::serialdevice_t(std::string name)
{
  std::cerr << "serialdevice: " << name << " loaded\n";
}

bool serialdevice_t::load(reg_t addr, size_t len, uint8_t* bytes)
{
  // std::cerr << "serialdevice_t::load called : addr = " << std::hex << addr << '\n';
  switch (addr) {
    case 5 : return 0x20;
    default : return 0x0;
  }

  return true;
}

bool serialdevice_t::store(reg_t addr, size_t len, const uint8_t* bytes)
{
  // std::cerr << "serialdevice_t::store called : addr = " << std::hex << addr << '\n';
  std::cout << bytes[0];
  return true;
}

extern "C" {
  static mmio_plugin_registration_t<serialdevice_t> serialdevice_mmio_plugin_registration("serialdevice");
}

#endif // _RISCV_SERIALDEVICE_H
