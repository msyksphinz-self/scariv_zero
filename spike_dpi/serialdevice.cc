// See LICENSE for license details.
#ifndef _RISCV_SERIALDEVICE_H
#define _RISCV_SERIALDEVICE_H

#include <riscv/mmio_plugin.h>

#include "abstract_device.h"
#include "mmu.h"

class serialdevice_t : public abstract_device_t {
  FILE *serial_log_fp;
 public:
  serialdevice_t(std::string name);
  bool load(reg_t addr, size_t len, uint8_t* bytes);
  bool store(reg_t addr, size_t len, const uint8_t* bytes);
 private:
};

serialdevice_t::serialdevice_t(std::string name)
{
  serial_log_fp = fopen ("spike_serial.log", "w");
  std::cerr << "serialdevice: " << name << " loaded\n";
}

bool serialdevice_t::load(reg_t addr, size_t len, uint8_t* bytes)
{
  // std::cerr << "serialdevice_t::load called : addr = " << std::hex << addr << '\n';
  switch (addr) {
    case 5  : bytes[0] = 0x20; break;
    default : bytes[0] = 0x00; break;
  }

  return true;
}

bool serialdevice_t::store(reg_t addr, size_t len, const uint8_t* bytes)
{
  // std::cerr << "serialdevice_t::store called : addr = " << std::hex << addr << '\n';
  if (bytes[0] >= 0x20 ||
      bytes[0] == 0x0a ||  // LF
      bytes[0] == 0x0d     // CR
      ) {
    fprintf (serial_log_fp, "%c", bytes[0]);
    fflush (serial_log_fp);
  }
  return true;
}

static mmio_plugin_registration_t<serialdevice_t> serialdevice_mmio_plugin_registration("serialdevice");

#endif // _RISCV_SERIALDEVICE_H
