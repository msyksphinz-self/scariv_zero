#include "memory_block.hpp"
#include "mem_body.hpp"

bool elf_load_finish = false;

extern std::unique_ptr<Memory> g_memory;

extern "C" int debug_tick(
    unsigned char *debug_req_valid,
    unsigned char debug_req_ready,
    int *debug_req_bits_addr,
    int *debug_req_bits_data)
{
  auto g_memory_ptr = g_memory.get();
  static auto m_it = g_memory_ptr->GetIterBegin();
  static Addr_t addr = 0;

  static int state = 0;

  if (debug_req_ready) {
    switch (state) {
      case 0 : {
        if (m_it != g_memory_ptr->GetIterEnd() &&
            m_it->second->GetBaseAddr() >= 0x80000000 &&
            addr < m_it->second->GetBlockSize()) {
          uint32_t data = 0;
          for (int i = 0; i < 4; i++) {
            uint8_t byte = m_it->second->ReadByte (static_cast<Addr_t>(addr + i));
            data = byte << (i * 8) | data;
          }

          *debug_req_valid     = 1;
          *debug_req_bits_addr = addr + m_it->second->GetBaseAddr();
          *debug_req_bits_data = data;
          // fprintf(stderr, "ELF Loading ... Addr = %08x, Data = %08x\n",
          //         *debug_req_bits_addr,
          //         *debug_req_bits_data);

          addr += 4;
          if (addr >= m_it->second->GetBlockSize() && m_it != g_memory_ptr->GetIterEnd()) {
            m_it ++;
            addr = 0;
          }
        } else if (m_it == g_memory_ptr->GetIterEnd()) {

          // fprintf(stderr, "ELF2 Loading ... Addr = %08x, Data = %08x\n",
          //         *debug_req_bits_addr,
          //         *debug_req_bits_data);

          state = 1;
          elf_load_finish = true;
        } else {
          m_it ++;
        }
        break;
      }
      default: {
        // fprintf(stderr, "ELF Load Not Ready\n");
        *debug_req_valid = 0;
        *debug_req_bits_addr = 0;
        *debug_req_bits_data = 0;
      }
    }
  } else {
    *debug_req_valid = 0;
    *debug_req_bits_addr = 0;
    *debug_req_bits_data = 0;
  }

  return 0;
}
