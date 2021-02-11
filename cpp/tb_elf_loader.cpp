#include "memory_block.hpp"
#include "mem_body.hpp"

#include <cstring>
#include <bfd.h>
#include <dis-asm.h>
#include <elf.h>
#include <limits.h>
#include <stdlib.h>
#include <string>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <memory>
// #include <vpi_user.h>
#include <iostream>
#include <iomanip>
// #include <svdpi.h>

// BFD debug information
std::unique_ptr<FunctionTable> m_func_table;
std::unique_ptr<VariableTable> m_gvar_table;
std::unique_ptr<Memory> m_memory;

bool elf_load_finish = false;

Addr_t  m_tohost_addr, m_fromhost_addr;
bool    m_tohost_en = false, m_fromhost_en = false;

extern "C" int debug_tick(
    unsigned char *debug_req_valid,
    unsigned char debug_req_ready,
    int *debug_req_bits_addr,
    int *debug_req_bits_data)
{
  auto m_memory_ptr = m_memory.get();
  static auto m_it = m_memory_ptr->GetIterBegin();
  static Addr_t addr = 0;

  static int state = 0;

  if (debug_req_ready) {
    switch (state) {
      case 0 : {
        if (m_it != m_memory_ptr->GetIterEnd() &&
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
          fprintf(stderr, "ELF Loading ... Addr = %08x, Data = %08x\n",
                  *debug_req_bits_addr,
                  *debug_req_bits_data);

          addr += 4;
          if (addr >= m_it->second->GetBlockSize() && m_it != m_memory_ptr->GetIterEnd()) {
            m_it ++;
            addr = 0;
          }
        } else if (m_it == m_memory_ptr->GetIterEnd()) {
          state = 1;
          elf_load_finish = true;
        } else {
          m_it ++;
        }
        break;
      }
      default: {
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

bool g_dump_hex = false;
static void load_bitfile (bfd *b, asection *section, PTR data);
static void load_hex (bfd *b, asection *section, Memory *p_memory);


extern "C" int32_t
load_binary(const char* path_exec, const char* filename, bool is_load_dump)
{
  g_dump_hex = is_load_dump;
  m_memory = std::unique_ptr<Memory> (new Memory ());

  // open binary
  bfd *abfd = bfd_openr (filename, NULL);
  if (abfd == NULL) {
    perror (filename);
    return -1;
  }

  bfd_check_format (abfd, bfd_object);

  bfd_map_over_sections (abfd, load_bitfile, static_cast<void *>(m_memory.get()));

  // LoadFunctionTable (abfd);
  // LoadGVariableTable (abfd);

  /* Read Entry Point */
  int fd = open(filename, O_RDONLY);
  struct stat s;
  assert(fd != -1);
  if (fstat(fd, &s) < 0)
    abort();
  size_t size = s.st_size;

  char* buf = (char*)mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
  assert(buf != MAP_FAILED);
  close(fd);

  // assert(size >= sizeof(Elf64_Ehdr));
  // const Elf64_Ehdr* eh64 = (const Elf64_Ehdr*)buf;
  // assert(IS_ELF32(*eh64) || IS_ELF64(*eh64));

  Elf64_Ehdr* eh = (Elf64_Ehdr*)buf;


  Addr_t entry_address = eh->e_entry;

  const int reset_vec_size = 8;

  if (!strcmp(path_exec, "")) {
    char szTmp[32];
    char dtb_path_buf[PATH_MAX];
    sprintf(szTmp, "/proc/%d/exe", getpid());
    int bytes = readlink(szTmp, dtb_path_buf, PATH_MAX);
    if(bytes >= 0)
      dtb_path_buf[bytes] = '\0';

    std::string dtb_path_str = dtb_path_buf;
    int slash_pos = dtb_path_str.rfind("/");
    std::string dtb_path_str_dir = dtb_path_str.substr(0, slash_pos);
    std::string dtb_path_str_replace = dtb_path_str_dir + "/riscv64.dtb";

    FILE *dtb_fp;
    if ((dtb_fp = fopen(dtb_path_str_replace.c_str(), "r")) == NULL) {
      perror (dtb_path_str_replace.c_str());
      return -1;
    }

    // Byte_t dtb_buf;
    // Addr_t rom_addr = 0x00001020;
    // while (fread(&dtb_buf, sizeof(Byte_t), 1, dtb_fp) == 1) {
    //   StoreMemoryDebug<Byte_t> (rom_addr, &dtb_buf); // To Disable Trace Log
    //   rom_addr++;
    // }
  }

  return 0;
}


static void load_bitfile (bfd *b, asection *section, PTR data)
{
  Memory *p_memory = static_cast<Memory *>(data);

  if (section->flags & SEC_LINKER_CREATED) return;
  if ((section->flags & SEC_CODE) ||
      (section->flags & SEC_ALLOC)) {
    if (!strncmp (".plt", section->name, 4) ||
        !strncmp (".got", section->name, 4)) {
      return;
    }
    load_hex (b, section, p_memory);
  } else if (section->flags & SEC_DATA ||
             section->flags & SEC_HAS_CONTENTS) {
    if (!strncmp (".debug", section->name, 6) ||
      !strncmp (".comment", section->name, 8)) {
      return;
    }

    load_hex (b, section, p_memory);
  }

  return;
}


static void load_hex (bfd *b, asection *section, Memory *p_memory)
{
  int size = bfd_section_size (b, section);
  std::unique_ptr<Byte_t[]> buf (new Byte_t[size]);

  if (!bfd_get_section_contents (b, section, buf.get(), 0, size))
    return;

  /* do hex dump of data */
  for (int i = 0; i < size; i+= 16) {
    int j;

    Addr_t addr = section->vma + i;
    if (g_dump_hex == true) {
      std::stringstream str;
      str << std::hex << std::setw(16) << std::setfill('0') << addr;
      fprintf (stderr, "%s:  ", str.str().c_str());
    }
    for (j = 0;j < 16 && (i+j) < size; j++) {
      if (g_dump_hex == true) {
        fprintf (stderr, "%02x ", static_cast<UByte_t>(buf[i+j]) & 0x00ff);
      }
      p_memory->StoreMemory<Byte_t> (addr+j, static_cast<Byte_t *>(&buf[i+j]));
    }
    if (g_dump_hex == true) {
      for (; j < 16; j++) {
        fprintf (stderr, "   ");
      }
      fprintf (stderr, "  ");
      for (j = 0; j < 16 && j+i < size; j++) {
        fprintf (stderr, "%c", isprint (buf[i+j]) ? buf[i+j] : '.');
      }
      fprintf (stderr, "\n");
    }
  }

  return;
}
