#include "memory_block.hpp"
#include "mem_body.hpp"
#include "tb_elf_loader.h"

// #include <libelf.h>
#include <cstring>
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
#include <iostream>
#include <iomanip>
#include <algorithm>
#include <functional>

bool g_dump_hex = false;
std::unique_ptr<Memory> g_memory;

extern FILE *compare_log_fp;
Addr_t  tohost_addr;
bool    tohost_en;

// static void failure()
// {
//   (void) fprintf(stderr, "Error: %s\n", elf_errmsg(elf_errno()));
//   exit(EXIT_FAILURE);
// }
//
// void dump_segment (const char* segname, int fd);
//
// Elf_Scn    *scn;
// Elf_Data   *data;
// Elf64_Ehdr *ehdr;
// Elf64_Phdr *phdr;
//
// extern "C" int
// load_binary(char const* path_exec,
//             char const* filename,
//             bool is_load_dump)
// {
//   g_dump_hex = is_load_dump;
//   g_memory = std::unique_ptr<Memory> (new Memory ());
//
//   int fd;
//   if ((fd = open(filename, O_RDONLY)) == -1) {
//     printf ("Fatal error. Can not open specified ELF file.\n");
//     exit(1);
//   }
//
//   Elf *          elf;
//   /* Obtain the ELF descriptor */
//   (void) elf_version(EV_CURRENT);
//   if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
//     failure();
//
//   if (((ehdr = elf64_getehdr(elf)) == NULL) ||
//       ((scn  = elf_getscn(elf, ehdr->e_shstrndx)) == NULL) ||
//       ((data = elf_getdata(scn, NULL)) == NULL) ||
//       ((phdr = elf64_getphdr(elf)) == NULL))
//     failure();
//
//   uint64_t elf_p_addr = 0;
//   uint64_t elf_v_addr = 0;
//
//   elf_p_addr = phdr->p_paddr;
//   elf_v_addr = phdr->p_vaddr;
//
//   // fprintf(stderr, "elf_p_addr = %012lx\n", elf_p_addr);
//   // fprintf(stderr, "elf_v_addr = %012lx\n", elf_v_addr);
//
//   dump_segment (".text", fd);
//   dump_segment (".text.init", fd);
//   dump_segment (".text.startup", fd);
//   dump_segment (".data", fd);
//   dump_segment (".rodata", fd);
//   dump_segment (".rodata.str1.8", fd);
//
//   if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
//     failure();
//   Elf64_Shdr * shdr;
//   unsigned int cnt;
//   for (cnt = 1, scn = NULL; (scn = elf_nextscn(elf, scn))!=NULL; cnt++) {
//     if ((shdr = elf64_getshdr(scn)) == NULL)
//       failure();
//     if (!strncmp ((char *)data->d_buf + shdr->sh_name,
//                   ".tohost", strlen(".tohost")) &&
//         strlen(".tohost") == strlen((char *)data->d_buf + shdr->sh_name)) {
//       tohost_en = true;
//       tohost_addr = shdr->sh_addr;
//
//       fprintf(compare_log_fp, "Set ToHost Addr %0lx\n", tohost_addr);
//
//       break;
//     }
//   }
//   if (!tohost_en) {
//     tohost_en = 1;
//     tohost_addr = 0x80001000;
//
//     fprintf(compare_log_fp, "Not found .tohost. Set Addr %0lx\n", tohost_addr);
//   }
//
//   return 0;
// }
//
//
// void dump_segment (const char* segname, int fd)
// {
//   unsigned int cnt;
//   Elf * elf;
//   Elf64_Shdr * shdr;
//   Elf_Data * datapoint;
//   int count, count2;
//   Byte_t * buffer;
//   unsigned int valsRead;
//   unsigned long long base;
//   char * identity;
//   size_t * ptr;
//
//   if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
//     failure();
//   /* Traverse input filename, printing each section */
//   for (cnt = 1, scn = NULL; (scn = elf_nextscn(elf, scn))!=NULL; cnt++) {
//     if ((shdr = elf64_getshdr(scn)) == NULL)
//       failure();
//     if (!strncmp ((char *)data->d_buf + shdr->sh_name,
// 				   segname,strlen(segname)) &&
//         strlen(segname) == strlen((char *)data->d_buf + shdr->sh_name)) {
//
//       lseek (fd,shdr->sh_offset,SEEK_SET);
//       buffer = (Byte_t *) malloc ((shdr->sh_size)*sizeof(unsigned char));
//       memset (buffer, 0, (shdr->sh_size)*sizeof(unsigned char));
//       valsRead=read(fd,buffer, shdr->sh_size);
//
//       // base = phdr->p_paddr;
//       base = shdr->sh_addr;
//
//       ptr = (size_t *)malloc(EI_NIDENT);
//       identity = elf_getident(elf, ptr);
//       {
//         /* Output endian indication for this segment */
//         char	endian[32];
//         switch (identity[EI_DATA]) {
//           case 1:
//             strcpy(endian, "Endian Little");
//             break;
//           case 2:
//             strcpy(endian, "Endian Big");
//             break;
//           default:
//             strcpy(endian, "Endian Unknown");
//             break;
//         }
//         // fprintf (stderr, "# %s\n", endian);
//         // fprintf (stderr, "%s\n", endian);
//       }
//
//       for(count=0; count < valsRead; count=count+4) {
//         // fprintf (stderr,"%08lx: ", base);
//
//         base = base + 4;
//         switch (identity[EI_DATA]) {
//
//           case 1: {	/* Little endian */
//             int max_count = valsRead - count < 4 ? valsRead - count : 4;
//             for (count2 = max_count-1;count2 >= 0;count2--) {
//               // fprintf (stderr,"%.2x",static_cast<UByte_t>(buffer[count+count2]));
//               ccZZZZ
//             }
//             // fprintf (stderr,"\n");
//             break;
//           }
//           case 2:	/* Big endian */
//             for (count2=0;count2<4;count2++) {
//               // fprintf (stderr,"%.2x",static_cast<UByte_t>(buffer[count+count2]));
//               g_memory->StoreMemory<Byte_t> (base - 4 + count + count2, static_cast<Byte_t *>(&buffer[count+count2]));
//             }
//             // fprintf (stderr,"\n");
//             break;
//
//           default:
//             printf ("Undetermined Endianness.  Fatal error.\n");
//             exit(EXIT_FAILURE);
//         }
//       }
//       free(ptr);
//     }
//   }
// }


#include "elf.h"
// #include "memif.h"
#include "byteorder.h"
#include <cstring>
#include <string>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <unistd.h>
#include <stdexcept>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <map>

#define MAX(a, b) ((a) > (b) ? (a) : (b))

extern "C" int
load_binary(char const* path_exec,
            char const* filename,
            bool is_load_dump)
// std::map<std::string, uint64_t> load_elf(const char* fn, memif_t* memif, reg_t* entry)
{

  int fd;
  if ((fd = open(filename, O_RDONLY)) == -1) {
    printf ("Fatal error. Can not open specified ELF file.\n");
    exit(1);
  }

  struct stat s;
  assert(fd != -1);
  if (fstat(fd, &s) < 0)
    abort();
  size_t size = s.st_size;

  char* buf = (char*)mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
  assert(buf != MAP_FAILED);
  close(fd);

  assert(size >= sizeof(Elf64_Ehdr));
  const Elf64_Ehdr* eh64 = (const Elf64_Ehdr*)buf;
  assert(IS_ELF32(*eh64) || IS_ELF64(*eh64));
  assert(IS_ELFLE(*eh64) || IS_ELFBE(*eh64));
  assert(IS_ELF_EXEC(*eh64));
  assert(IS_ELF_RISCV(*eh64) || IS_ELF_EM_NONE(*eh64));
  assert(IS_ELF_VCURRENT(*eh64));

  std::vector<uint8_t> zeros;
  // std::map<std::string, uint64_t> symbols;

  if (!g_memory) {
    g_memory = std::unique_ptr<Memory> (new Memory ());
  }

  #define LOAD_ELF(ehdr_t, phdr_t, shdr_t, sym_t, bswap) do { \
    ehdr_t* eh = (ehdr_t*)buf; \
    phdr_t* ph = (phdr_t*)(buf + bswap(eh->e_phoff)); \
    /* *entry = bswap(eh->e_entry); */ \
    assert(size >= bswap(eh->e_phoff) + bswap(eh->e_phnum)*sizeof(*ph)); \
    for (unsigned i = 0; i < bswap(eh->e_phnum); i++) {			\
      if(bswap(ph[i].p_type) == PT_LOAD && bswap(ph[i].p_memsz)) {	\
        if (bswap(ph[i].p_filesz)) {					\
          assert(size >= bswap(ph[i].p_offset) + bswap(ph[i].p_filesz)); \
          /* memif->write(bswap(ph[i].p_paddr), bswap(ph[i].p_filesz), (uint8_t*)buf + bswap(ph[i].p_offset));  */ \
          /* fprintf (stderr, "filesz = %d\n", ph[i].p_filesz); */\
          for (int b_idx = 0; b_idx < ph[i].p_filesz; b_idx++) { \
            /* fprintf(stderr, "addr = %08x, data = %02x\n", ph[i].p_paddr + b_idx, (uint8_t)(*(buf + bswap(ph[i].p_offset) + b_idx))); */ \
            g_memory->StoreMemory<Byte_t> (ph[i].p_paddr + b_idx, (Byte_t *)(buf + bswap(ph[i].p_offset) + b_idx)); \
          } \
        } \
        zeros.resize(bswap(ph[i].p_memsz) - bswap(ph[i].p_filesz)); \
        /* fprintf(stderr, "addr2 = %08x, data = %01x\n", ph[i].p_paddr, (Byte_t*)buf + bswap(ph[i].p_offset)); */ \
        /* memif->write(bswap(ph[i].p_paddr) + bswap(ph[i].p_filesz), bswap(ph[i].p_memsz) - bswap(ph[i].p_filesz), &zeros[0]); */ \
      } \
    } \
    shdr_t* sh = (shdr_t*)(buf + bswap(eh->e_shoff)); \
    assert(size >= bswap(eh->e_shoff) + bswap(eh->e_shnum)*sizeof(*sh)); \
    assert(bswap(eh->e_shstrndx) < bswap(eh->e_shnum)); \
    assert(size >= bswap(sh[bswap(eh->e_shstrndx)].sh_offset) + bswap(sh[bswap(eh->e_shstrndx)].sh_size)); \
    char *shstrtab = buf + bswap(sh[bswap(eh->e_shstrndx)].sh_offset);	\
    unsigned strtabidx = 0, symtabidx = 0; \
    for (unsigned i = 0; i < bswap(eh->e_shnum); i++) {		     \
      unsigned max_len = bswap(sh[bswap(eh->e_shstrndx)].sh_size) - bswap(sh[i].sh_name); \
      assert(bswap(sh[i].sh_name) < bswap(sh[bswap(eh->e_shstrndx)].sh_size));	\
      assert(strnlen(shstrtab + bswap(sh[i].sh_name), max_len) < max_len); \
      if (bswap(sh[i].sh_type) & SHT_NOBITS) continue; \
      assert(size >= bswap(sh[i].sh_offset) + bswap(sh[i].sh_size)); \
      if (strcmp(shstrtab + bswap(sh[i].sh_name), ".strtab") == 0) \
        strtabidx = i; \
      if (strcmp(shstrtab + bswap(sh[i].sh_name), ".symtab") == 0) \
        symtabidx = i; \
    } \
    if (strtabidx && symtabidx) { \
      char* strtab = buf + bswap(sh[strtabidx].sh_offset); \
      sym_t* sym = (sym_t*)(buf + bswap(sh[symtabidx].sh_offset)); \
      for (unsigned i = 0; i < bswap(sh[symtabidx].sh_size)/sizeof(sym_t); i++) { \
        unsigned max_len = bswap(sh[strtabidx].sh_size) - bswap(sym[i].st_name); \
        assert(bswap(sym[i].st_name) < bswap(sh[strtabidx].sh_size));	\
        assert(strnlen(strtab + bswap(sym[i].st_name), max_len) < max_len); \
        /* symbols[strtab + bswap(sym[i].st_name)] = bswap(sym[i].st_value); */ \
        /* fprintf(stderr, "symbols = %0s, symbolname = %08x\n", strtab + sym[i].st_name, sym[i].st_value); */ \
        if (!strncmp(strtab + sym[i].st_name, "tohost", MAX(strlen(strtab + sym[i].st_name), strlen("tohost")))) { \
          tohost_en = true; \
          tohost_addr = sym[i].st_value; \
          fprintf(compare_log_fp, "Set ToHost Addr %0lx\n", tohost_addr); \
        } \
      } \
    } \
    if (!tohost_en) { \
      tohost_en = 1; \
      tohost_addr = 0x80001000; \
      fprintf (compare_log_fp, "Not found .tohost. Set Addr %0lx\n", tohost_addr);  \
    } \
  } while(0)

  if (IS_ELFLE(*eh64)) {
    // memif->set_target_endianness(memif_endianness_little);
    if (IS_ELF32(*eh64))
      LOAD_ELF(Elf32_Ehdr, Elf32_Phdr, Elf32_Shdr, Elf32_Sym, from_le);
    else
      LOAD_ELF(Elf64_Ehdr, Elf64_Phdr, Elf64_Shdr, Elf64_Sym, from_le);
  } else {
#ifndef RISCV_ENABLE_DUAL_ENDIAN
    throw std::invalid_argument("Specified ELF is big endian.  Configure with --enable-dual-endian to enable support");
#else
    memif->set_target_endianness(memif_endianness_big);
    if (IS_ELF32(*eh64))
      LOAD_ELF(Elf32_Ehdr, Elf32_Phdr, Elf32_Shdr, Elf32_Sym, from_be);
    else
      LOAD_ELF(Elf64_Ehdr, Elf64_Phdr, Elf64_Shdr, Elf64_Sym, from_be);
#endif
  }

  munmap(buf, size);

  // return symbols;
  return 0;
}
