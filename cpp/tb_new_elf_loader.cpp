#include "memory_block.hpp"
#include "mem_body.hpp"

#include <libelf.h>
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

bool g_dump_hex = false;
std::unique_ptr<Memory> g_memory;

Addr_t  m_tohost_addr, m_fromhost_addr;
bool    m_tohost_en = false, m_fromhost_en = false;

extern "C" int load_binary(
    char const* path_exec,
    char const* filename,
    bool is_load_dump);

static void failure()
{
  (void) fprintf(stderr, "%s\n", elf_errmsg(elf_errno()));
  exit(EXIT_FAILURE);
}

void dump_segment (const char* segname, int fd);

Elf_Scn    *scn;
Elf_Data   *data;
Elf64_Ehdr *ehdr;
Elf64_Phdr *phdr;

extern "C" int
load_binary(char const* path_exec,
            char const* filename,
            bool is_load_dump)
{
  g_dump_hex = is_load_dump;
  g_memory = std::unique_ptr<Memory> (new Memory ());

  int fd;
  if ((fd = open(filename, O_RDONLY)) == -1) {
    printf ("Fatal error. Can not open specified ELF file.\n");
    exit(1);
  }

  Elf *          elf;
  /* Obtain the ELF descriptor */
  (void) elf_version(EV_CURRENT);
  if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
    failure();

  if (((ehdr = elf64_getehdr(elf)) == NULL) ||
      ((scn  = elf_getscn(elf, ehdr->e_shstrndx)) == NULL) ||
      ((data = elf_getdata(scn, NULL)) == NULL) ||
      ((phdr = elf64_getphdr(elf)) == NULL))
    failure();

  uint64_t elf_p_addr = 0;
  uint64_t elf_v_addr = 0;

  elf_p_addr = phdr->p_paddr;
  elf_v_addr = phdr->p_vaddr;

  fprintf(stderr, "elf_p_addr = %012lx\n", elf_p_addr);
  fprintf(stderr, "elf_v_addr = %012lx\n", elf_v_addr);

  dump_segment (".text", fd);

  return 0;
}


void dump_segment (const char* segname, int fd)
{
  unsigned int cnt;
  Elf * elf;
  Elf64_Shdr * shdr;
  Elf_Data * datapoint;
  int count, count2;
  Byte_t * buffer;
  unsigned int valsRead;
  unsigned long long base;
  char * identity;
  size_t * ptr;

  if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
    failure();
  /* Traverse input filename, printing each section */
  for (cnt = 1, scn = NULL; (scn = elf_nextscn(elf, scn))!=NULL; cnt++) {
    if ((shdr = elf64_getshdr(scn)) == NULL)
      failure();
    if (!strncmp ((char *)data->d_buf + shdr->sh_name,
				   segname,strlen(segname)) &&
        strlen(segname) == strlen((char *)data->d_buf + shdr->sh_name)) {

      lseek (fd,shdr->sh_offset,SEEK_SET);
      buffer = (Byte_t *) malloc ((shdr->sh_size)*sizeof(unsigned char));
      valsRead=read(fd,buffer, shdr->sh_size);

      base = phdr->p_paddr;

      ptr = (size_t *)malloc(EI_NIDENT);
      identity = elf_getident(elf, ptr);
      {
        /* Output endian indication for this segment */
        char	endian[32];
        switch (identity[EI_DATA]) {
          case 1:
            strcpy(endian, "Endian Little");
            break;
          case 2:
            strcpy(endian, "Endian Big");
            break;
          default:
            strcpy(endian, "Endian Unknown");
            break;
        }
        fprintf (stderr, "# %s\n", endian);
        fprintf (stderr, "%s\n", endian);
      }

      for(count=0; count < valsRead; count=count+4) {
        fprintf (stderr,"%08x: ", base);

        base = base + 4;
        switch (identity[EI_DATA]) {

          case 1:	/* Little endian */
            for (count2=3;count2>-1;count2--) {
              fprintf (stderr,"%.2x",static_cast<UByte_t>(buffer[count+count2]));
              g_memory->StoreMemory<Byte_t> (base - 4 + count + count2, static_cast<Byte_t *>(&buffer[count+count2]));
            }
            fprintf (stderr,"\n");
            break;

          case 2:	/* Big endian */
            for (count2=0;count2<4;count2++) {
              fprintf (stderr,"%.2x",static_cast<UByte_t>(buffer[count+count2]));
              g_memory->StoreMemory<Byte_t> (base - 4 + count + count2, static_cast<Byte_t *>(&buffer[count+count2]));
            }
            fprintf (stderr,"\n");
            break;

          default:
            printf ("Undetermined Endianness.  Fatal error.\n");
            exit(EXIT_FAILURE);
        }
      }
      free(ptr);
    }
  }
}
