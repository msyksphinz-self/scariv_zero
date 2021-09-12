#include <stdio.h>
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
#include <algorithm>
#include <functional>

static void failure()
{
  (void) fprintf(stderr, "Error: %s\n", elf_errmsg(elf_errno()));
  exit(EXIT_FAILURE);
}

int dump_bytewidth = 32;

void dump_segment (const char* segname, int fd);

Elf_Scn    *scn;
Elf_Data   *data;
Elf64_Ehdr *ehdr;
Elf64_Phdr *phdr;

int main(int argc, char **argv)
{
  int fd;
  if ((fd = open(argv[1], O_RDONLY)) == -1) {
    printf ("Fatal error. Can not open specified ELF file.\n");
    exit(1);
  }
  char *e;
  dump_bytewidth = strtol(argv[2], &e, 10);

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

  dump_segment (".text", fd);
  dump_segment (".text.init", fd);
  dump_segment (".text.startup", fd);
  dump_segment (".data", fd);
  dump_segment (".rodata", fd);
  dump_segment (".rodata.str1.8", fd);

  return 0;
}


void dump_segment (const char* segname, int fd)
{
  unsigned int cnt;
  Elf * elf;
  Elf64_Shdr * shdr;
  Elf_Data * datapoint;
  int count, count2;
  int8_t * buffer;
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
      buffer = (int8_t *) malloc ((shdr->sh_size)*sizeof(unsigned char));
      memset (buffer, 0, (shdr->sh_size)*sizeof(unsigned char));
      valsRead=read(fd,buffer, shdr->sh_size);

      // base = phdr->p_paddr;
      base = shdr->sh_addr;

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
        // fprintf (stderr, "# %s\n", endian);
      }

      fprintf (stdout,"@%08lx // %08lx\n", base / dump_bytewidth, base);
      for(count=0; count < valsRead; count=count+dump_bytewidth) {

        base = base + dump_bytewidth;
        switch (identity[EI_DATA]) {

          case 1: {	/* Little endian */
            int max_count = valsRead - count < dump_bytewidth ? valsRead - count : dump_bytewidth;
            for (count2 = max_count-1;count2 >= 0;count2--) {
              fprintf (stdout,"%.2x",static_cast<uint8_t>(buffer[count+count2]));
            }
            fprintf (stdout,"\n");
            break;
          }
          case 2:	/* Big endian */
            for (count2=0;count2<4;count2++) {
              fprintf (stdout,"%.2x",static_cast<uint8_t>(buffer[count+count2]));
            }
            fprintf (stdout,"\n");
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
