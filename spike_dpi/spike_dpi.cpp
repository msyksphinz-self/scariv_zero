#include "spike_dpi.h"
#include "tb_elf_loader.h"
#include <string.h>

#include "sim.h"
// #include "mmu.h"
#include "disasm.h"

#include <dlfcn.h>
#include <fesvr/option_parser.h>
#include "remote_bitbang.h"
#include "cachesim.h"
#include "memtracer.h"
#include "extension.h"
#include "../VERSION"

FILE *compare_log_fp;
extern uint64_t  tohost_addr; // define in tb_elf_loader.cpp
extern bool    tohost_en;   // define in tb_elf_loader.cpp

sim_t *spike_core;
disassembler_t *disasm;

int argc;
const char *argv[20];
int g_rv_xlen = 0;
int g_rv_flen = 0;

static std::vector<std::pair<reg_t, mem_t*>> make_mems(const char* arg);
static void merge_overlapping_memory_regions(std::vector<std::pair<reg_t, mem_t*>>& mems);
// static void help(int exit_code = 1);

static void help(int exit_code = 1)
{
  fprintf(compare_log_fp, "Spike RISC-V ISA Simulator " SPIKE_VERSION "\n\n");
  fprintf(compare_log_fp, "usage: spike [host options] <target program> [target options]\n");
  fprintf(compare_log_fp, "Host Options:\n");
  fprintf(compare_log_fp, "  -p<n>                 Simulate <n> processors [default 1]\n");
  fprintf(compare_log_fp, "  -m<n>                 Provide <n> MiB of target memory [default 2048]\n");
  fprintf(compare_log_fp, "  -m<a:m,b:n,...>       Provide memory regions of size m and n bytes\n");
  fprintf(compare_log_fp, "                          at base addresses a and b (with 4 KiB alignment)\n");
  fprintf(compare_log_fp, "  -d                    Interactive debug mode\n");
  fprintf(compare_log_fp, "  -g                    Track histogram of PCs\n");
  fprintf(compare_log_fp, "  -l                    Generate a log of execution\n");
  fprintf(compare_log_fp, "  -h, --help            Print this help message\n");
  fprintf(compare_log_fp, "  -H                    Start halted, allowing a debugger to connect\n");
  fprintf(compare_log_fp, "  --isa=<name>          RISC-V ISA string [default %s]\n", DEFAULT_ISA);
  fprintf(compare_log_fp, "  --priv=<m|mu|msu>     RISC-V privilege modes supported [default %s]\n", DEFAULT_PRIV);
  fprintf(compare_log_fp, "  --varch=<name>        RISC-V Vector uArch string [default %s]\n", DEFAULT_VARCH);
  fprintf(compare_log_fp, "  --pc=<address>        Override ELF entry point\n");
  fprintf(compare_log_fp, "  --hartids=<a,b,...>   Explicitly specify hartids, default is 0,1,...\n");
  fprintf(compare_log_fp, "  --ic=<S>:<W>:<B>      Instantiate a cache model with S sets,\n");
  fprintf(compare_log_fp, "  --dc=<S>:<W>:<B>        W ways, and B-byte blocks (with S and\n");
  fprintf(compare_log_fp, "  --l2=<S>:<W>:<B>        B both powers of 2).\n");
  fprintf(compare_log_fp, "  --device=<P,B,A>      Attach MMIO plugin device from an --extlib library\n");
  fprintf(compare_log_fp, "                          P -- Name of the MMIO plugin\n");
  fprintf(compare_log_fp, "                          B -- Base memory address of the device\n");
  fprintf(compare_log_fp, "                          A -- String arguments to pass to the plugin\n");
  fprintf(compare_log_fp, "                          This flag can be used multiple times.\n");
  fprintf(compare_log_fp, "                          The extlib flag for the library must come first.\n");
  fprintf(compare_log_fp, "  --log-cache-miss      Generate a log of cache miss\n");
  fprintf(compare_log_fp, "  --extension=<name>    Specify RoCC Extension\n");
  fprintf(compare_log_fp, "  --extlib=<name>       Shared library to load\n");
  fprintf(compare_log_fp, "                        This flag can be used multiple times.\n");
  fprintf(compare_log_fp, "  --rbb-port=<port>     Listen on <port> for remote bitbang connection\n");
  fprintf(compare_log_fp, "  --dump-dts            Print device tree string and exit\n");
  fprintf(compare_log_fp, "  --disable-dtb         Don't write the device tree blob into memory\n");
  fprintf(compare_log_fp, "  --kernel=<path>       Load kernel flat image into memory\n");
  fprintf(compare_log_fp, "  --initrd=<path>       Load kernel initrd into memory\n");
  fprintf(compare_log_fp, "  --bootargs=<args>     Provide custom bootargs for kernel [default: console=hvc0 earlycon=sbi]\n");
  fprintf(compare_log_fp, "  --real-time-clint     Increment clint time at real-time rate\n");
  fprintf(compare_log_fp, "  --dm-progsize=<words> Progsize for the debug module [default 2]\n");
  fprintf(compare_log_fp, "  --dm-sba=<bits>       Debug bus master supports up to "
      "<bits> wide accesses [default 0]\n");
  fprintf(compare_log_fp, "  --dm-auth             Debug module requires debugger to authenticate\n");
  fprintf(compare_log_fp, "  --dmi-rti=<n>         Number of Run-Test/Idle cycles "
      "required for a DMI access [default 0]\n");
  fprintf(compare_log_fp, "  --dm-abstract-rti=<n> Number of Run-Test/Idle cycles "
      "required for an abstract command to execute [default 0]\n");
  fprintf(compare_log_fp, "  --dm-no-hasel         Debug module supports hasel\n");
  fprintf(compare_log_fp, "  --dm-no-abstract-csr  Debug module won't support abstract to authenticate\n");
  fprintf(compare_log_fp, "  --dm-no-halt-groups   Debug module won't support halt groups\n");
  fprintf(compare_log_fp, "  --dm-no-impebreak     Debug module won't support implicit ebreak in program buffer\n");

  exit(exit_code);
}

static void suggest_help()
{
  fprintf(compare_log_fp, "Try 'spike --help' for more information.\n");
  exit(1);
}


static unsigned long atoul_safe(const char* s)
{
  char* e;
  auto res = strtoul(s, &e, 10);
  if (*e)
    help();
  return res;
}

static unsigned long atoul_nonzero_safe(const char* s)
{
  auto res = atoul_safe(s);
  if (!res)
    help();
  return res;
}

static bool check_file_exists(const char *fileName)
{
  std::ifstream infile(fileName);
  return infile.good();
}

static std::ifstream::pos_type get_file_size(const char *filename)
{
  std::ifstream in(filename, std::ios::ate | std::ios::binary);
  return in.tellg();
}

static void read_file_bytes(const char *filename,size_t fileoff,
                            mem_t* mem, size_t memoff, size_t read_sz)
{
  std::ifstream in(filename, std::ios::in | std::ios::binary);
  in.seekg(fileoff, std::ios::beg);

  std::vector<char> read_buf(read_sz, 0);
  in.read(&read_buf[0], read_sz);
  mem->store(memoff, read_sz, (uint8_t*)&read_buf[0]);
}


void initial_spike (const char *filename, int rv_xlen, int rv_flen, int rv_amo)
{
  argv[0] = "spike_dpi";
  char *isa_str = (char *)malloc(sizeof(char) * 32);
  sprintf(isa_str, "rv%dim", rv_xlen);
  if (rv_amo) {
    strcat(isa_str, "a");
  }
  if (rv_flen >= 32) {
    strcat(isa_str, "f");
  }
  if (rv_flen >= 64) {
    strcat(isa_str, "d");
  }
  strcat(isa_str, "c");
  char *spike_isa_argv =(char *)malloc(sizeof(char) * 32);
  sprintf(spike_isa_argv, "--isa=%s", isa_str);
  argv[1] = spike_isa_argv;
  if (!(rv_xlen == 32 || rv_xlen == 64)) {
    fprintf(compare_log_fp, "RV_XLEN should be 32 or 64.\n");
    exit(-1);
  }
  if (!(rv_flen == 0 || rv_flen == 32 || rv_flen == 64)) {
    fprintf(compare_log_fp, "RV_FLEN should be 0, 32 or 64.\n");
    exit(1);
  }
  int arg_max = 2;
  g_rv_xlen = rv_xlen;
  g_rv_flen = rv_flen;
  // argv[arg_max++] = "-m0x80000000:0x10000,"     \
  //     "0x0000000000125000:0x1000," \
  //     "0x0000000000129000:0x1000," \
  //     "0x000000000012e000:0x1000," \
  //     "0x000000000012e900:0x1000," \
  //     "0x000000000016d000:0x1000," \
  //     "0x000000000017b000:0x1000," \
  //     "0x0000000000185000:0x1000," \
  //     "0x0000000000199000:0x1000," \
  //     "0x00000000001b0000:0x1000," \
  //     "0x00000000001c0000:0x1000," \
  //     "0x00000000001e9000:0x1000," \
  //     "0x00000000001f8000:0x1000," \
  //     "0x0000000000200000:0x1000," \
  //     "0x0000000000204000:0x1000," \
  //     "0x0000000000231000:0x1000," \
  //     "0x000000000027a000:0x1000," \
  //     "0x000000000027e000:0x1000," \
  //     "0x000000000029c000:0x1000," \
  //     "0x00000000002e9000:0x1000," \
  //     "0x000000000036b000:0x1000," \
  //     "0x000000000039b000:0x1000," \
  //     "0x00000000003d3000:0x1000," \
  //     "0x000000000044d000:0x1000," \
  //     "0x00000000004a1000:0x1000," \
  //     "0x00000000004c7000:0x1000," \
  //     "0x000000000057f000:0x1000," \
  //     "0x0000000000599000:0x1000," \
  //     "0x00000000005c1000:0x1000," \
  //     "0x0000000000617000:0x1000," \
  //     "0x0000000000726000:0x1000," \
  //     "0x000000000072a000:0x1000," \
  //     "0x000000000073f000:0x1000," \
  //     "0x00000000007ae000:0x1000," \
  //     "0x00000000007bcb00:0x1000," \
  //     "0x00000000008e6000:0x1000," \
  //     "0x00000000008e6400:0x1000," \
  //     "0x00000000009e1000:0x1000," \
  //     "0x00000000009f9000:0x1000," \
  //     "0x0000000000bc0000:0x1000," \
  //     "0x0000000000e4a000:0x1000," \
  //     "0x0000000000f38000:0x1000," \
  //     "0x0000000000f49000:0x1000," \
  //     "0x0000000001146000:0x1000," \
  //     "0x0000000001158000:0x1000," \
  //     "0x0000000001193000:0x1000," \
  //     "0x0000000001280000:0x1000," \
  //     "0x0000000001298000:0x1000," \
  //     "0x00000000014e8000:0x1000," \
  //     "0x0000000001616000:0x1000," \
  //     "0x000000000188c000:0x1000," \
  //     "0x0000000001967000:0x1000," \
  //     "0x0000000001b3a000:0x1000," \
  //     "0x0000000001bb4000:0x1000," \
  //     "0x0000000001cb3000:0x1000," \
  //     "0x0000000002526000:0x1000," \
  //     "0x000000000279d000:0x1000," \
  //     "0x00000000029b4000:0x1000," \
  //     "0x0000000002de6000:0x1000," \
  //     "0x0000000002df0000:0x1000," \
  //     "0x00000000031dd000:0x1000," \
  //     "0x0000000003350000:0x1000," \
  //     "0x0000000003942000:0x1000," \
  //     "0x0000000003bcc000:0x1000," \
  //     "0x0000000003d16000:0x1000," \
  //     "0x0000000004a56f00:0x1000," \
  //     "0x00000000051d0000:0x1000," \
  //     "0x0000000005382000:0x1000," \
  //     "0x0000000005671000:0x1000," \
  //     "0x0000000005a99000:0x1000," \
  //     "0x000000000633a000:0x1000," \
  //     "0x0000000007066000:0x1000," \
  //     "0x0000000007081000:0x1000," \
  //     "0x0000000007292000:0x1000," \
  //     "0x0000000007ab0000:0x1000," \
  //     "0x0000000007b21000:0x1000," \
  //     "0x0000000007cc5000:0x1000," \
  //     "0x0000000007d1a000:0x1000," \
  //     "0x0000000007ef2f00:0x1000," \
  //     "0x0000000007fcb100:0x1000," \
  //     "0x0000000008a4f000:0x1000," \
  //     "0x000000000ae80000:0x1000," \
  //     "0x000000000bf50000:0x1000," \
  //     "0x000000000c770000:0x1000," \
  //     "0x000000000cc77000:0x1000," \
  //     "0x000000000ccdf000:0x1000," \
  //     "0x000000000ce68000:0x1000," \
  //     "0x000000000d035000:0x1000," \
  //     "0x000000000d6a7d00:0x1000," \
  //     "0x000000000ef64000:0x1000," \
  //     "0x000000000f212000:0x1000," \
  //     "0x000000000f2df000:0x1000," \
  //     "0x000000000f388000:0x1000," \
  //     "0x000000000f579000:0x1000," \
  //     "0x000000000f8d3000:0x1000," \
  //     "0x000000000fde8000:0x1000," \
  //     "0x0000000010925000:0x1000," \
  //     "0x0000000013e12000:0x1000," \
  //     "0x00000000155ed000:0x1000," \
  //     "0x0000000015dc1100:0x1000," \
  //     "0x0000000017891000:0x1000," \
  //     "0x0000000017cc8000:0x1000," \
  //     "0x000000001ab09000:0x1000," \
  //     "0x000000001ae8f000:0x1000," \
  //     "0x000000001bd52000:0x1000," \
  //     "0x000000001d047000:0x1000," \
  //     "0x000000001d563000:0x1000," \
  //     "0x000000001e339000:0x1000," \
  //     "0x000000001ecb2000:0x1000," \
  //     "0x000000001f1b0000:0x1000," \
  //     "0x000000001fe0a000:0x1000," \
  //     "0x000000001fe73900:0x1000," \
  //     "0x000000001ff0c000:0x1000," \
  //     "0x000000002182d000:0x1000," \
  //     "0x0000000027bdf000:0x1000," \
  //     "0x00000000289f4000:0x1000," \
  //     "0x0000000030194000:0x1000," \
  //     "0x00000000324bc000:0x1000," \
  //     "0x00000000347fdf00:0x1000," \
  //     "0x0000000037f5a800:0x1000," \
  //     "0x000000003b9da000:0x1000," \
  //     "0x000000003d11a000:0x1000," \
  //     "0x0000000043755000:0x1000," \
  //     "0x0000000048915000:0x1000," \
  //     "0x0000000049066000:0x1000," \
  //     "0x000000004bba9000:0x1000," \
  //     "0x0000000058448000:0x1000," \
  //     "0x0000000063f22000:0x1000," \
  //     "0x0000000065668000:0x1000," \
  //     "0x0000000066f56000:0x1000," \
  //     "0x00000000686e7000:0x1000," \
  //     "0x0000000068893000:0x1000," \
  //     "0x000000006bdc3000:0x1000," \
  //     "0x00000000724d9000:0x1000," \
  //     "0x00000000751a6c00:0x1000," \
  //     "0x0000000075fbf000:0x1000," \
  //     "0x000000007764f000:0x1000," \
  //     "0x000000007a631000:0x1000," \
  //     "0x0000000080000000:0x1000," \
  //     "0x0000000080001000:0x1000," \
  //     "0x0000000080002000:0x1000," \
  //     "0x0000000080030000:0x1000," \
  //     "0x0000000085222000:0x1000," \
  //     "0x0000000091873000:0x1000," \
  //     "0x0000000092a92000:0x1000," \
  //     "0x00000000942da000:0x1000," \
  //     "0x00000000a0886000:0x1000," \
  //     "0x00000000ac4c3000:0x1000," \
  //     "0x00000000ae06a000:0x1000," \
  //     "0x00000000b341b000:0x1000," \
  //     "0x00000000be39a000:0x1000," \
  //     "0x00000000c6d90000:0x1000," \
  //     "0x00000000cdbe3000:0x1000," \
  //     "0x00000000e26cb000:0x1000," \
  //     "0x00000000e2c54000:0x1000," \
  //     "0x00000000eec72000:0x1000," \
  //     "0x00000000f11c5000:0x1000," \
  //     "0x0000000102156000:0x1000," \
  //     "0x000000010a4cc000:0x1000," \
  //     "0x0000000117989000:0x1000," \
  //     "0x000000011b3e2300:0x1000," \
  //     "0x0000000123612c00:0x1000," \
  //     "0x0000000125fb9000:0x1000," \
  //     "0x00000001903ea000:0x1000," \
  //     "0x00000001a1a8f000:0x1000," \
  //     "0x00000001b8250000:0x1000," \
  //     "0x00000001d2c67000:0x1000," \
  //     "0x00000001e7406000:0x1000," \
  //     "0x00000001f1809500:0x1000," \
  //     "0x00000001fd7b6500:0x1000," \
  //     "0x0000000277960000:0x1000," \
  //     "0x000000028cfb4d00:0x1000," \
  //     "0x00000002f4ec8600:0x1000," \
  //     "0x0000000318457000:0x1000," \
  //     "0x0000000382c81000:0x1000," \
  //     "0x0000000382c82000:0x1000," \
  //     "0x00000003ae819000:0x1000," \
  //     "0x00000003d8129000:0x1000," \
  //     "0x00000003f8d25000:0x1000," \
  //     "0x00000004074c8000:0x1000," \
  //     "0x000000041af0c000:0x1000," \
  //     "0x000000043c354000:0x1000," \
  //     "0x000000050673c000:0x1000," \
  //     "0x000000051b076000:0x1000," \
  //     "0x000000051c2e2000:0x1000," \
  //     "0x00000005b895c000:0x1000," \
  //     "0x000000060e29b000:0x1000," \
  //     "0x00000006b1e47000:0x1000," \
  //     "0x00000006c20ad000:0x1000," \
  //     "0x00000006f1a64700:0x1000," \
  //     "0x0000000703074000:0x1000," \
  //     "0x000000076890f000:0x1000," \
  //     "0x00000007d57ba600:0x1000," \
  //     "0x00000007fbcae000:0x1000," \
  //     "0x0000000869955000:0x1000," \
  //     "0x0000000898878000:0x1000," \
  //     "0x000000089fa8a000:0x1000," \
  //     "0x00000008fc03c000:0x1000," \
  //     "0x0000000a2ab8a000:0x1000," \
  //     "0x0000000a3cdb5000:0x1000," \
  //     "0x0000000ac2a5a700:0x1000," \
  //     "0x0000000ac7b03f00:0x1000," \
  //     "0x0000000cf073a000:0x1000," \
  //     "0x0000000e50a3f000:0x1000," \
  //     "0x0000000effe87000:0x1000," \
  //     "0x0000000f16567400:0x1000," \
  //     "0x0000000f5318f000:0x1000," \
  //     "0x000000100869f000:0x1000," \
  //     "0x00000012a263c000:0x1000," \
  //     "0x0000001468a1e000:0x1000," \
  //     "0x00000014813ba000:0x1000," \
  //     "0x00000015b3666000:0x1000," \
  //     "0x00000016e578c000:0x1000," \
  //     "0x0000001802c8a000:0x1000," \
  //     "0x00000018b621e000:0x1000," \
  //     "0x00000018f96fb000:0x1000," \
  //     "0x000000192c79b000:0x1000," \
  //     "0x0000001cae7b5000:0x1000," \
  //     "0x0000001ce9e93c00:0x1000," \
  //     "0x0000001ec616e000:0x1000," \
  //     "0x00000022923b2000:0x1000," \
  //     "0x00000023fe535700:0x1000," \
  //     "0x00000025da867e00:0x1000," \
  //     "0x000000281ee84000:0x1000," \
  //     "0x00000028a5955000:0x1000," \
  //     "0x0000002d55de4000:0x1000," \
  //     "0x00000031063e4000:0x1000," \
  //     "0x00000031970f9000:0x1000," \
  //     "0x00000031d9975000:0x1000," \
  //     "0x00000034d96bf300:0x1000," \
  //     "0x00000037c42fd000:0x1000," \
  //     "0x00000039270f4000:0x1000," \
  //     "0x00000039f8022f00:0x1000," \
  //     "0x00000039f8023000:0x1000," \
  //     "0x0000003e7b0e9000:0x1000," \
  //     "0x000000437aee2000:0x1000," \
  //     "0x000000473f7fd000:0x1000," \
  //     "0x0000004bbbc98000:0x1000," \
  //     "0x0000004cf6b6b000:0x1000," \
  //     "0x000000506dfbd000:0x1000," \
  //     "0x00000053464db000:0x1000," \
  //     "0x000000534be78000:0x1000," \
  //     "0x00000058b33dd500:0x1000," \
  //     "0x0000005bb5644000:0x1000," \
  //     "0x0000005fb578b000:0x1000," \
  //     "0x0000006f87694000:0x1000," \
  //     "0x00000078c36b7000:0x1000," \
  //     "0x0000007f4eae2000:0x1000," \
  //     "0x0000009899ca3400:0x1000," \
  //     "0x0000009cbe169000:0x1000," \
  //     "0x000000a39b6a3000:0x1000," \
  //     "0x000000b1e378d000:0x1000," \
  //     "0x000000bab9132000:0x1000," \
  //     "0x000000ce8e0c0500:0x1000," \
  //     "0x000000ef8160e000:0x1000," \
  //     "0x000000f8b4323000:0x1000," \
  //     "0x000000fb9f4ec000:0x1000," \
  //     "0x0000010df4564000:0x1000," \
  //     "0x0000013e316afc00:0x1000," \
  //     "0x0000014e74d6c000:0x1000," \
  //     "0x00000174dacc1000:0x1000," \
  //     "0x000001757d8fe000:0x1000," \
  //     "0x000001c6c0983000:0x1000," \
  //     "0x000001d815480000:0x1000," \
  //     "0x000001e1fe63c000:0x1000," \
  //     "0x000001ea2d89b000:0x1000," \
  //     "0x000001f149cf3000:0x1000," \
  //     "0x000001f294755000:0x1000," \
  //     "0x000001f308651000:0x1000," \
  //     "0x00000207ebf34000:0x1000," \
  //     "0x0000022235ca8000:0x1000," \
  //     "0x00000231c73b0000:0x1000," \
  //     "0x00000243ff9b0000:0x1000," \
  //     "0x000002530925f000:0x1000," \
  //     "0x0000025a9d670700:0x1000," \
  //     "0x0000026ae0207000:0x1000," \
  //     "0x0000027803104000:0x1000," \
  //     "0x0000027cb635c000:0x1000," \
  //     "0x00000298b2df3000:0x1000," \
  //     "0x00000315306cd000:0x1000," \
  //     "0x000003198deed000:0x1000," \
  //     "0x0000034a6927b400:0x1000," \
  //     "0x00000363582aa000:0x1000," \
  //     "0x0000037077788100:0x1000," \
  //     "0x000003adb1ae7000:0x1000," \
  //     "0x000003ba08136400:0x1000," \
  //     "0x000003d275d54000:0x1000," \
  //     "0x0000046679920000:0x1000," \
  //     "0x0000047ea94a6000:0x1000," \
  //     "0x0000048a4f096000:0x1000," \
  //     "0x00000490983c1000:0x1000," \
  //     "0x000004b59a043800:0x1000," \
  //     "0x00000513516d6f00:0x1000," \
  //     "0x0000055b17546000:0x1000," \
  //     "0x0000068aae39d000:0x1000," \
  //     "0x000006ef09d64000:0x1000," \
  //     "0x0000073cddc45000:0x1000," \
  //     "0x0000073cddc46000:0x1000," \
  //     "0x00000759070cc000:0x1000," \
  //     "0x0000089767036000:0x1000," \
  //     "0x00000ac2681bd000:0x1000," \
  //     "0x00000bd1895a0000:0x1000," \
  //     "0x00000c14cc316000:0x1000," \
  //     "0x00000c1b22387000:0x1000," \
  //     "0x00000ffb21bca000:0x1000," \
  //     "0x00000ffc58f37000:0x1000," \
  //     "0x00000ffd34ba3000:0x1000," \
  //     "0x00000ffdaf7f5000:0x1000," \
  //     "0x00000ffddb75f000:0x1000," \
  //     "0x0000113c96814000:0x1000," \
  //     "0x0000115ccc928000:0x1000," \
  //     "0x000013a0602af800:0x1000," \
  //     "0x000014d9768f2000:0x1000," \
  //     "0x000015c3d3c3a000:0x1000," \
  //     "0x000015d23b75b000:0x1000," \
  //     "0x0000171620fa9a00:0x1000," \
  //     "0x0000185c9e780000:0x1000," \
  //     "0x00001a8b816a2000:0x1000," \
  //     "0x00001b455878f000:0x1000," \
  //     "0x00001c0bff9f5000:0x1000," \
  //     "0x00001e825d3ed000:0x1000," \
  //     "0x00001ed5587f2000:0x1000," \
  //     "0x00001f3638994000:0x1000," \
  //     "0x00001fb371155000:0x1000," \
  //     "0x0000208cb62fb000:0x1000," \
  //     "0x0000219d0c41f000:0x1000," \
  //     "0x0000219d0c41f600:0x1000," \
  //     "0x000025e3c625e000:0x1000," \
  //     "0x00002aa19ca4bb00:0x1000," \
  //     "0x00002c58f06c1000:0x1000," \
  //     "0x00002c7bac813000:0x1000," \
  //     "0x00002fa5e979c000:0x1000," \
  //     "0x000036b69203d000:0x1000," \
  //     "0x000036bd19e71000:0x1000," \
  //     "0x000038ae78bbf000:0x1000," \
  //     "0x000038f30908d000:0x1000," \
  //     "0x00003bb45bfd0700:0x1000," \
  //     "0x00003e89ee7fa000:0x1000," \
  //     "0x00003ec763881000:0x1000," \
  //     "0x000053663a67a000:0x1000," \
  //     "0x000057d36ef1d000:0x1000," \
  //     "0x00005de1f283d000:0x1000," \
  //     "0x0000643e93d6fb00:0x1000," \
  //     "0x000068a8c2ee5000:0x1000," \
  //     "0x00006a94309c8000:0x1000," \
  //     "0x00006d3cdad2d000:0x1000," \
  //     "0x000074db44a52000:0x1000," \
  //     "0x000077f714cee000:0x1000," \
  //     "0x000097c4895b9000:0x1000," \
  //     "0x0000a04967453000:0x1000," \
  //     "0x0000a5bfb7b28000:0x1000," \
  //     "0x0000a9fc1c762000:0x1000," \
  //     "0x0000b59016bf9000:0x1000," \
  //     "0x0000c617ed552000:0x1000," \
  //     "0x0000cf0e1d02c000:0x1000," \
  //     "0x0000e948b1f04000:0x1000," \
  //     "0x0000f2d93c0a2000:0x1000" \
  //     ;

#ifndef SIM_MAIN
  argv[arg_max++] = "--extlib=../../../spike_dpi/libserialdevice.so";
#else // SIM_MAIN
  argv[arg_max++] = "--extlib=./libserialdevice.so";
#endif // SIM_MAIN
  argv[arg_max++] = "--device=serialdevice,1409286144,uart";   // 1409286144 = 0x5400_0000
  argv[arg_max++] = "--log";
  argv[arg_max++] = "spike.log";
  argv[arg_max++] = "-l";
  argv[arg_max++] = "--log-commits";
  char *dts_file =(char *)malloc(sizeof(char) * 64);
#ifndef SIM_MAIN
  sprintf (dts_file, "../../../dts/%s.dtb", isa_str);
#else // SIM_MAIN
  sprintf (dts_file, "../dts/%s.dtb", isa_str);
#endif // SIM_MAIN
  argv[arg_max++] = "--dtb";
  argv[arg_max++] = dts_file;
#ifndef SIM_MAIN
  argv[arg_max++] = "--kernel=../../../tests/linux/Image";
  argv[arg_max++] = "--initrd=../../../tests/linux/spike_rootfs.cpio";
#else // SIM_MAIN
  argv[arg_max++] = "--kernel=../tests/linux/Image";
  argv[arg_max++] = "--initrd=../tests/linux/spike_rootfs.cpio";
#endif // SIM_MAIN
  argv[arg_max++] = filename;
  argc = arg_max;
  for (int i = argc; i < 20; i++) { argv[i] = NULL; }
  for (int i = 0; i < arg_max; i++) {
    fprintf (stderr, "argv[%d] = %s\n", i, argv[i]);
  }
  bool debug = false;
  bool halted = false;
  bool histogram = false;
  bool log = false;
  bool dump_dts = false;
  bool dtb_enabled = true;
  bool real_time_clint = false;
  size_t nprocs = 1;
  const char* kernel = NULL;
  reg_t kernel_offset, kernel_size;
  size_t initrd_size;
  reg_t initrd_start = 0, initrd_end = 0;
  const char* bootargs = NULL;
  reg_t start_pc = reg_t(-1);
  std::vector<std::pair<reg_t, mem_t*>> mems;
  std::vector<std::pair<reg_t, abstract_device_t*>> plugin_devices;
  std::unique_ptr<icache_sim_t> ic;
  std::unique_ptr<dcache_sim_t> dc;
  std::unique_ptr<cache_sim_t> l2;
  bool log_cache = false;
  bool log_commits = false;
  const char *log_path = nullptr;
  std::function<extension_t*()> extension;
  const char* initrd = NULL;
  const char* isa = DEFAULT_ISA;
  const char* priv = DEFAULT_PRIV;
  const char* varch = DEFAULT_VARCH;
  const char* dtb_file = NULL;
  uint16_t rbb_port = 0;
  bool use_rbb = false;
  unsigned dmi_rti = 0;
  debug_module_config_t dm_config = {
    .progbufsize = 2,
    .max_bus_master_bits = 0,
    .require_authentication = false,
    .abstract_rti = 0,
    .support_hasel = true,
    .support_abstract_csr_access = true,
    .support_haltgroups = true,
    .support_impebreak = true
  };
  std::vector<int> hartids;

  auto const hartids_parser = [&](const char *s) {
    std::string const str(s);
    std::stringstream stream(str);

    int n;
    while (stream >> n)
    {
      hartids.push_back(n);
      if (stream.peek() == ',') stream.ignore();
    }
  };

  auto const device_parser = [&plugin_devices](const char *s) {
    const std::string str(s);
    std::istringstream stream(str);

    // We are parsing a string like name,base,args.

    // Parse the name, which is simply all of the characters leading up to the
    // first comma. The validity of the plugin name will be checked later.
    std::string name;
    std::getline(stream, name, ',');
    if (name.empty()) {
      throw std::runtime_error("Plugin name is empty.");
    }

    // Parse the base address. First, get all of the characters up to the next
    // comma (or up to the end of the string if there is no comma). Then try to
    // parse that string as an integer according to the rules of strtoull. It
    // could be in decimal, hex, or octal. Fail if we were able to parse a
    // number but there were garbage characters after the valid number. We must
    // consume the entire string between the commas.
    std::string base_str;
    std::getline(stream, base_str, ',');
    if (base_str.empty()) {
      throw std::runtime_error("Device base address is empty.");
    }
    char* end;
    reg_t base = static_cast<reg_t>(strtoull(base_str.c_str(), &end, 0));
    if (end != &*base_str.cend()) {
      throw std::runtime_error("Error parsing device base address.");
    }

    // The remainder of the string is the arguments. We could use getline, but
    // that could ignore newline characters in the arguments. That should be
    // rare and discouraged, but handle it here anyway with this weird in_avail
    // technique. The arguments are optional, so if there were no arguments
    // specified we could end up with an empty string here. That's okay.
    auto avail = stream.rdbuf()->in_avail();
    std::string args(avail, '\0');
    stream.readsome(&args[0], avail);
    plugin_devices.emplace_back(base, new mmio_plugin_device_t(name, args));
  };

  option_parser_t parser;

  parser.help(&suggest_help);
  parser.option('h', "help", 0, [&](const char* s){help(0);});
  parser.option('d', 0, 0, [&](const char* s){debug = true;});
  parser.option('g', 0, 0, [&](const char* s){histogram = true;});
  parser.option('l', 0, 0, [&](const char* s){log = true;});
  parser.option('p', 0, 1, [&](const char* s){nprocs = atoul_nonzero_safe(s);});
  parser.option('m', 0, 1, [&](const char* s){mems = make_mems(s);});
  // I wanted to use --halted, but for some reason that doesn't work.
  parser.option('H', 0, 0, [&](const char* s){halted = true;});
  parser.option(0, "rbb-port", 1, [&](const char* s){use_rbb = true; rbb_port = atoul_safe(s);});
  parser.option(0, "pc", 1, [&](const char* s){start_pc = strtoull(s, 0, 0);});
  parser.option(0, "hartids", 1, hartids_parser);
  parser.option(0, "ic", 1, [&](const char* s){ic.reset(new icache_sim_t(s));});
  parser.option(0, "dc", 1, [&](const char* s){dc.reset(new dcache_sim_t(s));});
  parser.option(0, "l2", 1, [&](const char* s){l2.reset(cache_sim_t::construct(s, "L2$"));});
  parser.option(0, "log-cache-miss", 0, [&](const char* s){log_cache = true;});
  parser.option(0, "isa", 1, [&](const char* s){isa = s;});
  parser.option(0, "priv", 1, [&](const char* s){priv = s;});
  parser.option(0, "varch", 1, [&](const char* s){varch = s;});
  parser.option(0, "device", 1, device_parser);
  parser.option(0, "extension", 1, [&](const char* s){extension = find_extension(s);});
  parser.option(0, "dump-dts", 0, [&](const char *s){dump_dts = true;});
  parser.option(0, "disable-dtb", 0, [&](const char *s){dtb_enabled = false;});
  parser.option(0, "dtb", 1, [&](const char *s){dtb_file = s;});
  parser.option(0, "kernel", 1, [&](const char* s){kernel = s;});
  parser.option(0, "initrd", 1, [&](const char* s){initrd = s;});
  parser.option(0, "bootargs", 1, [&](const char* s){bootargs = s;});
  parser.option(0, "real-time-clint", 0, [&](const char *s){real_time_clint = true;});
  parser.option(0, "extlib", 1, [&](const char *s){
    void *lib = dlopen(s, RTLD_NOW | RTLD_GLOBAL);
    if (lib == NULL) {
      fprintf(compare_log_fp, "Unable to load extlib '%s': %s\n", s, dlerror());
      exit(-1);
    }
  });
  parser.option(0, "dm-progsize", 1,
      [&](const char* s){dm_config.progbufsize = atoul_safe(s);});
  parser.option(0, "dm-no-impebreak", 0,
      [&](const char* s){dm_config.support_impebreak = false;});
  parser.option(0, "dm-sba", 1,
      [&](const char* s){dm_config.max_bus_master_bits = atoul_safe(s);});
  parser.option(0, "dm-auth", 0,
      [&](const char* s){dm_config.require_authentication = true;});
  parser.option(0, "dmi-rti", 1,
      [&](const char* s){dmi_rti = atoul_safe(s);});
  parser.option(0, "dm-abstract-rti", 1,
      [&](const char* s){dm_config.abstract_rti = atoul_safe(s);});
  parser.option(0, "dm-no-hasel", 0,
      [&](const char* s){dm_config.support_hasel = false;});
  parser.option(0, "dm-no-abstract-csr", 0,
      [&](const char* s){dm_config.support_abstract_csr_access = false;});
  parser.option(0, "dm-no-halt-groups", 0,
      [&](const char* s){dm_config.support_haltgroups = false;});
  parser.option(0, "log-commits", 0,
                [&](const char* s){log_commits = true;});
  parser.option(0, "log", 1,
                [&](const char* s){log_path = s;});

  auto argv1 = parser.parse(static_cast<const char* const*>(argv));

  // fprintf (stderr, "parse = %s\n", argv1);

  std::vector<std::string> htif_args(argv1, (const char* const*)argv + argc);

  if (mems.empty())
    mems = make_mems("2048");

  if (kernel && check_file_exists(kernel)) {
    kernel_size = get_file_size(kernel);
    if (isa[2] == '6' && isa[3] == '4')
      kernel_offset = 0x200000;
    else
      kernel_offset = 0x400000;
    for (auto& m : mems) {
      if (kernel_size && (kernel_offset + kernel_size) < m.second->size()) {
         read_file_bytes(kernel, 0, m.second, kernel_offset, kernel_size);
         break;
      }
    }
  }

  if (initrd && check_file_exists(initrd)) {
    initrd_size = get_file_size(initrd);
    for (auto& m : mems) {
      if (initrd_size && (initrd_size + 0x1000) < m.second->size()) {
         initrd_end = m.first + m.second->size() - 0x1000;
         initrd_start = initrd_end - initrd_size;
         read_file_bytes(initrd, 0, m.second, initrd_start - m.first, initrd_size);
         break;
      }
    }
  }

  spike_core = new sim_t(isa, priv, varch, nprocs, halted, real_time_clint,
                         initrd_start, initrd_end, bootargs, start_pc, mems, plugin_devices, htif_args,
                         std::move(hartids), dm_config, log_path, dtb_enabled, dtb_file);

  std::unique_ptr<remote_bitbang_t> remote_bitbang((remote_bitbang_t *) NULL);
  std::unique_ptr<jtag_dtm_t> jtag_dtm(
      new jtag_dtm_t(&spike_core->debug_module, dmi_rti));
  if (use_rbb) {
    remote_bitbang.reset(new remote_bitbang_t(rbb_port, &(*jtag_dtm)));
    spike_core->set_remote_bitbang(&(*remote_bitbang));
  }

  if (dump_dts) {
    printf("%s", spike_core->get_dts());
    return;
  }

  if (ic && l2) ic->set_miss_handler(&*l2);
  if (dc && l2) dc->set_miss_handler(&*l2);
  if (ic) ic->set_log(log_cache);
  if (dc) dc->set_log(log_cache);
  for (size_t i = 0; i < nprocs; i++)
  {
    if (ic) spike_core->get_core(i)->get_mmu()->register_memtracer(&*ic);
    if (dc) spike_core->get_core(i)->get_mmu()->register_memtracer(&*dc);
    if (extension) spike_core->get_core(i)->register_extension(extension());
  }

  spike_core->set_debug(debug);
  spike_core->configure_log(log, log_commits);
  spike_core->set_histogram(histogram);

  spike_core->spike_dpi_init();
  spike_core->get_core(0)->reset();
  // spike_core->get_core(0)->get_state()->pc = 0x80000000;
  // spike_core->get_core(0)->step(5);
  spike_core->get_core(0)->set_csr(static_cast<int>(CSR_MCYCLE),   0);
  spike_core->get_core(0)->set_csr(static_cast<int>(CSR_MINSTRET), 0);

  fprintf(compare_log_fp, "spike iss done\n");

  disasm = new disassembler_t (64);

  return;
}


static std::vector<std::pair<reg_t, mem_t*>> make_mems(const char* arg)
{
  // handle legacy mem argument
  char* p;
  auto mb = strtoull(arg, &p, 0);
  if (*p == 0) {
    reg_t size = reg_t(mb) << 20;
    if (size != (size_t)size)
      throw std::runtime_error("Size would overflow size_t");
    return std::vector<std::pair<reg_t, mem_t*>>(1, std::make_pair(reg_t(DRAM_BASE), new mem_t(size)));
  }

  // handle base/size tuples
  std::vector<std::pair<reg_t, mem_t*>> res;
  while (true) {
    auto base = strtoull(arg, &p, 0);
    if (!*p || *p != ':')
      help();
    auto size = strtoull(p + 1, &p, 0);

    // page-align base and size
    auto base0 = base, size0 = size;
    size += base0 % PGSIZE;
    base -= base0 % PGSIZE;
    if (size % PGSIZE != 0)
      size += PGSIZE - size % PGSIZE;

    if (base + size < base)
      help();

    if (size != size0) {
      fprintf(compare_log_fp, "Warning: the memory at  [0x%llX, 0x%llX] has been realigned\n"
                      "to the %ld KiB page size: [0x%llX, 0x%llX]\n",
              base0, base0 + size0 - 1, long(PGSIZE / 1024), base, base + size - 1);
    }

    res.push_back(std::make_pair(reg_t(base), new mem_t(size)));
    if (!*p)
      break;
    if (*p != ',')
      help();
    arg = p + 1;
  }

  merge_overlapping_memory_regions(res);
  return res;
}


static bool sort_mem_region(const std::pair<reg_t, mem_t*> &a,
                            const std::pair<reg_t, mem_t*> &b)
{
  if (a.first == b.first)
    return (a.second->size() < b.second->size());
  else
    return (a.first < b.first);
}


static void merge_overlapping_memory_regions(std::vector<std::pair<reg_t, mem_t*>>& mems)
{
  // check the user specified memory regions and merge the overlapping or
  // eliminate the containing parts
  std::sort(mems.begin(), mems.end(), sort_mem_region);
  reg_t start_page = 0, end_page = 0;
  std::vector<std::pair<reg_t, mem_t*>>::reverse_iterator it = mems.rbegin();
  std::vector<std::pair<reg_t, mem_t*>>::reverse_iterator _it = mems.rbegin();
  for(; it != mems.rend(); ++it) {
    reg_t _start_page = it->first/PGSIZE;
    reg_t _end_page = _start_page + it->second->size()/PGSIZE;
    if (_start_page >= start_page && _end_page <= end_page) {
      // contains
      mems.erase(std::next(it).base());
    }else if ( _start_page < start_page && _end_page > start_page) {
      // overlapping
      _it->first = _start_page;
      if (_end_page > end_page)
        end_page = _end_page;
      mems.erase(std::next(it).base());
    }else {
      _it = it;
      start_page = _start_page;
      end_page = _end_page;
      assert(start_page < end_page);
    }
  }
}


bool inline is_equal_xlen(int64_t val1, int64_t val2, int compare_lsb = 0)
{
  val1 = val1 & ~((1 << compare_lsb) - 1);
  val2 = val2 & ~((1 << compare_lsb) - 1);

  if (g_rv_xlen == 32) {
    return (val1 & 0xffffffffULL) == (val2 & 0xffffffffULL);
  } else if (g_rv_xlen == 64) {
    return val1 == val2;
  } else {
    fprintf(compare_log_fp, "rv_xlen should be 32 or 64\n");
    exit(-1);
  }
}


bool inline is_equal_flen(int64_t val1, int64_t val2)
{
  if (g_rv_flen == 32) {
    return (val1 & 0xffffffffULL) == (val2 & 0xffffffffULL);
  } else if (g_rv_flen == 64) {
    return val1 == val2;
  } else {
    fprintf(compare_log_fp, "rv_flen should be 32 or 64\n");
    exit(-1);
  }
}


bool inline is_equal_vaddr(int64_t val1, int64_t val2)
{
  int vaddr_len;
  if (g_rv_xlen == 32) {
    vaddr_len = 32;  // XLEN = 32
  } else if (g_rv_xlen == 64) {
    vaddr_len = 39;   // XLEN = 64
  } else {
    fprintf(compare_log_fp, "rv_xlen should be 32 or 64\n");
    exit(-1);
  }

  return (val1 & ((1ULL << vaddr_len)-1)) == (val2 & ((1ULL << vaddr_len)-1));
}


int64_t xlen_convert(int64_t val)
{
  int vaddr_len;
  if (g_rv_xlen == 32) {
    vaddr_len = 32;  // XLEN = 32
  } else if (g_rv_xlen == 64) {
    vaddr_len = 39;   // XLEN = 64
  } else {
    fprintf(compare_log_fp, "rv_xlen should be 32 or 64\n");
    exit(-1);
  }

  return val & ((1ULL << vaddr_len)-1);
}


const int fail_max = 1;
int fail_count = 0;

std::map<int, const char *> riscv_excpt_map {
  { 0, "Instruction Access Misaligned"},
  { 1, "Instruction Access Fault"},
  { 2, "Illegal Instruction"},
  { 3, "Breakpoint"},
  { 4, "Load Access Misaligned"},
  { 5, "Load Access Fault"},
  { 6, "Store Access Misaligned"},
  { 7, "Store Access Fault"},
  { 8, "Environment Call from U-mode"},
  { 9, "Environment Call from S-mode"},
  {11,"Environment Call from M-mode"},
  {12, "Instruction Page Fault"},
  {13, "Load Page Fault"},
  {15, "Store Page Fault"},
  {24, "MRET Flush"},
  {25, "SRET Flush"},
  {26, "URET Flush"},
  {27, "CSR Update Flush"},
  {28, "Another Flush"}
};

void step_spike(long long time, long long rtl_pc,
                int rtl_priv, long long rtl_mstatus,
                int rtl_exception, int rtl_exception_cause,
                int rtl_cmt_id, int rtl_grp_id,
                int rtl_insn,
                int rtl_wr_valid, int rtl_wr_type, int rtl_wr_gpr_addr,
                int rtl_wr_gpr_rnid, long long rtl_wr_val)
{
#ifndef SIM_MAIN
  svScope g_scope;
  g_scope = svGetScopeFromName("tb");
  svSetScope(g_scope);
#endif // SIM_MAIN

  processor_t *p = spike_core->get_core(0);

  if (rtl_exception) {
    fprintf(compare_log_fp, "%lld : RTL(%d,%d) Exception Cause = %s(%d) PC=%012llx, Inst=%08x, %s\n",
            time, rtl_cmt_id, rtl_grp_id,
            riscv_excpt_map[rtl_exception_cause], rtl_exception_cause,
            rtl_pc, rtl_insn, disasm->disassemble(rtl_insn).c_str());
  }
  if (rtl_exception & ((rtl_exception_cause == 0 ) ||  // Instruction Access Misaligned
                       (rtl_exception_cause == 1 ) ||  // Instruction Access Fault
                       (rtl_exception_cause == 2 ) ||  // Illegal Instruction
                       (rtl_exception_cause == 4 ) ||  // Load Access Misaligned
                       (rtl_exception_cause == 5 ) ||  // Load Access Fault
                       (rtl_exception_cause == 6 ) ||  // Store Access Misaligned
                       (rtl_exception_cause == 7 ))) { // Store Access Fault
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "%lld : Exception Happened(%d,%d) : Cause = %s(%d)\n", time,
            rtl_cmt_id, rtl_grp_id,
            riscv_excpt_map[rtl_exception_cause],
            rtl_exception_cause),
    fprintf(compare_log_fp, "==========================================\n");
    return;
  }

  if (rtl_exception & ((rtl_exception_cause == 13) ||  // Load Page Fault
                       (rtl_exception_cause == 15) ||  // Store Page Fault
                       (rtl_exception_cause == 12))) {  // Instruction Page Fault
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "%lld : Exception Happened : Cause = %s(%d)\n", time,
            riscv_excpt_map[rtl_exception_cause],
            rtl_exception_cause),
    fprintf(compare_log_fp, "==========================================\n");
    p->step(1);
    return;
  }

  if (rtl_exception & ((rtl_exception_cause == 28))) {  // Another Flush
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "%lld : Exception Happened : Cause = %s(%d)\n", time,
            riscv_excpt_map[rtl_exception_cause],
            rtl_exception_cause),
    fprintf(compare_log_fp, "==========================================\n");
    return;
  }

  if (rtl_exception & ((rtl_exception_cause == 8 ) ||  // ECALL_U
                       (rtl_exception_cause == 9 ) ||  // ECALL_S
                       (rtl_exception_cause == 11))) { // ECALL_M
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "%lld : Exception Happened : Cause = %s(%d)\n", time,
            riscv_excpt_map[rtl_exception_cause],
            rtl_exception_cause),
    fprintf(compare_log_fp, "==========================================\n");
    return;
  }


  p->step(1);

  auto instret  = p->get_state()->minstret;
  static reg_t prev_instret = 1;
  static bool prev_minstret_access = false;
  if (prev_instret == instret && !prev_minstret_access) {
    p->step(1);
  }
  prev_minstret_access = false;
  prev_instret = instret;
  fprintf(compare_log_fp, "%lld : %ld : PC=[%016llx] (%c,%02d,%02d) %08x %s\n", time,
          instret,
          rtl_pc,
          rtl_priv == 0 ? 'U' : rtl_priv == 2 ? 'S' : 'M',
          rtl_cmt_id, rtl_grp_id, rtl_insn, disasm->disassemble(rtl_insn).c_str());
  auto iss_pc   = p->get_state()->prev_pc;
  auto iss_insn = p->get_state()->insn;
  auto iss_priv = p->get_state()->last_inst_priv;
  auto iss_mstatus = p->get_state()->mstatus;
  // fprintf(compare_log_fp, "%lld : ISS PC = %016llx, NormalPC = %016llx INSN = %08x\n",
  //         time,
  //         iss_pc,
  //         p->get_state()->prev_pc,
  //         iss_insn);
  // fprintf(compare_log_fp, "%lld : ISS MSTATUS = %016llx, RTL MSTATUS = %016llx\n", time, iss_mstatus, rtl_mstatus);

  if (iss_insn.bits() == 0x10500073U) { // WFI
    return; // WFI doesn't update PC -> just skip
  }

  for (auto &iss_rd: p->get_state()->log_mem_read) {
    int64_t iss_wr_val = p->get_state()->XPR[rtl_wr_gpr_addr];
    uint64_t iss_lsu_addr = std::get<0>(iss_rd);
    fprintf(compare_log_fp, "MR%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_rd),
            g_rv_xlen / 4, iss_lsu_addr,
            g_rv_xlen / 4, iss_wr_val /* std::get<1>(iss_rd) */);
    if (iss_lsu_addr == 0x200bff8) {
      fprintf(compare_log_fp, "==========================================\n");
      fprintf(compare_log_fp, "RTL MTIME (0x2000_bff8) Backporting to ISS.\n");
      fprintf(compare_log_fp, "ISS MTIME is updated by RTL = %0*llx\n", g_rv_xlen / 4, rtl_wr_val);
      fprintf(compare_log_fp, "==========================================\n");
      p->get_mmu()->store_uint64 (0x200bff8, rtl_wr_val);
      p->get_state()->XPR.write(rtl_wr_gpr_addr, rtl_wr_val);
      return;
    }
  }
  for (auto &iss_wr: p->get_state()->log_mem_write) {
    fprintf(compare_log_fp, "MW%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_wr),
            g_rv_xlen / 4, std::get<0>(iss_wr),
            g_rv_xlen / 4, std::get<1>(iss_wr));
  }

  if (!is_equal_vaddr(iss_pc, rtl_pc)) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "Wrong PC: RTL = %0*lx, ISS = %0*lx\n",
            g_rv_xlen / 4, xlen_convert(rtl_pc), g_rv_xlen / 4, xlen_convert(iss_pc));
    fprintf(compare_log_fp, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(100, time);
    }
    return;
  }
  if (iss_priv != rtl_priv) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "Wrong Priv Mode: RTL = %d, ISS = %d\n",
            rtl_priv, static_cast<uint32_t>(iss_priv));
    fprintf(compare_log_fp, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(100, time);
    }
    // p->step(10);
    // stop_sim(100);
    return;
  }

  // When RTL generate exception, stop to compare mstatus.
  // Because mstatus update timing is too much complex.
  if (!rtl_exception && !is_equal_xlen(iss_mstatus, rtl_mstatus, 13)) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "Wrong MSTATUS: RTL = %0*llx, ISS = %0*lx\n",
            g_rv_xlen / 4, rtl_mstatus,
            g_rv_xlen / 4, iss_mstatus);
    fprintf(compare_log_fp, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(100, time);
    }
    // p->step(10);
    // stop_sim(100);
    return;
  }

  if (static_cast<int>(iss_insn.bits()) != rtl_insn) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "Wrong INSN: RTL = %08x, ISS = %08x\n",
            rtl_insn, static_cast<uint32_t>(iss_insn.bits()));
    fprintf(compare_log_fp, "            RTL = %s\n",
            disasm->disassemble(rtl_insn).c_str());
    fprintf(compare_log_fp, "            ISS = %s\n",
            disasm->disassemble(iss_insn.bits()).c_str());
    fprintf(compare_log_fp, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(100, time);
    }
    // p->step(10);
    // stop_sim(100);
    return;
  }

  if (rtl_wr_valid && (rtl_wr_gpr_addr != 0) && (p->get_state()->log_reg_write.size() == 0)) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "RTL Writes Register but ISS NOT. RTL GPR[%d] = %0*llx\n",
            rtl_wr_gpr_addr,
            g_rv_xlen / 4, rtl_wr_val);
    fprintf(compare_log_fp, "==========================================\n");
    stop_sim(100, time);
  }

  // // Dumping for ISS GPR Register Writes
  // fprintf(compare_log_fp, "INFO %d %d\n", rtl_wr_valid, p->get_state()->log_reg_write.size());
  // for (auto &iss_rd: p->get_state()->log_reg_write) {
  //   int64_t iss_wr_val = p->get_state()->XPR[std::get<0>(iss_rd)];
  //
  //   fprintf(compare_log_fp, "  GPR[%ld]<=%0*lx\n",
  //           std::get<0>(iss_rd) / 16,
  //           g_rv_xlen / 4, iss_wr_val);
  // }

  if (!rtl_wr_valid && p->get_state()->log_reg_write.size() != 0) {
    for (auto &iss_rd: p->get_state()->log_reg_write) {
      // magic number "16" is category of register write
      if (std::get<0>(iss_rd) < 32 * 16) {
        fprintf(compare_log_fp, "==========================================\n");
        fprintf(compare_log_fp, "ISS Writes GPR but RTL NOT");
        int64_t iss_wr_val = p->get_state()->XPR[std::get<0>(iss_rd)];

        fprintf(compare_log_fp, "  GPR[%ld]<=%0*lx\n",
                std::get<0>(iss_rd) / 16,
                g_rv_xlen / 4, iss_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        stop_sim(100, time);
      }
    }
  }

  int iss_wr_type = 0;
  for (auto &iss_rd: p->get_state()->log_reg_write) {
    iss_wr_type = std::get<0>(iss_rd) % 16;
  }

  if (rtl_wr_valid &&
      (iss_wr_type == 0 || iss_wr_type == 1) &&
      (rtl_wr_type == 0 || rtl_wr_type == 1) &&
      iss_wr_type != rtl_wr_type) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "RTL/ISS Write Register Type different.\n");
    fprintf(compare_log_fp, "ISS = %s, RTL = %s\n", iss_wr_type == 0 ? "GPR" :
            iss_wr_type == 1 ? "FPR" : "Others",
            rtl_wr_type == 0 ? "GPR" :
            iss_wr_type == 1 ? "FPR" : "Others");
    fprintf(compare_log_fp, "==========================================\n");
    stop_sim(100, time);
  }
  if (rtl_wr_valid && iss_wr_type == 0) { // GPR write
    int64_t iss_wr_val = p->get_state()->XPR[rtl_wr_gpr_addr];
    if ((((iss_insn.bits() & MASK_CSRRW) == MATCH_CSRRW) ||
         ((iss_insn.bits() & MASK_CSRRS) == MATCH_CSRRS) ||
         ((iss_insn.bits() & MASK_CSRRC) == MATCH_CSRRC) ||
         ((iss_insn.bits() & MASK_CSRRWI) == MATCH_CSRRWI) ||
         ((iss_insn.bits() & MASK_CSRRSI) == MATCH_CSRRSI) ||
         ((iss_insn.bits() & MASK_CSRRCI) == MATCH_CSRRCI))) {
      if (((iss_insn.bits() >> 20) & 0x0fff) == CSR_MCYCLE) {
        p->set_csr(static_cast<int>(CSR_MCYCLE), static_cast<reg_t>(rtl_wr_val));
        p->get_state()->XPR.write(rtl_wr_gpr_addr, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        fprintf(compare_log_fp, "RTL MCYCLE Backporting to ISS.\n");
        fprintf(compare_log_fp, "ISS MCYCLE is updated to RTL = %0*llx\n", g_rv_xlen / 4, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        return;
      } else if (((iss_insn.bits() >> 20) & 0x0fff) == CSR_CYCLE) {
        p->set_csr(static_cast<int>(CSR_CYCLE), static_cast<reg_t>(rtl_wr_val));
        p->get_state()->XPR.write(rtl_wr_gpr_addr, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        fprintf(compare_log_fp, "RTL CYCLE Backporting to ISS.\n");
        fprintf(compare_log_fp, "ISS CYCLE is updated to RTL = %0*llx\n", g_rv_xlen / 4, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        return;
      } else if (((iss_insn.bits() >> 20) & 0x0fff) == CSR_MINSTRET) {
        if (rtl_wr_val != iss_wr_val) {
          p->set_csr(static_cast<int>(CSR_MINSTRET), static_cast<reg_t>(rtl_wr_val));
          p->get_state()->XPR.write(rtl_wr_gpr_addr, rtl_wr_val);

          fprintf(compare_log_fp, "==========================================\n");
          fprintf(compare_log_fp, "WARNING : RTL MINSTRET is different from ISS. Backported\n");
          fprintf(compare_log_fp, "ISS MINSTRET = %0*lx\n", g_rv_xlen / 4, iss_wr_val);
          fprintf(compare_log_fp, "RTL MINSTRET = %0*llx\n", g_rv_xlen / 4, rtl_wr_val);
          fprintf(compare_log_fp, "==========================================\n");

          prev_minstret_access = true;
          return;
        }
      }
    }

    if (!is_equal_xlen(iss_wr_val, rtl_wr_val)) {
      fprintf(compare_log_fp, "==========================================\n");
      fprintf(compare_log_fp, "Wrong GPR[%02d](%d): RTL = %0*llx, ISS = %0*lx\n",
              rtl_wr_gpr_addr, rtl_wr_gpr_rnid,
              g_rv_xlen / 4, rtl_wr_val,
              g_rv_xlen / 4, iss_wr_val);
      fprintf(compare_log_fp, "==========================================\n");
      fail_count ++;
      if (fail_count >= fail_max) {
        // p->step(10);
        stop_sim(100, time);
      }
      // p->step(10);
      // stop_sim(100);
      return;
    } else {
      fprintf(compare_log_fp, "GPR[%02d](%d) <= %0*llx\n", rtl_wr_gpr_addr, rtl_wr_gpr_rnid, g_rv_xlen / 4, rtl_wr_val);
    }
  } else if (rtl_wr_valid && iss_wr_type == 1) { // FPR write
    int64_t iss_wr_val = p->get_state()->FPR[rtl_wr_gpr_addr].v[0];
    if (!is_equal_flen(iss_wr_val, rtl_wr_val)) {
      fprintf(compare_log_fp, "==========================================\n");
      fprintf(compare_log_fp, "Wrong FPR[%02d](%d): RTL = %0*llx, ISS = %0*lx\n",
              rtl_wr_gpr_addr, rtl_wr_gpr_rnid,
              g_rv_flen / 4, rtl_wr_val,
              g_rv_flen / 4, iss_wr_val);
      fprintf(compare_log_fp, "==========================================\n");
      fail_count ++;
      if (fail_count >= fail_max) {
        stop_sim(100, time);
      }
      return;
    } else {
      fprintf(compare_log_fp, "FPR[%02d](%d) <= %0*llx\n", rtl_wr_gpr_addr, rtl_wr_gpr_rnid, g_rv_flen / 4, rtl_wr_val);
    }
  }

}

void record_stq_store(long long rtl_time,
                      long long paddr,
                      int ram_addr,
                      const char* l1d_data,
                      long long be,
                      int size)
{

  fprintf(compare_log_fp, "%lld : L1D Stq Store  : %llx(%05d) : ", rtl_time, paddr, ram_addr);
  for (int i = size-1; i >= 0; i--) {
    if ((be >> i) & 0x01) {
      fprintf(compare_log_fp, "%02x", (uint8_t)(l1d_data[i]));
    } else {
      fprintf(compare_log_fp, "__");
    }
    if (i % 4 == 0 && i != 0) {
      fprintf(compare_log_fp, "_");
    }
  }
  fprintf(compare_log_fp, "\n");

  bool diff_found = false;
  fprintf(compare_log_fp, "%lld : STQ  ISS Check : %llx        : ", rtl_time, paddr);
  try {
    for (int i = size/8-1; i >= 0; i--) {
      uint64_t iss_ld_data;
      spike_core->read_mem(paddr + i * 8, 8, &iss_ld_data);
      fprintf(compare_log_fp, "%08lx_%08lx", iss_ld_data >> 32 & 0xffffffff, iss_ld_data & 0xffffffff);
      for (int b = 0; b < 8; b++) {
        if ((be >> ((i * 8) + b) & 0x01) && (((iss_ld_data >> (b * 8)) & 0xff) != (uint8_t)(l1d_data[i * 8 + b]))) {
          diff_found = true;
        }
      }
      if (i != 0) { fprintf (compare_log_fp, "_"); }
    }
    fprintf(compare_log_fp, "\n");
  } catch (trap_t &t) {
    fprintf (compare_log_fp, "Catch exception at record_l1d_evict : PA = %08llx, %s\n", paddr, t.name());
  }

  if (diff_found) {
    fprintf (compare_log_fp, "Warning: L1D Update Data Compare Error\n");
    // stop_sim (100);
  }

#ifndef SIM_MAIN
  if (tohost_en && (tohost_addr == paddr) && (l1d_data[0] & 0x1 == 1)) {
    stop_sim(l1d_data[0], rtl_time);
  }
#endif // SIM_MAIN
}


void record_l1d_load(long long rtl_time,
                     long long paddr,
                     int ram_addr,
                     const uint8_t* l1d_data,
                     long long l1d_be,
                     int merge_valid,
                     const uint8_t* merged_l1d_data,
                     long long merge_be,
                     int size)
{

  if (size > 64) {
    fprintf (stderr, "Error: this compare system only support up to 512-bit system\n");
    stop_sim(100, rtl_time);
    return;
  }

  fprintf(compare_log_fp, "%lld : L1D Load-In     : %llx(%05d) : ", rtl_time, paddr, ram_addr);
  for (int i = size-1; i >= 0; i--) {
    fprintf(compare_log_fp, "%02x", l1d_data[i]);
    if (i % 4 == 0 && i != 0) {
      fprintf(compare_log_fp, "_");
    }
  }
  fprintf(compare_log_fp, "\n");
  if (merge_valid) {
    fprintf(compare_log_fp, "%lld : L1D Merged      : %llx(%05d) : ", rtl_time, paddr, ram_addr);
    for (int i = size-1; i >= 0; i--) {
      fprintf(compare_log_fp, "%02x", merged_l1d_data[i]);
      if (i % 4 == 0 && i != 0) {
        fprintf(compare_log_fp, "_");
      }
    }
    fprintf(compare_log_fp, "\n");
#ifndef SIM_MAIN
    if (tohost_en && (tohost_addr == paddr) && (merged_l1d_data[0] & 0x1 == 1)) {
      stop_sim(merged_l1d_data[0], rtl_time);
    }
#endif // SIM_MAIN
  }

  bool diff_found = false;
  fprintf(compare_log_fp, "%lld : Load ISS Check  : %llx        : ", rtl_time, paddr);
  try {
    for (int i = size/8-1; i >= 0; i--) {
      uint64_t iss_ld_data;
      spike_core->read_mem(paddr + i * 8, 8, &iss_ld_data);
      fprintf(compare_log_fp, "%08lx_%08lx", iss_ld_data >> 32 & 0xffffffff, iss_ld_data & 0xffffffff);
      long long be = merge_valid ? merge_be : l1d_be;
      for (int b = 0; b < 8; b++) {
        uint8_t rtl_wr_data0 = merge_valid ? merged_l1d_data[i * 8 + b] : l1d_data[i * 8 + b];
        if (((be >> (i * 8 + b)) & 0x01) &&
            (((iss_ld_data >> (b * 8)) & 0xff) != rtl_wr_data0)) {
          diff_found = true;
        }
      }
      if (i != 0) { fprintf (compare_log_fp, "_"); }
    }
    fprintf(compare_log_fp, "\n");
  } catch (trap_t &t) {
    fprintf (compare_log_fp, "Catch exception at record_l1d_evict : PA = %08llx, %s\n", paddr, t.name());
  }

  if (diff_found) {
    fprintf (compare_log_fp, "Warning : L1D Load Data Compare Error\n");
    // stop_sim (100);
  }
}


void record_l1d_evict(long long rtl_time,
                      long long paddr,
                      int ram_addr,
                      const unsigned int* l1d_data,
                      int size)
{

  fprintf(compare_log_fp, "%lld : L1D Evict       : %llx(%05d) : ", rtl_time, paddr, ram_addr);
  for (int i = size/4-1; i >= 0; i--) {
    fprintf(compare_log_fp, "%08x", l1d_data[i]);
    if (i != 0) {
      fprintf(compare_log_fp, "_");
    }
  }
  fprintf(compare_log_fp, "\n");

  bool diff_found = false;
  fprintf(compare_log_fp, "%lld : EVict ISS Check : %llx        : ", rtl_time, paddr);
  try {
    for (int i = size/8-1; i >= 0; i--) {
      uint64_t iss_ld_data;
      spike_core->read_mem(paddr + i * 8, 8, &iss_ld_data);
      fprintf(compare_log_fp, "%08lx_%08lx", iss_ld_data >> 32 & 0xffffffff, iss_ld_data & 0xffffffff);
      if (((iss_ld_data >> 32 & 0xffffffff) != l1d_data[i*2+1]) |
          ((iss_ld_data       & 0xffffffff) != l1d_data[i*2+0])) {
        diff_found = true;
      }
      if (i != 0) {
        fprintf(compare_log_fp, "_");
      }
    }
    fprintf(compare_log_fp, "\n");
  } catch (trap_t &t) {
    fprintf (compare_log_fp, "Catch exception at record_l1d_evict : PA = %08llx, %s\n", paddr, t.name());
  }

  if (diff_found) {
    fprintf (compare_log_fp, "Warning : Eviction Data Compare Error\n");
    // stop_sim (100);
  }
}


void step_spike_wo_cmp(int steps)
{
  processor_t *p = spike_core->get_core(0);

  fprintf(stderr, "step_spike_wo_cmp(%d)\n\n", steps);

  for (int i = 0; i < steps; i++) {
    p->step(1);
    char spike_out_str[256];
    auto instret  = p->get_state()->minstret;
    auto iss_pc   = p->get_state()->prev_pc;
    auto iss_insn = p->get_state()->insn;
    auto iss_priv = p->get_state()->last_inst_priv;
    sprintf (spike_out_str, "Spike Result : %ld : PC=[%016lx] (%c) %08lx %s\n",
             instret,
             iss_pc,
             iss_priv == 0 ? 'U' : iss_priv == 2 ? 'S' : 'M',
             iss_insn, disasm->disassemble(iss_insn).c_str());
    fprintf(compare_log_fp, spike_out_str);
    fprintf(stderr, spike_out_str);
  }
}

void check_mmu_trans (long long time, long long rtl_va,
                      int rtl_len, int rtl_acc_type,
                      long long rtl_pa)
{
  processor_t *p = spike_core->get_core(0);
  spike_core->set_procs_debug(true);
  mmu_t *mmu = p->get_mmu();

  access_type acc_type;
  switch (rtl_acc_type) {
    case 0 : acc_type = LOAD;  break;
    case 1 : acc_type = STORE; break;
    default :
      fprintf (stderr, "rtl_acc_type = %d is not supported\n", rtl_acc_type);
      stop_sim(1, time);
  }

  try {
    reg_t iss_paddr = mmu->translate(rtl_va, rtl_len, static_cast<access_type>(rtl_acc_type), 0);
    if (iss_paddr != rtl_pa) {
      char spike_out_str[256];
      sprintf (spike_out_str, "Error : PA->VA different.\nRTL = %08llx, ISS=%08lx\n",
               rtl_pa, iss_paddr);
      fprintf (compare_log_fp, spike_out_str);
      fprintf (stderr, spike_out_str);
      stop_sim(100, time);
    } else {
      // fprintf (compare_log_fp, "MMU check passed : VA = %08llx, PA = %08llx\n", rtl_va, rtl_pa);
    }
  } catch (trap_t &t) {
    // fprintf (compare_log_fp, "Catch exception at check_mmu_trans : VA = %08llx, PA = %08llx\n", rtl_va, rtl_pa);
  }

  spike_core->set_procs_debug(false);
}


void spike_update_timer (long long value)
{
  processor_t *p = spike_core->get_core(0);
  p->get_mmu()->store_uint64 (0x200bff8, value);
}


#ifdef SIM_MAIN
void stop_sim(int code, long long rtl_time)
{
  fprintf(compare_log_fp, "stop_ism %d\n", code);
}

int main(int argc, char **argv)
{
  compare_log_fp = fopen("spike_dpi_main.log", "w");

  initial_spike (argv[1], 64, 64, 1);
  processor_t *p = spike_core->get_core(0);

  // fprintf(compare_log_fp, "INST     CYCLE    PC\n");

  for (int i = 0; i < 1000000000; i++) {
    p->step(1);
    auto iss_pc = p->get_state()->prev_pc;
    auto instret = p->get_state()->minstret;
    auto cycle = p->get_state()->mcycle;

    // fprintf(compare_log_fp, "%10d %10d %08lx\n", instret, cycle, iss_pc);

    // for (auto &iss_rd: p->get_state()->log_mem_read) {
    //   fprintf(compare_log_fp, "MR%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_rd),
    //           g_rv_xlen / 4, std::get<0>(iss_rd),
    //           g_rv_xlen / 4, std::get<1>(iss_rd));
    // }
    // for (auto &iss_wr: p->get_state()->log_mem_write) {
    //   fprintf(compare_log_fp, "MW%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_wr),
    //           g_rv_xlen / 4, std::get<0>(iss_wr),
    //           g_rv_xlen / 4, std::get<1>(iss_wr));
    // }
  }

  return 0;
}

#endif // SIM_MAIN

#ifndef VERILATOR
void open_log_fp(const char *filename)
{
  fprintf(stderr, "open_log_fp\n");
  if ((compare_log_fp = fopen("compare.log", "w")) == NULL) {
    perror("failed to open log file");
    exit(EXIT_FAILURE);
  }
  initial_spike(filename, 64, 64, 1);

}
#endif // VERILATOR
