#include "spike_dpi.h"
#include "gshare_model.h"
#include "tb_elf_loader.h"
#include <string.h>

#include "config.h"
#include "cfg.h"
#include "sim.h"
#include "mmu.h"
#include "arith.h"
#include "disasm.h"

#include <dlfcn.h>
#include <fesvr/option_parser.h>
#include <stdexcept>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string>
#include <memory>
#include <fstream>
#include <limits>
#include <cinttypes>
#include <sstream>
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

extern long long iss_bhr;   // defined in gshare_model.cpp

static std::vector<std::pair<reg_t, abstract_mem_t*>> make_mems(const std::vector<mem_cfg_t> &layout);
static std::vector<mem_cfg_t> merge_overlapping_memory_regions(std::vector<mem_cfg_t> mems);
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
  fprintf(compare_log_fp, "                          This flag can be used multiple rtl_times.\n");
  fprintf(compare_log_fp, "                          The extlib flag for the library must come first.\n");
  fprintf(compare_log_fp, "  --log-cache-miss      Generate a log of cache miss\n");
  fprintf(compare_log_fp, "  --extension=<name>    Specify RoCC Extension\n");
  fprintf(compare_log_fp, "  --extlib=<name>       Shared library to load\n");
  fprintf(compare_log_fp, "                        This flag can be used multiple rtl_times.\n");
  fprintf(compare_log_fp, "  --rbb-port=<port>     Listen on <port> for remote bitbang connection\n");
  fprintf(compare_log_fp, "  --dump-dts            Print device tree string and exit\n");
  fprintf(compare_log_fp, "  --disable-dtb         Don't write the device tree blob into memory\n");
  fprintf(compare_log_fp, "  --kernel=<path>       Load kernel flat image into memory\n");
  fprintf(compare_log_fp, "  --initrd=<path>       Load kernel initrd into memory\n");
  fprintf(compare_log_fp, "  --bootargs=<args>     Provide custom bootargs for kernel [default: console=hvc0 earlycon=sbi]\n");
  fprintf(compare_log_fp, "  --real-rtl_time-clint     Increment clint rtl_time at real-rtl_time rate\n");
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


static std::vector<mem_cfg_t> parse_mem_layout(const char* arg)
{
  std::vector<mem_cfg_t> res;

  // handle legacy mem argument
  char* p;
  auto mb = strtoull(arg, &p, 0);
  if (*p == 0) {
    reg_t size = reg_t(mb) << 20;
    if (size != (size_t)size)
      throw std::runtime_error("Size would overflow size_t");
    res.push_back(mem_cfg_t(reg_t(DRAM_BASE), size));
    return res;
  }

  // handle base/size tuples
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

    if (size != size0) {
      fprintf(stderr, "Warning: the memory at [0x%llX, 0x%llX] has been realigned\n"
                      "to the %ld KiB page size: [0x%llX, 0x%llX]\n",
              base0, base0 + size0 - 1, long(PGSIZE / 1024), base, base + size - 1);
    }

    if (!mem_cfg_t::check_if_supported(base, size)) {
      fprintf(stderr, "Unsupported memory region "
                      "{base = 0x%llX, size = 0x%llX} specified\n",
              base, size);
      exit(EXIT_FAILURE);
    }

    const unsigned long long max_allowed_pa = (1ull << MAX_PADDR_BITS) - 1ull;
    assert(max_allowed_pa <= std::numeric_limits<reg_t>::max());
    mem_cfg_t mem_region(base, size);
    if (mem_region.get_inclusive_end() > max_allowed_pa) {
      int bits_required = 64 - clz(mem_region.get_inclusive_end());
      fprintf(stderr, "Unsupported memory region "
                      "{base = 0x%" PRIX64 ", size = 0x%" PRIX64 "} specified,"
                      " which requires %d bits of physical address\n"
                      "    The largest accessible physical address "
                      "is 0x%llX (defined by MAX_PADDR_BITS constant, which is %d)\n",
              mem_region.get_base(), mem_region.get_size(), bits_required,
              max_allowed_pa, MAX_PADDR_BITS);
      exit(EXIT_FAILURE);
    }

    res.push_back(mem_region);

    if (!*p)
      break;
    if (*p != ',')
      help();
    arg = p + 1;
  }

  auto merged_mem = merge_overlapping_memory_regions(res);

  assert(!merged_mem.empty());
  return merged_mem;
}

static std::vector<std::pair<reg_t, abstract_mem_t*>> make_mems(const std::vector<mem_cfg_t> &layout)
{
  std::vector<std::pair<reg_t, abstract_mem_t*>> mems;
  mems.reserve(layout.size());
  for (const auto &cfg : layout) {
    mems.push_back(std::make_pair(cfg.get_base(), new mem_t(cfg.get_size())));
  }
  return mems;
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

static std::vector<size_t> parse_hartids(const char *s)
{
  std::string const str(s);
  std::stringstream stream(str);
  std::vector<size_t> hartids;

  int n;
  while (stream >> n) {
    if (n < 0) {
      fprintf(stderr, "Negative hart ID %d is unsupported\n", n);
      exit(-1);
    }

    hartids.push_back(n);
    if (stream.peek() == ',') stream.ignore();
  }

  if (hartids.empty()) {
    fprintf(stderr, "No hart IDs specified\n");
    exit(-1);
  }

  std::sort(hartids.begin(), hartids.end());

  const auto dup = std::adjacent_find(hartids.begin(), hartids.end());
  if (dup != hartids.end()) {
    fprintf(stderr, "Duplicate hart ID %zu\n", *dup);
    exit(-1);
  }

  return hartids;
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
                            abstract_mem_t* mem, size_t memoff, size_t read_sz)
{
  std::ifstream in(filename, std::ios::in | std::ios::binary);
  in.seekg(fileoff, std::ios::beg);

  std::vector<char> read_buf(read_sz, 0);
  in.read(&read_buf[0], read_sz);
  mem->store(memoff, read_sz, (uint8_t*)&read_buf[0]);
}


void initial_spike (const char *filename, int rv_xlen, int rv_flen, const char* ext_isa)
{
  argv[0] = "spike_dpi";
  char *isa_str = (char *)malloc(sizeof(char) * 32);
  sprintf(isa_str, "rv%d%s", rv_xlen, ext_isa);
  // if (rv_amo) {
  //   strcat(isa_str, "a");
  // }
  // if (rv_bitmanip) {
  //   strcat(isa_str, "b");
  // }
  // if (rv_flen >= 32) {
  //   strcat(isa_str, "f");
  // }
  // if (rv_flen >= 64) {
  //   strcat(isa_str, "d");
  // }
  // strcat(isa_str, "c");
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

  // argv[arg_max++] = "--pc=0x0";
  argv[arg_max++] = "--pc=0x80000000";
  argv[arg_max++] = "-m0x0:0x100000,0x10000000:0x100000,0x12000000:0x10000,0x80000000:0x80000000";
#ifndef SIM_MAIN
  // argv[arg_max++] = "--extlib=../../../spike_dpi/libserialdevice.so";
#else // SIM_MAIN
  argv[arg_max++] = "--extlib=./libserialdevice.so";
#endif // SIM_MAIN
  // argv[arg_max++] = "--device=serialdevice,1409286144,uart";   // 1409286144 = 0x5400_0000
  argv[arg_max++] = "--log";
  argv[arg_max++] = "spike.log";
  argv[arg_max++] = "-l";
  argv[arg_max++] = "--log-commits";
  char *dts_file =(char *)malloc(sizeof(char) * 64);
#ifndef SIM_MAIN
  sprintf (dts_file, "--dtb=../../../dts/%s.dtb", isa_str);
#else // SIM_MAIN
  sprintf (dts_file, "--dtb=../dts/%s.dtb", isa_str);
#endif // SIM_MAIN
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
  bool UNUSED socket = false;  // command line option -s
  bool dump_dts = false;
  bool dtb_enabled = true;
  const char* kernel = NULL;
  reg_t kernel_offset, kernel_size;
  std::vector<device_factory_t*> plugin_device_factories;
  std::unique_ptr<icache_sim_t> ic;
  std::unique_ptr<dcache_sim_t> dc;
  std::unique_ptr<cache_sim_t> l2;
  bool log_cache = false;
  bool log_commits = false;
  const char *log_path = nullptr;
  std::vector<std::function<extension_t*()>> extensions;
  const char* initrd = NULL;
  const char* dtb_file = NULL;
  uint16_t rbb_port = 0;
  bool use_rbb = false;
  unsigned dmi_rti = 0;
  reg_t blocksz = 64;
  debug_module_config_t dm_config;
  cfg_arg_t<size_t> nprocs(1);

  cfg_t cfg;

  auto const device_parser = [&plugin_device_factories](const char *s) {
    const std::string device_args(s);
    std::vector<std::string> parsed_args;
    std::stringstream sstr(device_args);
    while (sstr.good()) {
      std::string substr;
      getline(sstr, substr, ',');
      parsed_args.push_back(substr);
    }
    if (parsed_args.empty()) throw std::runtime_error("Plugin argument is empty.");

    const std::string name = parsed_args[0];
    if (name.empty()) throw std::runtime_error("Plugin name is empty.");

    auto it = mmio_device_map().find(name);
    if (it == mmio_device_map().end()) throw std::runtime_error("Plugin \"" + name + "\" not found in loaded extlibs.");

    parsed_args.erase(parsed_args.begin());
    it->second->set_sargs(parsed_args);
    plugin_device_factories.push_back(it->second);
  };

  option_parser_t parser;

  parser.help(&suggest_help);
  parser.option('h', "help", 0, [&](const char UNUSED *s){help(0);});
  parser.option('d', 0, 0, [&](const char UNUSED *s){debug = true;});
  parser.option('g', 0, 0, [&](const char UNUSED *s){histogram = true;});
  parser.option('l', 0, 0, [&](const char UNUSED *s){log = true;});
#ifdef HAVE_BOOST_ASIO
  parser.option('s', 0, 0, [&](const char UNUSED *s){socket = true;});
#endif
  parser.option('p', 0, 1, [&](const char* s){nprocs = atoul_nonzero_safe(s);});
  parser.option('m', 0, 1, [&](const char* s){cfg.mem_layout = parse_mem_layout(s);});
  // I wanted to use --halted, but for some reason that doesn't work.
  parser.option('H', 0, 0, [&](const char UNUSED *s){halted = true;});
  parser.option(0, "rbb-port", 1, [&](const char* s){use_rbb = true; rbb_port = atoul_safe(s);});
  parser.option(0, "pc", 1, [&](const char* s){cfg.start_pc = strtoull(s, 0, 0);});
  parser.option(0, "hartids", 1, [&](const char* s){
    cfg.hartids = parse_hartids(s);
    cfg.explicit_hartids = true;
  });
  parser.option(0, "ic", 1, [&](const char* s){ic.reset(new icache_sim_t(s));});
  parser.option(0, "dc", 1, [&](const char* s){dc.reset(new dcache_sim_t(s));});
  parser.option(0, "l2", 1, [&](const char* s){l2.reset(cache_sim_t::construct(s, "L2$"));});
  parser.option(0, "big-endian", 0, [&](const char UNUSED *s){cfg.endianness = endianness_big;});
  parser.option(0, "misaligned", 0, [&](const char UNUSED *s){cfg.misaligned = true;});
  parser.option(0, "log-cache-miss", 0, [&](const char UNUSED *s){log_cache = true;});
  parser.option(0, "isa", 1, [&](const char* s){cfg.isa = s;});
  parser.option(0, "pmpregions", 1, [&](const char* s){cfg.pmpregions = atoul_safe(s);});
  parser.option(0, "pmpgranularity", 1, [&](const char* s){cfg.pmpgranularity = atoul_safe(s);});
  parser.option(0, "priv", 1, [&](const char* s){cfg.priv = s;});
  parser.option(0, "varch", 1, [&](const char* s){cfg.varch = s;});
  parser.option(0, "device", 1, device_parser);
  parser.option(0, "extension", 1, [&](const char* s){extensions.push_back(find_extension(s));});
  parser.option(0, "dump-dts", 0, [&](const char UNUSED *s){dump_dts = true;});
  parser.option(0, "disable-dtb", 0, [&](const char UNUSED *s){dtb_enabled = false;});
  parser.option(0, "dtb", 1, [&](const char *s){dtb_file = s;});
  parser.option(0, "kernel", 1, [&](const char* s){kernel = s;});
  parser.option(0, "initrd", 1, [&](const char* s){initrd = s;});
  parser.option(0, "bootargs", 1, [&](const char* s){cfg.bootargs = s;});
  parser.option(0, "real-time-clint", 0, [&](const char UNUSED *s){cfg.real_time_clint = true;});
  parser.option(0, "triggers", 1, [&](const char *s){cfg.trigger_count = atoul_safe(s);});
  parser.option(0, "extlib", 1, [&](const char *s){
    void *lib = dlopen(s, RTLD_NOW | RTLD_GLOBAL);
    if (lib == NULL) {
      fprintf(stderr, "Unable to load extlib '%s': %s\n", s, dlerror());
      exit(-1);
    }
  });
  parser.option(0, "dm-progsize", 1,
      [&](const char* s){dm_config.progbufsize = atoul_safe(s);});
  parser.option(0, "dm-no-impebreak", 0,
      [&](const char UNUSED *s){dm_config.support_impebreak = false;});
  parser.option(0, "dm-sba", 1,
      [&](const char* s){dm_config.max_sba_data_width = atoul_safe(s);});
  parser.option(0, "dm-auth", 0,
      [&](const char UNUSED *s){dm_config.require_authentication = true;});
  parser.option(0, "dmi-rti", 1,
      [&](const char* s){dmi_rti = atoul_safe(s);});
  parser.option(0, "dm-abstract-rti", 1,
      [&](const char* s){dm_config.abstract_rti = atoul_safe(s);});
  parser.option(0, "dm-no-hasel", 0,
      [&](const char UNUSED *s){dm_config.support_hasel = false;});
  parser.option(0, "dm-no-abstract-csr", 0,
      [&](const char UNUSED *s){dm_config.support_abstract_csr_access = false;});
  parser.option(0, "dm-no-abstract-fpr", 0,
      [&](const char UNUSED *s){dm_config.support_abstract_fpr_access = false;});
  parser.option(0, "dm-no-halt-groups", 0,
      [&](const char UNUSED *s){dm_config.support_haltgroups = false;});
  parser.option(0, "log-commits", 0,
                [&](const char* s){log_commits = true;});
  parser.option(0, "log", 1,
                [&](const char* s){log_path = s;});

  auto argv1 = parser.parse(argv);

  // fprintf (stderr, "parse = %s\n", argv1);

  std::vector<std::string> htif_args(argv1, (const char* const*)argv + argc);

  std::vector<std::pair<reg_t, abstract_mem_t*>> mems =
      make_mems(cfg.mem_layout);

  if (kernel && check_file_exists(kernel)) {
    const char *isa = cfg.isa;
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
    size_t initrd_size = get_file_size(initrd);
    for (auto& m : mems) {
      if (initrd_size && (initrd_size + 0x1000) < m.second->size()) {
         reg_t initrd_end = m.first + m.second->size() - 0x1000;
         reg_t initrd_start = initrd_end - initrd_size;
         cfg.initrd_bounds = std::make_pair(initrd_start, initrd_end);
         read_file_bytes(initrd, 0, m.second, initrd_start - m.first, initrd_size);
         break;
      }
    }
  }

  if (cfg.explicit_hartids) {
    if (nprocs.overridden() && (nprocs() != cfg.nprocs())) {
      std::cerr << "Number of specified hartids ("
                << cfg.nprocs()
                << ") doesn't match specified number of processors ("
                << nprocs() << ").\n";
      exit(1);
    }
  } else {
    // Set default set of hartids based on nprocs, but don't set the
    // explicit_hartids flag (which means that downstream code can know that
    // we've only set the number of harts, not explicitly chosen their IDs).
    std::vector<size_t> default_hartids;
    default_hartids.reserve(nprocs());
    for (size_t i = 0; i < nprocs(); ++i) {
      default_hartids.push_back(i);
    }
    cfg.hartids = default_hartids;
  }

  spike_core = new sim_t(&cfg, halted,
                         mems, plugin_device_factories, htif_args, dm_config, log_path, dtb_enabled, dtb_file,
                         socket,
                         NULL);

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
  for (size_t i = 0; i < cfg.nprocs(); i++)
  {
    if (ic) spike_core->get_core(i)->get_mmu()->register_memtracer(&*ic);
    if (dc) spike_core->get_core(i)->get_mmu()->register_memtracer(&*dc);
    for (auto e : extensions)
      spike_core->get_core(i)->register_extension(e());
  }

  spike_core->set_debug(debug);
  spike_core->configure_log(log, log_commits);
  spike_core->set_histogram(histogram);

  spike_core->spike_dpi_init();
  spike_core->get_core(0)->reset();
  // spike_core->get_core(0)->get_state()->pc = 0x80000000;
  // spike_core->get_core(0)->step(5);
  spike_core->get_core(0)->put_csr(CSR_MCYCLE,   0);
  spike_core->get_core(0)->put_csr(CSR_MINSTRET, 0);

  fprintf(compare_log_fp, "spike iss done\n");

  isa_parser_t isa_parser(cfg.isa, cfg.priv);
  disasm = new disassembler_t (&isa_parser);

  return;
}


bool sort_mem_region(const mem_cfg_t &a, const mem_cfg_t &b)
{
  if (a.get_base() == b.get_base())
    return (a.get_size() < b.get_size());
  else
    return (a.get_base() < b.get_base());
}

static bool check_mem_overlap(const mem_cfg_t& L, const mem_cfg_t& R)
{
  return std::max(L.get_base(), R.get_base()) <= std::min(L.get_inclusive_end(), R.get_inclusive_end());
}

static bool check_if_merge_covers_64bit_space(const mem_cfg_t& L,
                                              const mem_cfg_t& R)
{
  if (!check_mem_overlap(L, R))
    return false;

  auto start = std::min(L.get_base(), R.get_base());
  auto end = std::max(L.get_inclusive_end(), R.get_inclusive_end());

  return (start == 0ull) && (end == std::numeric_limits<uint64_t>::max());
}

// check the user specified memory regions and merge the overlapping or
static mem_cfg_t merge_mem_regions(const mem_cfg_t& L, const mem_cfg_t& R)
{
  // one can merge only intersecting regions
  assert(check_mem_overlap(L, R));

  const auto merged_base = std::min(L.get_base(), R.get_base());
  const auto merged_end_incl = std::max(L.get_inclusive_end(), R.get_inclusive_end());
  const auto merged_size = merged_end_incl - merged_base + 1;

  return mem_cfg_t(merged_base, merged_size);
}

// eliminate the containing parts
static std::vector<mem_cfg_t>
merge_overlapping_memory_regions(std::vector<mem_cfg_t> mems)
{
  if (mems.empty())
    return {};

  std::sort(mems.begin(), mems.end(), sort_mem_region);

  std::vector<mem_cfg_t> merged_mem;
  merged_mem.push_back(mems.front());

  for (auto mem_it = std::next(mems.begin()); mem_it != mems.end(); ++mem_it) {
    const auto& mem_int = *mem_it;
    if (!check_mem_overlap(merged_mem.back(), mem_int)) {
      merged_mem.push_back(mem_int);
      continue;
    }
    // there is a weird corner case preventing two memory regions from being
    // merged: if the resulting size of a region is 2^64 bytes - currently,
    // such regions are not representable by mem_cfg_t class (because the
    // actual size field is effectively a 64 bit value)
    // so we create two smaller memory regions that total for 2^64 bytes as
    // a workaround
    if (check_if_merge_covers_64bit_space(merged_mem.back(), mem_int)) {
      merged_mem.clear();
      merged_mem.push_back(mem_cfg_t(0ull, 0ull - PGSIZE));
      merged_mem.push_back(mem_cfg_t(0ull - PGSIZE, PGSIZE));
      break;
    }
    merged_mem.back() = merge_mem_regions(merged_mem.back(), mem_int);
  }

  return merged_mem;
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

void step_spike(long long rtl_time, long long rtl_pc,
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
            rtl_time, rtl_cmt_id, rtl_grp_id,
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
    fprintf(compare_log_fp, "%lld : Exception Happened(%d,%d) : Cause = %s(%d)\n", rtl_time,
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
    fprintf(compare_log_fp, "%lld : Exception Happened : Cause = %s(%d)\n", rtl_time,
            riscv_excpt_map[rtl_exception_cause],
            rtl_exception_cause),
    fprintf(compare_log_fp, "==========================================\n");
    p->step(1);
    return;
  }

  if (rtl_exception & ((rtl_exception_cause == 28))) {  // Another Flush
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "%lld : Exception Happened : Cause = %s(%d)\n", rtl_time,
            riscv_excpt_map[rtl_exception_cause],
            rtl_exception_cause),
    fprintf(compare_log_fp, "==========================================\n");
    return;
  }

  if (rtl_exception & ((rtl_exception_cause == 8 ) ||  // ECALL_U
                       (rtl_exception_cause == 9 ) ||  // ECALL_S
                       (rtl_exception_cause == 11) ||  // ECALL_M
                       (rtl_exception_cause == 3))) {  // BREAKPOINT
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "%lld : Exception Happened : Cause = %s(%d)\n", rtl_time,
            riscv_excpt_map[rtl_exception_cause],
            rtl_exception_cause),
    fprintf(compare_log_fp, "==========================================\n");
    return;
  }


  p->step(1);

  auto instret  = p->get_state()->minstret->read();
  static reg_t prev_instret = -1;
  static bool prev_minstret_access = false;
  if (prev_instret == instret && !prev_minstret_access) {
    fprintf(compare_log_fp, "instret = %08x, p->step called\n", instret);
    p->step(1);
  }
  prev_minstret_access = false;
  prev_instret = instret;
  fprintf(compare_log_fp, "%lld : %ld : PC=[%016llx] (%c,%02d,%02d) %08x %s\n", rtl_time,
          instret,
          rtl_pc,
          rtl_priv == 0 ? 'U' : rtl_priv == 2 ? 'S' : 'M',
          rtl_cmt_id, rtl_grp_id, rtl_insn, disasm->disassemble(rtl_insn).c_str());
  auto iss_pc   = p->get_state()->prev_pc;
  auto iss_insn = p->get_state()->insn;
  auto iss_priv = p->get_state()->last_inst_priv;
  auto iss_mstatus = p->get_state()->mstatus->read();
  // fprintf(compare_log_fp, "%lld : ISS PC = %016llx, NormalPC = %016llx INSN = %08x\n",
  //         rtl_time,
  //         iss_pc,
  //         p->get_state()->prev_pc,
  //         iss_insn);
  // fprintf(compare_log_fp, "%lld : ISS MSTATUS = %016llx, RTL MSTATUS = %016llx\n", rtl_time, iss_mstatus, rtl_mstatus);

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
      p->get_mmu()->store (0x200bff8, static_cast<uint64_t>(rtl_wr_val));
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
      stop_sim(100, rtl_time);
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
      stop_sim(100, rtl_time);
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
      stop_sim(100, rtl_time);
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
      stop_sim(100, rtl_time);
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
    stop_sim(100, rtl_time);
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
        stop_sim(100, rtl_time);
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
    stop_sim(100, rtl_time);
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
        p->put_csr(CSR_MCYCLE, static_cast<reg_t>(rtl_wr_val));
        p->get_state()->XPR.write(rtl_wr_gpr_addr, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        fprintf(compare_log_fp, "RTL MCYCLE Backporting to ISS.\n");
        fprintf(compare_log_fp, "ISS MCYCLE is updated to RTL = %0*llx\n", g_rv_xlen / 4, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        return;
      } else if (((iss_insn.bits() >> 20) & 0x0fff) == CSR_CYCLE) {
        p->put_csr(CSR_CYCLE, static_cast<reg_t>(rtl_wr_val));
        p->get_state()->XPR.write(rtl_wr_gpr_addr, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        fprintf(compare_log_fp, "RTL CYCLE Backporting to ISS.\n");
        fprintf(compare_log_fp, "ISS CYCLE is updated to RTL = %0*llx\n", g_rv_xlen / 4, rtl_wr_val);
        fprintf(compare_log_fp, "==========================================\n");
        return;
      } else if (((iss_insn.bits() >> 20) & 0x0fff) == CSR_MINSTRET) {
        if (rtl_wr_val != iss_wr_val) {
          p->put_csr(CSR_MINSTRET, static_cast<reg_t>(rtl_wr_val));
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
        stop_sim(100, rtl_time);
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
      if (abs(iss_wr_val - rtl_wr_val) == 1) {
        float128_t f128_rtl_val;
        f128_rtl_val.v[0] = rtl_wr_val;
        f128_rtl_val.v[1] = 0xffffffffffffffff;
        fprintf(compare_log_fp, "Small Approximation error. Backpropagating to ISS\n");
        p->get_state()->FPR.write(rtl_wr_gpr_addr, f128_rtl_val);
        fprintf(compare_log_fp, "==========================================\n");
        return;
      }
      fprintf(compare_log_fp, "==========================================\n");
      fail_count ++;
      if (fail_count >= fail_max) {
        stop_sim(100, rtl_time);
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
      spike_core->read_mem(paddr + i * 8, 8, (uint8_t *)(&iss_ld_data));
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
//   if (merge_valid) {
//     fprintf(compare_log_fp, "%lld : L1D Merged      : %llx(%05d) : ", rtl_time, paddr, ram_addr);
//     for (int i = size-1; i >= 0; i--) {
//       fprintf(compare_log_fp, "%02x", merged_l1d_data[i]);
//       if (i % 4 == 0 && i != 0) {
//         fprintf(compare_log_fp, "_");
//       }
//     }
//     fprintf(compare_log_fp, "\n");
// #ifndef SIM_MAIN
//     if (tohost_en && (tohost_addr == paddr) && (merged_l1d_data[0] & 0x1 == 1)) {
//       stop_sim(merged_l1d_data[0], rtl_time);
//     }
// #endif // SIM_MAIN
//   }

#ifndef SIM_MAIN
    if (tohost_en && (tohost_addr == paddr) && (l1d_data[0] & 0x1 == 1)) {
      stop_sim(l1d_data[0], rtl_time);
    }
#endif // SIM_MAIN


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

// void check_mmu_trans (long long rtl_time, long long rtl_va,
//                       int rtl_len, int rtl_acc_type,
//                       long long rtl_pa)
// {
//   processor_t *p = spike_core->get_core(0);
//   spike_core->set_procs_debug(true);
//   mmu_t *mmu = p->get_mmu();

//   access_type acc_type;
//   switch (rtl_acc_type) {
//     case 0 : acc_type = LOAD;  break;
//     case 1 : acc_type = STORE; break;
//     default :
//       fprintf (stderr, "rtl_acc_type = %d is not supported\n", rtl_acc_type);
//       stop_sim(1, rtl_time);
//   }

//   try {
//     reg_t iss_paddr = mmu->translate(rtl_va, rtl_len, static_cast<access_type>(rtl_acc_type), 0);
//     if (iss_paddr != rtl_pa) {
//       char spike_out_str[256];
//       sprintf (spike_out_str, "Error : PA->VA different.\nRTL = %08llx, ISS=%08lx\n",
//                rtl_pa, iss_paddr);
//       fprintf (compare_log_fp, spike_out_str);
//       fprintf (stderr, spike_out_str);
//       stop_sim(100, rtl_time);
//     } else {
//       // fprintf (compare_log_fp, "MMU check passed : VA = %08llx, PA = %08llx\n", rtl_va, rtl_pa);
//     }
//   } catch (trap_t &t) {
//     // fprintf (compare_log_fp, "Catch exception at check_mmu_trans : VA = %08llx, PA = %08llx\n", rtl_va, rtl_pa);
//   }

//   spike_core->set_procs_debug(false);
// }


void spike_update_timer (long long value)
{
  processor_t *p = spike_core->get_core(0);
  p->get_mmu()->store (0x200bff8, static_cast<uint64_t>(value));
}


#ifdef SIM_MAIN
static void main_suggest_help()
{
  fprintf(stderr, "Try 'spike --help' for more information.\n");
  exit(1);
}

void stop_sim(int code, long long rtl_time)
{
  fprintf(compare_log_fp, "stop_ism %d\n", code);
}

int main(int argc, char **argv)
{
  option_parser_t parser;
  bool log;
  uint64_t sim_cycle;

  parser.help(&main_suggest_help);
  parser.option('l', 0, 0, [&](const char* s){log = true;});
  parser.option('c', 0, 1, [&](const char* s){sim_cycle = strtoull(s, 0, 0);});
  auto argv1 = parser.parse(static_cast<const char* const*>(argv));

  std::vector<std::string> htif_args(argv1, (const char* const*)argv + argc);

  if (log) {
    fprintf(stderr, "Log open\n");
    compare_log_fp = fopen("spike_dpi_main.log", "w");
    fprintf(compare_log_fp, "INST     CYCLE    PC\n");
  }

  initial_spike (htif_args[0].c_str(), 64, 64, "imafdc");
  processor_t *p = spike_core->get_core(0);

  initial_gshare(10, 64);

  fprintf (compare_log_fp, "sim_cycle = %ld\n", sim_cycle);

  for (int i = 0; i < sim_cycle; i++) {
    p->step(1);
    auto iss_pc = p->get_state()->prev_pc;
    auto instret = p->get_state()->minstret;
    auto cycle = p->get_state()->mcycle->read();

    if (log) {
      fprintf(compare_log_fp, "%10ld %10ld %08lx\n", instret, cycle, iss_pc);

      for (auto &iss_rd: p->get_state()->log_mem_read) {
        fprintf(compare_log_fp, "MR%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_rd),
                g_rv_xlen / 4, std::get<0>(iss_rd),
                g_rv_xlen / 4, std::get<1>(iss_rd));
      }
      for (auto &iss_wr: p->get_state()->log_mem_write) {
        fprintf(compare_log_fp, "MW%d(0x%0*lx)<=%0*lx\n", std::get<2>(iss_wr),
                g_rv_xlen / 4, std::get<0>(iss_wr),
                g_rv_xlen / 4, std::get<1>(iss_wr));
      }
    }

    step_gshare (cycle, 0, 0, iss_bhr);
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
  initial_spike(filename, 64, 64, "imafdc");

}
#endif // VERILATOR
