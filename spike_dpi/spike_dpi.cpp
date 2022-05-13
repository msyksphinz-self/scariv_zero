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

#ifdef SIM_MAIN
FILE *compare_log_fp;
#else // SIM_MAIN
#ifdef VERILATOR
extern FILE *compare_log_fp;
#else // VERILATOR
FILE     *compare_log_fp;
#endif // VERILATOR
extern uint64_t  tohost_addr; // define in tb_elf_loader.cpp
extern bool    tohost_en;   // define in tb_elf_loader.cpp
#endif // SIM_MAIN

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

// void stop_sim(int code)
// {
//   fprintf(compare_log_fp, "stop_ism %d\n", code);
// }

void initial_spike (const char *filename, int rv_xlen, int rv_flen)
{
  argv[0] = "spike_dpi";
  if (rv_xlen == 32) {
    if (rv_flen == 0) {
      argv[1] = "--isa=rv32imac";
    } else if (rv_flen == 32) {
      argv[1] = "--isa=rv32imafc";
    } else if (rv_flen == 64) {
      argv[1] = "--isa=rv32imafdc";
    } else {
      fprintf(compare_log_fp, "RV_FLEN should be 0, 32 or 64.\n");
      exit(1);
    }
  } else if (rv_xlen == 64) {
    if (rv_flen == 0) {
      argv[1] = "--isa=rv64imac";
    } else if (rv_flen == 32) {
      argv[1] = "--isa=rv64imafc";
    } else if (rv_flen == 64) {
      argv[1] = "--isa=rv64imafdc";
    } else {
      fprintf(compare_log_fp, "RV_FLEN should be 0, 32 or 64.\n");
      exit(1);
    }
  } else {
    fprintf(compare_log_fp, "RV_XLEN should be 32 or 64.\n");
    exit(-1);
  }
  int arg_max = 2;
  g_rv_xlen = rv_xlen;
  g_rv_flen = rv_flen;
  argv[arg_max++] = "--log";
  argv[arg_max++] = "spike.log";
  argv[arg_max++] = "-l";
  argv[arg_max++] = "--log-commits";
  // argv[arg_max++] = "--dtb";
  // argv[arg_max++] = "msrh.dtb";
  argv[arg_max++] = filename;
  argc = arg_max;
  for (int i = argc; i < 20; i++) { argv[i] = NULL; }
  // for (int i = 0; i < 20; i++) {
  //   fprintf (stderr, "argv[%d] = %s\n", i, argv[i]);
  // }
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
  // parser.option(0, "device", 1, device_parser);
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
  spike_core->get_core(0)->step(5);
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


bool inline is_equal_xlen(int64_t val1, int64_t val2)
{
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
  processor_t *p = spike_core->get_core(0);

  if (rtl_exception) {
    fprintf(compare_log_fp, "%lld : RTL(%d,%d) Exception Cause = %s(%d) PC=%012x, Inst=%08x, %s\n",
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
    fprintf(compare_log_fp, "MR%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_rd),
            g_rv_xlen / 4, std::get<0>(iss_rd),
            g_rv_xlen / 4, iss_wr_val /* std::get<1>(iss_rd) */);
  }
  for (auto &iss_wr: p->get_state()->log_mem_write) {
    fprintf(compare_log_fp, "MW%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_wr),
            g_rv_xlen / 4, std::get<0>(iss_wr),
            g_rv_xlen / 4, std::get<1>(iss_wr));
  }

  if (!is_equal_vaddr(iss_pc, rtl_pc)) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "Wrong PC: RTL = %0*llx, ISS = %0*llx\n",
            g_rv_xlen / 4, xlen_convert(rtl_pc), g_rv_xlen / 4, xlen_convert(iss_pc));
    fprintf(compare_log_fp, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(100);
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
      stop_sim(100);
    }
    // p->step(10);
    // stop_sim(100);
    return;
  }

  // When RTL generate exception, stop to compare mstatus.
  // Because mstatus update timing is too much complex.
  if (!rtl_exception && !is_equal_xlen(iss_mstatus, rtl_mstatus)) {
    fprintf(compare_log_fp, "==========================================\n");
    fprintf(compare_log_fp, "Wrong MSTATUS: RTL = %0*llx, ISS = %0*lx\n",
            g_rv_xlen / 4, rtl_mstatus,
            g_rv_xlen / 4, iss_mstatus);
    fprintf(compare_log_fp, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(100);
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
      stop_sim(100);
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
    stop_sim(100);
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
        stop_sim(100);
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
    stop_sim(100);
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
        stop_sim(100);
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
        stop_sim(100);
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

  fprintf(compare_log_fp, "%lld : L1D Stq Store : %llx(%02d) : ", rtl_time, paddr, ram_addr);
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

#ifndef SIM_MAIN
  if (tohost_en && (tohost_addr == paddr) && (l1d_data[0] & 0x1 == 1)) {
    stop_sim(l1d_data[0]);
  }
#endif // SIM_MAIN
}


void record_l1d_load(long long rtl_time,
                     long long paddr,
                     int ram_addr,
                     const unsigned int* l1d_data,
                     int merge_valid,
                     const unsigned int* merged_l1d_data,
                     int size)
{

  fprintf(compare_log_fp, "%lld : L1D Load-In   : %llx(%02d) : ", rtl_time, paddr, ram_addr);
  for (int i = size/4-1; i >= 0; i--) {
    fprintf(compare_log_fp, "%08x", l1d_data[i]);
    if (i != 0) {
      fprintf(compare_log_fp, "_");
    }
  }
  fprintf(compare_log_fp, "\n");
  if (merge_valid) {
    fprintf(compare_log_fp, "%lld : L1D Merged    : %llx(%02d) : ", rtl_time, paddr, ram_addr);
    for (int i = size/4-1; i >= 0; i--) {
      fprintf(compare_log_fp, "%08x", merged_l1d_data[i]);
      if (i != 0) {
        fprintf(compare_log_fp, "_");
      }
    }
    fprintf(compare_log_fp, "\n");
#ifndef SIM_MAIN
    if (tohost_en && (tohost_addr == paddr) && (merged_l1d_data[0] & 0x1 == 1)) {
      stop_sim(merged_l1d_data[0]);
    }
#endif // SIM_MAIN
  }
}


void record_l1d_evict(long long rtl_time,
                      long long paddr,
                      int ram_addr,
                      const unsigned int* l1d_data,
                      int size)
{

  fprintf(compare_log_fp, "%lld : L1D Evict     : %llx(%02d) : ", rtl_time, paddr, ram_addr);
  for (int i = size/4-1; i >= 0; i--) {
    fprintf(compare_log_fp, "%08x", l1d_data[i]);
    if (i != 0) {
      fprintf(compare_log_fp, "_");
    }
  }
  fprintf(compare_log_fp, "\n");
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
    sprintf (spike_out_str, "Spike Result : %ld : PC=[%016llx] (%c) %08x %s\n",
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
      stop_sim(1);
  }

  try {
    reg_t iss_paddr = mmu->translate(rtl_va, rtl_len, static_cast<access_type>(rtl_acc_type), 0);
    if (iss_paddr != rtl_pa) {
      char spike_out_str[256];
      sprintf (spike_out_str, "Error : PA->VA different.\nRTL = %08x, ISS=%08x",
               rtl_pa, iss_paddr);
      fprintf (compare_log_fp, spike_out_str);
      fprintf (stderr, spike_out_str);
      stop_sim(101);
    } else {
      // fprintf (compare_log_fp, "MMU check passed : VA = %08x, PA = %08x\n", rtl_va, rtl_pa);
    }
  } catch (trap_t &t) {
    // fprintf (compare_log_fp, "Catch exception at check_mmu_trans : VA = %08x, PA = %08x\n", rtl_va, rtl_pa);
  }

  spike_core->set_procs_debug(false);
}


#ifdef SIM_MAIN
int main(int argc, char **argv)
{
  compare_log_fp = fopen("spike_dpi_main.log", "w");

  initial_spike (argv[1], 64, 64);
  processor_t *p = spike_core->get_core(0);

  fprintf(compare_log_fp, "INST     CYCLE    PC\n");

  for (int i = 0; i < 100; i++) {
    p->step(1);
    auto iss_pc = p->get_state()->prev_pc;
    auto instret = p->get_state()->minstret;
    auto cycle = p->get_state()->mcycle;

    fprintf(compare_log_fp, "%10d %10d %08lx\n", instret, cycle, iss_pc);

    for (auto &iss_rd: p->get_state()->log_mem_read) {
      fprintf(compare_log_fp, "MR%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_rd),
              g_rv_xlen / 4, std::get<0>(iss_rd),
              g_rv_xlen / 4, std::get<1>(iss_rd));
    }
    for (auto &iss_wr: p->get_state()->log_mem_write) {
      fprintf(compare_log_fp, "MW%d(0x%0*lx)=>%0*lx\n", std::get<2>(iss_wr),
              g_rv_xlen / 4, std::get<0>(iss_wr),
              g_rv_xlen / 4, std::get<1>(iss_wr));
    }
  }

  return 0;
}

#endif // SIM_MAIN

#ifndef VERILATOR
void open_log_fp(const char *filename)
{
  if ((compare_log_fp = fopen("compare.log", "w")) == NULL) {
    perror("failed to open log file");
    exit(EXIT_FAILURE);
  }
  initial_spike(filename, 64, 64);

}
#endif // VERILATOR
