#include "spike_dpi.h"
#include "sim.h"
#include "mmu.h"
#include "disasm.h"

#include <fesvr/option_parser.h>
#include "remote_bitbang.h"
#include "cachesim.h"
#include "extension.h"
#include "../VERSION"

sim_t *spike_core;
disassembler_t *disasm;

std::vector<const char *> argv;

static std::vector<std::pair<reg_t, mem_t*>> make_mems(const char* arg);
static void merge_overlapping_memory_regions(std::vector<std::pair<reg_t, mem_t*>>& mems);
// static void help(int exit_code = 1);

static void help(int exit_code = 1)
{
  fprintf(stderr, "Spike RISC-V ISA Simulator " SPIKE_VERSION "\n\n");
  fprintf(stderr, "usage: spike [host options] <target program> [target options]\n");
  fprintf(stderr, "Host Options:\n");
  fprintf(stderr, "  -p<n>                 Simulate <n> processors [default 1]\n");
  fprintf(stderr, "  -m<n>                 Provide <n> MiB of target memory [default 2048]\n");
  fprintf(stderr, "  -m<a:m,b:n,...>       Provide memory regions of size m and n bytes\n");
  fprintf(stderr, "                          at base addresses a and b (with 4 KiB alignment)\n");
  fprintf(stderr, "  -d                    Interactive debug mode\n");
  fprintf(stderr, "  -g                    Track histogram of PCs\n");
  fprintf(stderr, "  -l                    Generate a log of execution\n");
  fprintf(stderr, "  -h, --help            Print this help message\n");
  fprintf(stderr, "  -H                    Start halted, allowing a debugger to connect\n");
  fprintf(stderr, "  --isa=<name>          RISC-V ISA string [default %s]\n", DEFAULT_ISA);
  fprintf(stderr, "  --priv=<m|mu|msu>     RISC-V privilege modes supported [default %s]\n", DEFAULT_PRIV);
  fprintf(stderr, "  --varch=<name>        RISC-V Vector uArch string [default %s]\n", DEFAULT_VARCH);
  fprintf(stderr, "  --pc=<address>        Override ELF entry point\n");
  fprintf(stderr, "  --hartids=<a,b,...>   Explicitly specify hartids, default is 0,1,...\n");
  fprintf(stderr, "  --ic=<S>:<W>:<B>      Instantiate a cache model with S sets,\n");
  fprintf(stderr, "  --dc=<S>:<W>:<B>        W ways, and B-byte blocks (with S and\n");
  fprintf(stderr, "  --l2=<S>:<W>:<B>        B both powers of 2).\n");
  fprintf(stderr, "  --device=<P,B,A>      Attach MMIO plugin device from an --extlib library\n");
  fprintf(stderr, "                          P -- Name of the MMIO plugin\n");
  fprintf(stderr, "                          B -- Base memory address of the device\n");
  fprintf(stderr, "                          A -- String arguments to pass to the plugin\n");
  fprintf(stderr, "                          This flag can be used multiple times.\n");
  fprintf(stderr, "                          The extlib flag for the library must come first.\n");
  fprintf(stderr, "  --log-cache-miss      Generate a log of cache miss\n");
  fprintf(stderr, "  --extension=<name>    Specify RoCC Extension\n");
  fprintf(stderr, "  --extlib=<name>       Shared library to load\n");
  fprintf(stderr, "                        This flag can be used multiple times.\n");
  fprintf(stderr, "  --rbb-port=<port>     Listen on <port> for remote bitbang connection\n");
  fprintf(stderr, "  --dump-dts            Print device tree string and exit\n");
  fprintf(stderr, "  --disable-dtb         Don't write the device tree blob into memory\n");
  fprintf(stderr, "  --kernel=<path>       Load kernel flat image into memory\n");
  fprintf(stderr, "  --initrd=<path>       Load kernel initrd into memory\n");
  fprintf(stderr, "  --bootargs=<args>     Provide custom bootargs for kernel [default: console=hvc0 earlycon=sbi]\n");
  fprintf(stderr, "  --real-time-clint     Increment clint time at real-time rate\n");
  fprintf(stderr, "  --dm-progsize=<words> Progsize for the debug module [default 2]\n");
  fprintf(stderr, "  --dm-sba=<bits>       Debug bus master supports up to "
      "<bits> wide accesses [default 0]\n");
  fprintf(stderr, "  --dm-auth             Debug module requires debugger to authenticate\n");
  fprintf(stderr, "  --dmi-rti=<n>         Number of Run-Test/Idle cycles "
      "required for a DMI access [default 0]\n");
  fprintf(stderr, "  --dm-abstract-rti=<n> Number of Run-Test/Idle cycles "
      "required for an abstract command to execute [default 0]\n");
  fprintf(stderr, "  --dm-no-hasel         Debug module supports hasel\n");
  fprintf(stderr, "  --dm-no-abstract-csr  Debug module won't support abstract to authenticate\n");
  fprintf(stderr, "  --dm-no-halt-groups   Debug module won't support halt groups\n");
  fprintf(stderr, "  --dm-no-impebreak     Debug module won't support implicit ebreak in program buffer\n");

  exit(exit_code);
}

static void suggest_help()
{
  fprintf(stderr, "Try 'spike --help' for more information.\n");
  exit(1);
}


void initial_spike (const char *filename)
{
  argv.push_back("./spike_dpi");
  argv.push_back("--isa=rv64gc");
  argv.push_back("--log spike.log");
  argv.push_back("-l");
  argv.push_back("--log-commits");
  argv.push_back(filename);

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

  option_parser_t parser;

  parser.help(&suggest_help);
  parser.option('h', "help", 0, [&](const char* s){help(0);});
  parser.option('d', 0, 0, [&](const char* s){debug = true;});
  parser.option('g', 0, 0, [&](const char* s){histogram = true;});
  parser.option('l', 0, 0, [&](const char* s){log = true;});
  // parser.option('p', 0, 1, [&](const char* s){nprocs = atoul_nonzero_safe(s);});
  parser.option('m', 0, 1, [&](const char* s){mems = make_mems(s);});
  // I wanted to use --halted, but for some reason that doesn't work.
  parser.option('H', 0, 0, [&](const char* s){halted = true;});
  // parser.option(0, "rbb-port", 1, [&](const char* s){use_rbb = true; rbb_port = atoul_safe(s);});
  parser.option(0, "pc", 1, [&](const char* s){start_pc = strtoull(s, 0, 0);});
  // parser.option(0, "hartids", 1, hartids_parser);
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
  // parser.option(0, "extlib", 1, [&](const char *s){
  //   void *lib = dlopen(s, RTLD_NOW | RTLD_GLOBAL);
  //   if (lib == NULL) {
  //     fprintf(stderr, "Unable to load extlib '%s': %s\n", s, dlerror());
  //     exit(-1);
  //   }
  // });
  // parser.option(0, "dm-progsize", 1,
  //     [&](const char* s){dm_config.progbufsize = atoul_safe(s);});
  parser.option(0, "dm-no-impebreak", 0,
      [&](const char* s){dm_config.support_impebreak = false;});
  // parser.option(0, "dm-sba", 1,
  //     [&](const char* s){dm_config.max_bus_master_bits = atoul_safe(s);});
  parser.option(0, "dm-auth", 0,
      [&](const char* s){dm_config.require_authentication = true;});
  // parser.option(0, "dmi-rti", 1,
  //     [&](const char* s){dmi_rti = atoul_safe(s);});
  // parser.option(0, "dm-abstract-rti", 1,
  //     [&](const char* s){dm_config.abstract_rti = atoul_safe(s);});
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

  auto argv1 = parser.parse(static_cast<const char* const*>(argv.data()));

  std::vector<std::string> htif_args(argv1, (const char* const*)argv.data() + argv.size());

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

  // if (dump_dts) {
  //   printf("%s", spike_core->get_dts());
  //   return 0;
  // }

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

  processor_t *p = spike_core->get_core(0);
  p->step(10);

  fprintf(stderr, "spike iss done\n");

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
      fprintf(stderr, "Warning: the memory at  [0x%llX, 0x%llX] has been realigned\n"
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


void step_spike(long long time, long long rtl_pc,
                int rtl_cmt_id, int rtl_grp_id,
                int rtl_insn,
                int rtl_wr_valid, int rtl_wr_gpr_addr,
                long long rtl_wr_val)
{
  fprintf(stderr, "step_iss called()\n");

  processor_t *p = spike_core->get_core(0);
  p->step(1);

  fprintf(stderr, "%ld : PC=[%016lx] %s\n", time, rtl_pc,
          disasm->disassemble(rtl_insn).c_str());
  if (rtl_wr_valid) {
    int64_t iss_wr_val = p->get_state()->XPR[rtl_wr_gpr_addr];
    if (iss_wr_val != rtl_wr_val) {
      fprintf(stderr, "==========================================\n");
      fprintf(stderr, "Wrong GPR[%02d]: RTL = %016lx, ISS = %016lx\n",
              rtl_wr_gpr_addr, rtl_wr_val, iss_wr_val);
      fprintf(stderr, "==========================================\n");
    } else {
      fprintf(stderr, "GPR[%02d] <= %016lx", rtl_wr_gpr_addr, rtl_wr_val);
    }
  }
  fprintf (stderr, "\n");
}
