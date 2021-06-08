#include "spike_dpi.h"
#include "sim.h"
#include "mmu.h"
#include "disasm.h"

#include <dlfcn.h>
#include <fesvr/option_parser.h>
#include "remote_bitbang.h"
#include "cachesim.h"
#include "extension.h"
#include "../VERSION"

sim_t *spike_core;
disassembler_t *disasm;

int argc;
const char *argv[20];
int g_rv_xlen = 0;

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


void initial_spike (const char *filename, int rv_xlen)
{
  argv[0] = "spike_dpi";
  if (rv_xlen == 32) {
    argv[1] = "--isa=rv32gc";
  } else if (rv_xlen == 64) {
    argv[1] = "--isa=rv64gc";
  } else {
    fprintf(stderr, "RV_XLEN should be 32 or 64.\n");
    exit(-1);
  }
  g_rv_xlen = rv_xlen;
  argv[2] = "--log";
  argv[3] = "spike.log";
  argv[4] = "-l";
  // argv[5] = "-d";
  argv[5] = "--log-commits";
  argv[6] = filename;
  argc = 7;
  for (int i = argc; i < 20; i++) { argv[i] = NULL; }

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
      fprintf(stderr, "Unable to load extlib '%s': %s\n", s, dlerror());
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

  fprintf(stderr, "argv = %s\n", argv[0]);
  auto argv1 = parser.parse(static_cast<const char* const*>(argv));

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


bool inline is_equal_xlen(int64_t val1, int64_t val2)
{
  if (g_rv_xlen == 32) {
    return (val1 & 0xffffffffULL) == (val2 & 0xffffffffULL);
  } else if (g_rv_xlen == 64) {
    return val1 == val2;
  } else {
    fprintf(stderr, "rv_xlen should be 32 or 64\n");
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
    fprintf(stderr, "rv_xlen should be 32 or 64\n");
    exit(-1);
  }

  return (val1 & ((1ULL << vaddr_len)-1)) == (val2 & ((1ULL << vaddr_len)-1));
}

const int fail_max = 5;
int fail_count = 0;

void step_spike(long long time, long long rtl_pc,
                int rtl_priv, long long rtl_mstatus,
                int rtl_exception, int rtl_exception_cause,
                int rtl_cmt_id, int rtl_grp_id,
                int rtl_insn,
                int rtl_wr_valid, int rtl_wr_gpr_addr,
                int rtl_wr_gpr_rnid, long long rtl_wr_val)
{
  processor_t *p = spike_core->get_core(0);

  if (rtl_exception) {
    fprintf(stderr, "%lld : RTL(%d,%d) Exception Cause = %d\n",
            time, rtl_cmt_id, rtl_grp_id, rtl_exception_cause);
  }
  if (rtl_exception & ((rtl_exception_cause == 0 ) ||  // Instruction Access Misaligned
                       (rtl_exception_cause == 1 ) ||  // Instruction Access Fault
                       (rtl_exception_cause == 2 ) ||  // Illegal Instruction
                       (rtl_exception_cause == 4 ) ||  // Load Access Misaligned
                       (rtl_exception_cause == 5 ) ||  // Load Access Fault
                       (rtl_exception_cause == 6 ) ||  // Store Access Misaligned
                       (rtl_exception_cause == 7 ))) { // Store Access Fault
    fprintf(stderr, "==========================================\n");
    fprintf(stderr, "%lld : Exception Happened : Cause = %d\n", time, rtl_exception_cause),
    fprintf(stderr, "==========================================\n");
    return;
  }

  if (rtl_exception & ((rtl_exception_cause == 13) ||  // Load Page Fault
                       (rtl_exception_cause == 15) ||  // Store Page Fault
                       (rtl_exception_cause == 12) || // Instruction Page Fault
                       (rtl_exception_cause == 8 ) ||  // ECALL_U
                       (rtl_exception_cause == 9 ) ||  // ECALL_S
                       (rtl_exception_cause == 10))) { // ECALL_M
    fprintf(stderr, "==========================================\n");
    fprintf(stderr, "%lld : Exception Happened : Cause = %d\n", time, rtl_exception_cause),
    fprintf(stderr, "==========================================\n");
    p->step(1);
    return;
  }

  p->step(1);

  auto instret  = p->get_state()->minstret;
  fprintf(stderr, "%lld : %ld : PC=[%016llx] (%02d,%02x) %08x %s\n", time,
          instret,
          rtl_pc,
          rtl_cmt_id, rtl_grp_id, rtl_insn, disasm->disassemble(rtl_insn).c_str());
  auto iss_pc   = p->get_state()->prev_pc;
  auto iss_insn = p->get_state()->insn;
  auto iss_priv = p->get_state()->last_inst_priv;
  auto iss_mstatus = p->get_state()->mstatus;
  // fprintf(stderr, "%lld : ISS PC = %016llx, NormalPC = %016llx INSN = %08x\n",
  //         time,
  //         iss_pc,
  //         p->get_state()->prev_pc,
  //         iss_insn);
  // fprintf(stderr, "%lld : ISS MSTATUS = %016llx, RTL MSTATUS = %016llx\n", time, iss_mstatus, rtl_mstatus);

  if (!is_equal_vaddr(iss_pc, rtl_pc)) {
    fprintf(stderr, "==========================================\n");
    fprintf(stderr, "Wrong PC: RTL = %0*llx, ISS = %0*lx\n",
            g_rv_xlen / 4, rtl_pc, g_rv_xlen / 4, iss_pc);
    fprintf(stderr, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(1);
    }
    return;
  }
  if (iss_priv != rtl_priv) {
    fprintf(stderr, "==========================================\n");
    fprintf(stderr, "Wrong Priv Mode: RTL = %d, ISS = %d\n",
            rtl_priv, static_cast<uint32_t>(iss_priv));
    fprintf(stderr, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(1);
    }
    // p->step(10);
    // stop_sim(1);
    return;
  }

  // When RTL generate exception, stop to compare mstatus.
  // Because mstatus update timing is too much complex.
  if (!rtl_exception && !is_equal_xlen(iss_mstatus, rtl_mstatus)) {
    fprintf(stderr, "==========================================\n");
    fprintf(stderr, "Wrong MSTATUS: RTL = %0*llx, ISS = %0*lx\n",
            g_rv_xlen / 4, rtl_mstatus,
            g_rv_xlen / 4, iss_mstatus);
    fprintf(stderr, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(1);
    }
    // p->step(10);
    // stop_sim(1);
    return;
  }

  if (static_cast<int>(iss_insn.bits()) != rtl_insn) {
    fprintf(stderr, "==========================================\n");
    fprintf(stderr, "Wrong INSN: RTL = %08x, ISS = %08x\n",
            rtl_insn, static_cast<uint32_t>(iss_insn.bits()));
    fprintf(stderr, "            RTL = %s\n",
            disasm->disassemble(rtl_insn).c_str());
    fprintf(stderr, "            ISS = %s\n",
            disasm->disassemble(iss_insn.bits()).c_str());
    fprintf(stderr, "==========================================\n");
    fail_count ++;
    if (fail_count >= fail_max) {
      // p->step(10);
      stop_sim(1);
    }
    // p->step(10);
    // stop_sim(1);
    return;
  }

  if (rtl_wr_valid) {
    int64_t iss_wr_val = p->get_state()->XPR[rtl_wr_gpr_addr];
    if (!is_equal_xlen(iss_wr_val, rtl_wr_val)) {
      fprintf(stderr, "==========================================\n");
      fprintf(stderr, "Wrong GPR[%02d](%d): RTL = %0*llx, ISS = %0*lx\n",
              rtl_wr_gpr_addr, rtl_wr_gpr_rnid,
              g_rv_xlen / 4, rtl_wr_val,
              g_rv_xlen / 4, iss_wr_val);
      fprintf(stderr, "==========================================\n");
      fail_count ++;
      if (fail_count >= fail_max) {
        // p->step(10);
        stop_sim(1);
      }
      // p->step(10);
      // stop_sim(1);
      return;
    } else {
      fprintf(stderr, "GPR[%02d](%d) <= %0*llx\n", rtl_wr_gpr_addr, rtl_wr_gpr_rnid, g_rv_xlen / 4, rtl_wr_val);
    }
  }
}


#ifdef SIM_MAIN
int main(int argc, char **argv)
{
  initial_spike (argv[1], 64);
  processor_t *p = spike_core->get_core(0);
  for (int i = 0; i < 100; i++) {
    p->step(1);
    auto iss_pc = p->get_state()->prev_pc;
    fprintf(stderr, "iss_pc = %08lx\n", iss_pc);
  }

  return 0;
}

void stop_sim(int code)
{
  fprintf(stderr, "stop_ism %d\n", code);
}
#endif // SIM_MAIN
