#include "memory_block.hpp"
#include "mem_body.hpp"

#include "spike_dpi.h"
#include "kanata.hpp"

#include <getopt.h>
#include <iostream>
#include <verilated.h>
#include <verilated_fst_c.h>
#include "Vmsrh_tb.h"

extern std::unique_ptr<Memory> g_memory;
extern bool elf_load_finish;
extern "C" {
  FILE *compare_log_fp;
}

extern "C" {
  int load_binary(char const* path_exec,
                  char const* filename,
                  bool is_load_dump);
}

// Instantiate DUT
Vmsrh_tb *dut;
// Trace DUMP ON
VerilatedFstC* tfp = NULL;

int time_counter = 0;
bool dump_fst_enable = false;
bool kanata_enable = false;

static void usage(const char * program_name)
{
  printf("Usage: %s [EMULATOR OPTION]... [VERILOG PLUSARG]... [HOST OPTION]... BINARY [TARGET OPTION]...\n",
         program_name);
}


extern "C" {
  void stop_sim(int code);
}

double sc_time_stamp()
{
  return time_counter;
}

int main(int argc, char** argv) {

  char *filename;

  int cycle = 10000000;

  Verilated::commandArgs(argc, argv);

  bool set_output_file = false;

  while (1) {
    static struct option long_options[] = {
      {"elf"    , required_argument, 0, 'e' },
#ifdef DUMP_FST
      {"dump"   , no_argument,       0, 'd' },
#endif // DUMP_FST
      {"output" , required_argument, 0, 'o' },
      {"cycle"  , required_argument, 0, 'c' },
      {"kanata" , no_argument,       0, 'k' },
      {"help"   , no_argument,       0, 'h' },
      {0        , 0          ,       0, 0   }
    };

    int option_index = 0;
    int c = getopt_long(argc, argv, "e:dho:c:k", long_options, &option_index);

    if (c == -1) break;
 retry:
    switch (c) {
      // Process long and short EMULATOR options
      case 'h': usage(argv[0]);             return 1;
      case 'd':
        dump_fst_enable = true;
        break;
      case 'e': {
        g_memory   = std::unique_ptr<Memory> (new Memory ());

        filename = (char*)malloc(strlen(optarg) + 1);
        strcpy(filename, optarg);

        break;
      }
      case 'o': {
        if ((compare_log_fp = fopen(optarg, "w")) == NULL) {
          fprintf(stderr, "optarg = %s", optarg);
          perror("failed to open log file");
          exit(EXIT_FAILURE);
        }
        set_output_file = true;
        break;
      }
      case 'c': {
        cycle = strtol(optarg, NULL, 10);
        fprintf(stderr, "cycle = %d\n", cycle);
        break;
      }
      case 'k':
        kanata_enable = true;
        break;
    }
  }

  if (set_output_file == false) {
    compare_log_fp = stdout;
  }
  load_binary("", filename, true);

  // Instantiate DUT
  dut = new Vmsrh_tb();

#ifdef DUMP_FST
  if (dump_fst_enable) {
    Verilated::traceEverOn(true);
    tfp = new VerilatedFstC;

    dut->trace(tfp, 100);  // Trace 100 levels of hierarchy
    tfp->open("simx.fst");
  }
#endif // DUMP_FST

  if (konata_enable) {
    fprintf(compare_log_fp, "init kanata ...\n");
    init_kanata();
  }

  fprintf(compare_log_fp, "initial_spike opening %s ...\n", filename);
  initial_spike(filename, RV_XLEN, RV_FLEN);

  // Format
  dut->i_elf_loader_reset_n = 0;
  dut->i_msrh_reset_n = 0;
  dut->i_ram_reset_n = 0;
  dut->i_clk = 0;

  // Format
  dut->i_elf_loader_reset_n = 1;
  dut->i_msrh_reset_n = 1;
  dut->i_ram_reset_n = 1;
  dut->i_clk = 0;
  // Reset Time
  while (time_counter < 10) {
    dut->eval();
#ifdef DUMP_FST
    if (dump_fst_enable) tfp->dump(time_counter);
#endif // DUMP_FST
    time_counter++;
  }

  // Format
  dut->i_elf_loader_reset_n = 0;
  dut->i_msrh_reset_n = 0;
  dut->i_ram_reset_n = 0;
  dut->i_clk = 0;
  while (time_counter < 100) {
    dut->eval();
#ifdef DUMP_FST
    if (dump_fst_enable) tfp->dump(time_counter);
#endif // DUMP_FST
    time_counter++;
  }
  // Release reset
  dut->i_elf_loader_reset_n = 1;
  dut->i_msrh_reset_n = 0;
  dut->i_ram_reset_n = 1;

  if (kanata_enable) {
    start_kanata (time_counter / 4);
  }

  while (time_counter < cycle && !Verilated::gotFinish()) {
    if ((time_counter % 2) == 0) {
      dut->i_clk = !dut->i_clk; // Toggle clock
      if (kanata_enable) {
        proceed_kanata_cycle();
      }
    }

    // Evaluate DUT
    dut->eval();

#ifdef DUMP_FST
    if (dump_fst_enable) tfp->dump(time_counter);
#endif // DUMP_FST

    if (elf_load_finish) {
      dut->i_elf_loader_reset_n = 0;
      dut->i_msrh_reset_n = 1;
    }

    time_counter++;
  }

  if (!Verilated::gotFinish()) {
    fprintf(compare_log_fp, "===============================\n");
    fprintf(compare_log_fp, "SIMULATION TIMEOUT\n");
    fprintf(compare_log_fp, "===============================\n");
  }
  dut->final();
#ifdef DUMP_FST
  if (dump_fst_enable) tfp->close();
#endif // DUMP_FST
}


void stop_sim(int code)
{
  fprintf(compare_log_fp, "===============================\n");
  fprintf(compare_log_fp, "SIMULATION FINISH : ");
  if (code == 1) {
    fprintf(compare_log_fp, "PASS\n");
  } else {
    fprintf(compare_log_fp, "FAIL (CODE=%d)\n", code);
  }
  fprintf(compare_log_fp, "===============================\n");

  // dut->final();
#ifdef DUMP_FST
  if (dump_fst_enable) tfp->close();
#endif // DUMP_FST

  exit(!(code == 1));
}
