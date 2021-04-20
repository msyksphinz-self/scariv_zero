#include "memory_block.hpp"
#include "mem_body.hpp"

#include "spike_dpi.h"

#include <getopt.h>
#include <iostream>
#include <verilated.h>
#include <verilated_fst_c.h>
#include "Vmsrh_tb.h"

extern std::unique_ptr<Memory> g_memory;
extern bool elf_load_finish;

// Instantiate DUT
Vmsrh_tb *dut;
// Trace DUMP ON
VerilatedFstC* tfp = NULL;

int time_counter = 0;
bool dump_fst_enable = false;

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

  Verilated::commandArgs(argc, argv);

  while (1) {
    static struct option long_options[] = {
      {"elf",  no_argument, 0, 'e' },
      {"dump", no_argument, 0, 'd' },
      {"help", no_argument, 0, 'h' }
    };

    int option_index = 0;
    int c = getopt_long(argc, argv, "-e:h:d", long_options, &option_index);

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
        load_binary("", optarg, true);

        break;
      }
    }
  }

  // Instantiate DUT
  dut = new Vmsrh_tb();

  if (dump_fst_enable) {
    Verilated::traceEverOn(true);
    tfp = new VerilatedFstC;

    dut->trace(tfp, 100);  // Trace 100 levels of hierarchy
    tfp->open("simx.fst");
  }

  fprintf(stderr, "initial_spike opening %s ...\n", filename);
  initial_spike(filename, RV_XLEN);

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
    if (dump_fst_enable) tfp->dump(time_counter);
    time_counter++;
  }

  // Format
  dut->i_elf_loader_reset_n = 0;
  dut->i_msrh_reset_n = 0;
  dut->i_ram_reset_n = 0;
  dut->i_clk = 0;
  while (time_counter < 100) {
    dut->eval();
    if (dump_fst_enable) tfp->dump(time_counter);
    time_counter++;
  }
  // Release reset
  dut->i_elf_loader_reset_n = 1;
  dut->i_msrh_reset_n = 0;
  dut->i_ram_reset_n = 1;

  int cycle = 0;
  while (time_counter < 50000) {
    if ((time_counter % 5) == 0) {
      dut->i_clk = !dut->i_clk; // Toggle clock
    }
    if ((time_counter % 10) == 0) {
      // Cycle Count
      cycle ++;
    }

    // Evaluate DUT
    dut->eval();
    if (dump_fst_enable) tfp->dump(time_counter);

    if (elf_load_finish) {
      dut->i_elf_loader_reset_n = 0;
      dut->i_msrh_reset_n = 1;
    }

    time_counter++;
  }

  dut->final();
  if (dump_fst_enable) tfp->close();
}


void stop_sim(int code)
{
  fprintf(stdout, "===============================\n");
  fprintf(stdout, "SIMULATION FINISH : ");
  if (code == 0) {
    fprintf(stdout, "PASS\n");
  } else {
    fprintf(stdout, "FAIL (CODE=%d)\n", code);
  }
  fprintf(stdout, "===============================\n");

  dut->final();
  if (dump_fst_enable) tfp->close();

  exit(code);
}
