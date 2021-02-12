#include "memory_block.hpp"
#include "mem_body.hpp"

#include <getopt.h>
#include <iostream>
#include <verilated.h>
#include <verilated_fst_c.h>
#include "Vmrh_tb.h"

extern std::unique_ptr<Memory> g_memory;
// extern int32_t load_binary(char const* path_exec, char const* filename, bool is_load_dump);
extern bool elf_load_finish;

int time_counter = 0;

static void usage(const char * program_name)
{
  printf("Usage: %s [EMULATOR OPTION]... [VERILOG PLUSARG]... [HOST OPTION]... BINARY [TARGET OPTION]...\n",
         program_name);
}


double sc_time_stamp()
{
  return time_counter;
}

int main(int argc, char** argv) {

  Verilated::commandArgs(argc, argv);

  while (1) {
    static struct option long_options[] = {
      {"elf",  no_argument, 0, 'e' },
      {"help", no_argument, 0, 'h' }
    };

    int option_index = 0;
    int c = getopt_long(argc, argv, "-e:h", long_options, &option_index);

    if (c == -1) break;
 retry:
    switch (c) {
      // Process long and short EMULATOR options
      case 'h': usage(argv[0]);             return 1;
      case 'e': {
        g_memory   = std::unique_ptr<Memory> (new Memory ());

        int ret = load_binary("", optarg, true);
        break;
      }
    }
  }

  // Instantiate DUT
  Vmrh_tb *dut = new Vmrh_tb();

  // Trace DUMP ON
  Verilated::traceEverOn(true);
  VerilatedFstC* tfp = new VerilatedFstC;

  dut->trace(tfp, 100);  // Trace 100 levels of hierarchy
  tfp->open("simx.fst");

  // Format
  dut->i_elf_loader_reset_n = 0;
  dut->i_mrh_reset_n = 0;
  dut->i_ram_reset_n = 0;
  dut->i_clk = 0;

  // Format
  dut->i_elf_loader_reset_n = 1;
  dut->i_mrh_reset_n = 1;
  dut->i_ram_reset_n = 1;
  dut->i_clk = 0;
  // Reset Time
  while (time_counter < 10) {
    dut->eval();
    tfp->dump(time_counter);
    time_counter++;
  }

  // Format
  dut->i_elf_loader_reset_n = 0;
  dut->i_mrh_reset_n = 0;
  dut->i_ram_reset_n = 0;
  dut->i_clk = 0;
  while (time_counter < 100) {
    dut->eval();
    tfp->dump(time_counter);
    time_counter++;
  }
  // Release reset
  dut->i_elf_loader_reset_n = 1;
  dut->i_mrh_reset_n = 0;
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
    tfp->dump(time_counter);

    if (elf_load_finish) {
      dut->i_elf_loader_reset_n = 0;
      dut->i_mrh_reset_n = 1;
    }

    time_counter++;
  }

  dut->final();
  tfp->close();
}
