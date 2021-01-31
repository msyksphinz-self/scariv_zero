#include <iostream>
#include <verilated.h>
#include <verilated_fst_c.h>
#include "Vmrh_tb.h"

int time_counter = 0;

double sc_time_stamp()
{
  return time_counter;
}

int main(int argc, char** argv) {

  Verilated::commandArgs(argc, argv);

  // Instantiate DUT
  Vmrh_tb *dut = new Vmrh_tb();

  // Trace DUMP ON
  Verilated::traceEverOn(true);
  VerilatedFstC* tfp = new VerilatedFstC;

  dut->trace(tfp, 100);  // Trace 100 levels of hierarchy
  tfp->open("simx.fst");

  // Format
  dut->i_reset_n = 0;
  dut->i_clk = 0;

  // Format
  dut->i_reset_n = 1;
  dut->i_clk = 0;
  // Reset Time
  while (time_counter < 10) {
    dut->eval();
    tfp->dump(time_counter);
    time_counter++;
  }

  // Format
  dut->i_reset_n = 0;
  dut->i_clk = 0;
  while (time_counter < 100) {
    dut->eval();
    tfp->dump(time_counter);
    time_counter++;
  }
  // Release reset
  dut->i_reset_n = 1;

  int cycle = 0;
  while (time_counter < 500) {
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

    time_counter++;
  }

  dut->final();
  tfp->close();
}
