// ------------------------------------------------------------------------
// NAME : CLINT Packages
// TYPE : packages
// ------------------------------------------------------------------------
// CLINT (Core Local Interruptor) Packages
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

interface clint_if;

logic ipi_valid;
logic time_irq_valid;
logic time_irq_clear;

modport master (
  output ipi_valid,
  output time_irq_valid,
  output time_irq_clear
);


modport slave (
  input ipi_valid,
  input time_irq_valid,
  input time_irq_clear
);

endinterface // clint_if
