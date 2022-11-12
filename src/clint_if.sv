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

modport master (
  output ipi_valid,
  output time_irq_valid
);


modport slave (
  input ipi_valid,
  input time_irq_valid
);

endinterface // clint_if
