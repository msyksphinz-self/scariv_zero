// ------------------------------------------------------------------------
// NAME : PLIC Packages
// TYPE : packages
// ------------------------------------------------------------------------
// PLIC (Platform Level Interruptor) Packages
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

interface plic_if;

logic [ 0: 0] int_valid;
logic [ 2: 0] int_id;
logic         int_complete;
logic         ie;
logic         ip;

modport master (
  output ip,
  input  ie,
  output int_valid,
  output int_id,
  input  int_complete
);


modport slave (
  input  ip,
  output ie,
  input  int_valid,
  input  int_id,
  output int_complete
);

endinterface // plic_if
