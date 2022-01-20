package riscv_common_pkg;

  // Privilege Mode
  localparam PRIV_U = 2'h0;
  localparam PRIV_S = 2'h1;
  localparam PRIV_H = 2'h2;
  localparam PRIV_M = 2'h3;

localparam SUPER_SOFT_INT       = 'h1;
localparam MACHINE_SOFT_INT     = 'h3;
localparam SUPER_TIMER_INT      = 'h5;
localparam MACHINE_TIMER_INT    = 'h7;
localparam SUPER_EXTERNAL_INT   = 'h9;
localparam MACHINE_EXTERNAL_INT = 'hb;

endpackage
