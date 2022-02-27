package riscv_common_pkg;

typedef enum logic [1:0] {
   PRIV_U = 0,
   PRIV_S = 1,
   PRIV_H = 2,
   PRIV_M = 3
} priv_t;

localparam SUPER_SOFT_INT       = 'h1;
localparam MACHINE_SOFT_INT     = 'h3;
localparam SUPER_TIMER_INT      = 'h5;
localparam MACHINE_TIMER_INT    = 'h7;
localparam SUPER_EXTERNAL_INT   = 'h9;
localparam MACHINE_EXTERNAL_INT = 'hb;

endpackage
