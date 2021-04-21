package msrh_conf_pkg;

  localparam ICACHE_DATA_W = 256;
  localparam DCACHE_DATA_W = 256;

  localparam DISP_SIZE = 3;

  localparam ALU_INST_NUM = 1;
  localparam LSU_INST_NUM = 1;

  localparam ARITH_DISP_SIZE = 2;
  localparam MEM_DISP_SIZE = 2;
  localparam BRU_DISP_SIZE   = 1;
  localparam CSU_DISP_SIZE   = 1;

  localparam RV_ALU_ENTRY_SIZE = 16;

  localparam LDQ_SIZE = 8;
  localparam STQ_SIZE = 8;

  localparam RV_CSU_ENTRY_SIZE = 4;

  localparam RV_BRU_ENTRY_SIZE = 8;

  localparam CMT_ENTRY_SIZE = 32;

endpackage // msrh_conf_pkg
