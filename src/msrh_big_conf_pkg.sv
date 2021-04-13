package msrh_conf_pkg;

  localparam ICACHE_DATA_W = 256;
  localparam DCACHE_DATA_W = 256;

  localparam DISP_SIZE = 8;

  localparam ALU_INST_NUM = 4;
  localparam LSU_INST_NUM = 3;

  localparam ARITH_DISP_SIZE = 8;
  localparam MEM_DISP_SIZE = 6;
  localparam BRU_DISP_SIZE   = 1;
  localparam CSU_DISP_SIZE   = 1;

  localparam RV_ALU_ENTRY_SIZE = 32;

  localparam LDQ_SIZE = 16;
  localparam STQ_SIZE = 16;

  localparam RV_CSU_ENTRY_SIZE = 8;

  localparam RV_BRU_ENTRY_SIZE = 16;


endpackage // msrh_conf_pkg
