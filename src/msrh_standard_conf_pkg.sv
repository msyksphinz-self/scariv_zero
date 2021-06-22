package msrh_conf_pkg;

  localparam ICACHE_DATA_W = 256;
  localparam DCACHE_DATA_W = 256;
  localparam ICACHE_WORDS = 64;
  localparam DCACHE_WORDS = 64;
  localparam ICACHE_WAYS = 4;
  localparam DCACHE_WAYS = 4;

  localparam DISP_SIZE = 5;

  localparam ALU_INST_NUM = 2;
  localparam LSU_INST_NUM = 2;

  localparam ARITH_DISP_SIZE = 4;
  localparam MEM_DISP_SIZE   = 4;
  localparam BRU_DISP_SIZE   = 1;
  localparam CSU_DISP_SIZE   = 1;

  localparam RV_ALU_ENTRY_SIZE = 32;

  localparam LDQ_SIZE = 16;
  localparam STQ_SIZE = 16;

  localparam RV_CSU_ENTRY_SIZE = 8;

  localparam RV_BRU_ENTRY_SIZE = 16;

  localparam CMT_ENTRY_SIZE = 32;

  localparam USING_VM = 1'b1;

endpackage // msrh_conf_pkg
