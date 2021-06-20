package msrh_conf_pkg;

  localparam ICACHE_DATA_W = 128;
  localparam DCACHE_DATA_W = 128;
  localparam ICACHE_WORDS = 32;
  localparam DCACHE_WORDS = 32;
  localparam ICACHE_WAYS = 2;
  localparam DCACHE_WAYS = 2;

  localparam DISP_SIZE = 2;

  localparam ALU_INST_NUM = 1;
  localparam LSU_INST_NUM = 1;

  localparam ARITH_DISP_SIZE = 1;
  localparam MEM_DISP_SIZE   = 1;
  localparam BRU_DISP_SIZE   = 1;
  localparam CSU_DISP_SIZE   = 1;

  localparam RV_ALU_ENTRY_SIZE = 4;

  localparam LDQ_SIZE = 4;
  localparam STQ_SIZE = 4;

  localparam RV_CSU_ENTRY_SIZE = 4;

  localparam RV_BRU_ENTRY_SIZE = 4;

  localparam CMT_ENTRY_SIZE = 8;

  localparam USING_VM = 1'b1;

endpackage // msrh_conf_pkg
