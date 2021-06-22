package msrh_conf_pkg;

  localparam ICACHE_DATA_W = 512;
  localparam DCACHE_DATA_W = 512;
  localparam ICACHE_WORDS = 128;
  localparam DCACHE_WORDS = 128;
  localparam ICACHE_WAYS = 8;
  localparam DCACHE_WAYS = 8;

  localparam DISP_SIZE = 16;

  localparam ALU_INST_NUM = 8;
  localparam LSU_INST_NUM = 4;

  localparam ARITH_DISP_SIZE = 16;
  localparam MEM_DISP_SIZE = 8;
  localparam BRU_DISP_SIZE   = 1;
  localparam CSU_DISP_SIZE   = 1;

  localparam RV_ALU_ENTRY_SIZE = 32;

  localparam LDQ_SIZE = 32;
  localparam STQ_SIZE = 32;

  localparam RV_CSU_ENTRY_SIZE = 8;

  localparam RV_BRU_ENTRY_SIZE = 32;

  localparam CMT_ENTRY_SIZE = 128;

  localparam USING_VM = 1'b1;

endpackage // msrh_conf_pkg
