package scariv_conf_pkg;

  localparam ICACHE_DATA_W = 128;
  localparam DCACHE_DATA_W = 128;
  localparam ICACHE_WORDS = 32;
  localparam DCACHE_WORDS = 32;
  localparam ICACHE_WAYS = 2;
  localparam DCACHE_WAYS = 2;
  localparam DCACHE_BANKS = 2;

  localparam INST_BUF_SIZE = 4;

  localparam DISP_SIZE = 2;

  localparam ALU_INST_NUM = 1;
  localparam LSU_INST_NUM = 1;
  localparam FPU_INST_NUM = 1;

  localparam ARITH_DISP_SIZE = 1;
  localparam MULDIV_DISP_SIZE = ARITH_DISP_SIZE / ALU_INST_NUM;
  localparam MEM_DISP_SIZE   = 1;
  localparam BRU_DISP_SIZE   = 1;
  localparam CSU_DISP_SIZE   = 1;
  localparam FPU_DISP_SIZE   = 1;

  localparam RV_ALU_ENTRY_SIZE = 4;

  localparam RV_LSU_ENTRY_SIZE = 4;
  localparam LDQ_SIZE = 4;
  localparam STQ_SIZE = 4;

  localparam RV_CSU_ENTRY_SIZE = 4;
  localparam RV_BRU_ENTRY_SIZE = 4;
  localparam RV_FPU_ENTRY_SIZE = 4;

  localparam MISSU_ENTRY_SIZE = 2;

  localparam CMT_ENTRY_SIZE = 8;
  localparam XPR_PRF_SIZE_PER_GRP = 8;
  localparam FPR_PRF_SIZE_PER_GRP = 4;

  localparam USING_VM = 1'b1;

  localparam BTB_ENTRY_SIZE = 32;
  localparam RAS_ENTRY_SIZE = 8;
  localparam GSHARE_BHT_W = 8;

  localparam FPNEW_LATENCY = 1;

endpackage // scariv_conf_pkg
