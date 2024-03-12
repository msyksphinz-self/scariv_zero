package scariv_conf_pkg;

  localparam ICACHE_DATA_W = 256;
  localparam DCACHE_DATA_W = 256;
  localparam ICACHE_WORDS = 64;
  localparam DCACHE_WORDS = 64;
  localparam ICACHE_WAYS = 2;
  localparam DCACHE_WAYS = 2;
  localparam DCACHE_BANKS = 2;

  localparam INST_BUF_SIZE = 6;

  localparam DISP_SIZE = 3;

  localparam ALU_INST_NUM = 1;
  localparam LSU_INST_NUM = 1;
  localparam FPU_INST_NUM = 1;

  localparam ARITH_DISP_SIZE = 2;
  localparam MULDIV_DISP_SIZE = ARITH_DISP_SIZE / ALU_INST_NUM;
  localparam MEM_DISP_SIZE = 2;
  localparam BRU_DISP_SIZE   = 1;
  localparam CSU_DISP_SIZE   = 1;
  localparam FPU_DISP_SIZE   = 2;

  localparam RV_ALU_ENTRY_SIZE = 16;

  localparam RV_LSU_ENTRY_SIZE = 16;
  localparam LDQ_SIZE = 8;
  localparam STQ_SIZE = 8;
  localparam STQ_REGRD_PORT_NUM = 1;
  localparam DETAIL_STLD_FWD = 0;

  localparam RV_CSU_ENTRY_SIZE = 4;
  localparam RV_BRU_ENTRY_SIZE = 8;
  localparam RV_FPU_ENTRY_SIZE = 8;

  localparam VEC_ALU_INST_NUM = 0;
  localparam RV_VEC_ALU_ENTRY_SIZE = 0;
  localparam VALU_DISP_SIZE = 1;

  localparam MISSU_ENTRY_SIZE = 4;

  localparam CMT_ENTRY_SIZE = 16;
  localparam XPR_PRF_SIZE_PER_GRP = 16;
  localparam FPR_PRF_SIZE_PER_GRP = 8;

  localparam USING_VM = 1'b1;

  localparam BTB_ENTRY_SIZE = 64;
  localparam RAS_ENTRY_SIZE = 16;
  localparam GSHARE_BHT_W   = 9;

  localparam FPNEW_LATENCY = 2;

endpackage // scariv_conf_pkg
