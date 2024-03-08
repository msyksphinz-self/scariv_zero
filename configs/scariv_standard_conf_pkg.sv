package scariv_conf_pkg;

  localparam ICACHE_DATA_W = 128;
  localparam DCACHE_DATA_W = 512;
  localparam ICACHE_WORDS = 32;
  localparam DCACHE_WORDS = 32;
  localparam ICACHE_WAYS = 4;
  localparam DCACHE_WAYS = 4;
  localparam DCACHE_BANKS = 4;

  localparam INST_BUF_SIZE = 8;

  localparam DISP_SIZE = 4;

  localparam ALU_INST_NUM = 2;
  localparam LSU_INST_NUM = 2;
  localparam FPU_INST_NUM = 2;

  localparam ARITH_DISP_SIZE = 4;
  localparam MULDIV_DISP_SIZE = ARITH_DISP_SIZE / ALU_INST_NUM;
  localparam MEM_DISP_SIZE   = 4;
  localparam BRU_DISP_SIZE   = 2;
  localparam CSU_DISP_SIZE   = 1;
  localparam FPU_DISP_SIZE   = 4;

  localparam RV_ALU_ENTRY_SIZE = 32;

  localparam RV_LSU_ENTRY_SIZE = 32;
  localparam LDQ_SIZE = 24;
  localparam STQ_SIZE = 24;
  localparam STQ_REGRD_PORT_NUM = 2;
  localparam DETAIL_STLD_FWD = 1;

  localparam RV_CSU_ENTRY_SIZE = 8;
  localparam RV_BRU_ENTRY_SIZE = 16;
  localparam RV_FPU_ENTRY_SIZE = 16;

  localparam VEC_ALU_INST_NUM = 1;
  localparam RV_VALU_ENTRY_SIZE = 32;
  localparam RV_VLSU_ENTRY_SIZE = 32;
  localparam VALU_DISP_SIZE = 1;
  localparam VLSU_DISP_SIZE = 1;

  localparam MISSU_ENTRY_SIZE = 8;

  localparam CMT_ENTRY_SIZE = 32;

  localparam USING_VM = 1'b1;
  localparam XPR_PRF_SIZE_PER_GRP = 32;
  localparam FPR_PRF_SIZE_PER_GRP = 16;

  localparam BTB_ENTRY_SIZE = 128;
  localparam RAS_ENTRY_SIZE = 32;
  localparam GSHARE_BHT_W   = 10;

  localparam FPNEW_LATENCY = 4;

  localparam VEC_VSETVL_DISP_SIZE = 1;
  localparam VEC_ARITH_DISP_SIZE  = 2;
  localparam VEC_MEM_DISP_SIZE    = 2;

endpackage // scariv_conf_pkg
