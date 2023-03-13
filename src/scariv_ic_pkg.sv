// ------------------------------------------------------------------------
// NAME : scariv_ic_pkg
// TYPE : Instruction Cache Package
// ------------------------------------------------------------------------
// Instruction Cache Package
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

package scariv_ic_pkg;

typedef logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] ic_block_t;
typedef logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][riscv_pkg::VADDR_W-1:0] ic_block_vaddr_t;

typedef logic [riscv_pkg::VADDR_W-1: 1]  ic_vaddr_h_t;

typedef logic [riscv_pkg::VADDR_W-1:scariv_lsu_pkg::ICACHE_TAG_LOW + $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)] ic_tag_t;

typedef struct packed {
  logic valid;
  scariv_pkg::vaddr_t vaddr;
} ic_req_t;

typedef struct packed {
  logic valid;
  logic [riscv_pkg::VADDR_W-1:1] vaddr;
  scariv_pkg::ic_data_t data;
  scariv_pkg::ic_strb_t be;

  logic miss;

`ifdef SIMULATION
  scariv_pkg::vaddr_t vaddr_dbg;
`endif // SIMULATION
} ic_resp_t;

typedef enum logic [ 1: 0] {
  ICInit,
  ICReq,
  ICInvalidate,
  ICResp
} ic_state_t;


typedef enum logic [0:0] {
  PrefWrInit,
  PrefWrWait
} pref_wr_state_t;

//
// Instruction Buffer Decode Flush
//
typedef struct packed {
  logic             valid;
  scariv_pkg::vaddr_t pred_vaddr;
} decode_flush_t;

endpackage // scariv_ic_pkg
