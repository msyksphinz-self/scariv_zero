package msrh_ic_pkg;

typedef struct packed {
  logic valid;
  msrh_pkg::vaddr_t vaddr;
} ic_req_t;

typedef struct packed {
  logic valid;
  logic [riscv_pkg::VADDR_W-1:1] vaddr;
  msrh_pkg::ic_data_t data;
  msrh_pkg::ic_strb_t be;

  logic miss;

`ifdef SIMULATION
  msrh_pkg::vaddr_t vaddr_dbg;
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

endpackage // msrh_ic_pkg
