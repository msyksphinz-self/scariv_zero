`default_nettype none

package mrh_pkg;
  import riscv_pkg::*;

  localparam ICACHE_TAG_HIGH = riscv_pkg::XLEN_W;
  localparam ICACHE_TAG_LOW = 12;
  localparam ICACHE_DATA_W  = 256;
  localparam ICACHE_WAY_W   = 4;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::XLEN_W-1:0] vaddr;
  } ic_req;

  typedef struct packed {
    logic valid;
    logic [mrh_pkg::ICACHE_DATA_W-1:0] data;
  } ic_resp;

endpackage

`default_nettype wire
