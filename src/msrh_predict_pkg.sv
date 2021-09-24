// ------------------------------------------------------------------------
// NAME : Packages for Branch Prediction
// TYPE : package
// ------------------------------------------------------------------------
// Packages used for branch prediction
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package msrh_predict_pkg;

localparam BTB_ENTRY_SIZE = 1024;

typedef struct packed {
  logic          valid;
  logic [riscv_pkg::VADDR_W-1:$clog2(BTB_ENTRY_SIZE)] pc_tag;
  logic [riscv_pkg::VADDR_W-1:0]                      target_addr;
} btb_entry_t;

endpackage // msrh_predict_pkg

interface btb_search_if;

  logic                                                 s0_valid;
  logic [riscv_pkg::VADDR_W-1:0]                        s0_pc_vaddr;
  logic                                                 s1_hit;
  logic [riscv_pkg::VADDR_W-1:0]                        s1_target_addr;

  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input s1_hit,
    input s1_target_addr
  );

  modport slave (
    input s0_valid,
    input s0_pc_vaddr,
    output s1_hit,
    output s1_target_addr
  );

endinterface // btb_search_if


interface btb_update_if;

  logic                                                 valid;
  logic [riscv_pkg::VADDR_W-1:0]                        pc_vaddr;
  logic                                                 target_vaddr;

  modport master (
    output valid,
    output pc_vaddr,
    output target_vaddr
  );

  modport slave (
    input valid,
    input pc_vaddr,
    input target_vaddr
  );

endinterface // btb_search_if


interface bim_search_if;

  logic                                                 s0_valid;
  logic [riscv_pkg::VADDR_W-1:0]                        s0_pc_vaddr;
  logic [ 1: 0]                                         s1_bim_value;

  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input  s1_bim_value
  );

  modport slave (
    input s0_valid,
    input s0_pc_vaddr,
    output s1_bim_value
  );

endinterface // btb_search_if


interface bim_update_if;

  logic                                                 valid;
  logic [riscv_pkg::VADDR_W-1:0]                        pc_vaddr;
  logic                                                 hit;
  logic [ 1: 0]                                         bim_value;

  modport master (
    output valid,
    output pc_vaddr,
    output hit,
    output bim_value
  );

  modport slave (
    input valid,
    input pc_vaddr,
    input hit,
    input bim_value
  );

endinterface // btb_search_if
