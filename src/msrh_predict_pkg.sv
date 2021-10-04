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

localparam BTB_ENTRY_FIELD_MSB = $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W/2);

localparam BTB_ENTRY_BIT_LSB   = BTB_ENTRY_FIELD_MSB + 1;
localparam BTB_ENTRY_BIT_MSB   = $clog2(BTB_ENTRY_SIZE) - 1 + BTB_ENTRY_BIT_LSB;

typedef struct packed {
  logic                                            valid;
  logic [riscv_pkg::VADDR_W-1:BTB_ENTRY_BIT_MSB+1] pc_tag;
  logic [riscv_pkg::VADDR_W-1:0]                   target_vaddr;
} btb_entry_t;

endpackage // msrh_predict_pkg

interface btb_search_if;

  logic                                                 s0_valid;
  logic [riscv_pkg::VADDR_W-1:0]                        s0_pc_vaddr;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s2_hit;
  logic [riscv_pkg::VADDR_W-1:0][msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] s2_target_vaddr;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]                         s2_valid;
  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input s2_hit,
    input s2_target_vaddr,
    input s2_valid
  );

  modport slave (
    input s0_valid,
    input s0_pc_vaddr,
    output s2_hit,
    output s2_target_vaddr,
    output s2_valid
  );

  modport monitor (
    input s2_hit,
    input s2_target_vaddr,
    input s2_valid
  );

endinterface // btb_search_if


interface btb_update_if;

  logic                                                 valid;
  logic [riscv_pkg::VADDR_W-1:0]                        pc_vaddr;
  logic [riscv_pkg::VADDR_W-1:0]                        target_vaddr;

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

endinterface // btb_update_if


interface bim_search_if;

  logic                                                 s0_valid;
  logic [riscv_pkg::VADDR_W-1:0]                        s0_pc_vaddr;
  logic [ 1: 0][msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]   s2_bim_value;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s2_pred_taken;

  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input  s2_bim_value,
    input  s2_pred_taken
  );

  modport slave (
    input s0_valid,
    input s0_pc_vaddr,
    output s2_bim_value,
    output s2_pred_taken
  );

  modport monitor (
    input s2_bim_value
  );

endinterface // bim_search_if


interface bim_update_if;

  logic                                                 valid;
  logic [riscv_pkg::VADDR_W-1:0]                        pc_vaddr;
  logic                                                 hit;
  logic                                                 taken;
  logic [ 1: 0]                                         bim_value;

  modport master (
    output valid,
    output pc_vaddr,
    output hit,
    output taken,
    output bim_value
  );

  modport slave (
    input valid,
    input pc_vaddr,
    input hit,
    input taken,
    input bim_value
  );

endinterface // bim_update_if
