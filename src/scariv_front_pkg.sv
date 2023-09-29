package scariv_front_pkg;

typedef struct packed {
  /* verilator lint_off UNOPTFLAT */
  scariv_pkg::cmt_id_t           cmt_id;
  logic [riscv_pkg::VADDR_W-1:1] pc_addr;
  scariv_pkg::grp_id_t                                   tlb_except_valid;
  scariv_pkg::except_t [scariv_conf_pkg::DISP_SIZE-1: 0] tlb_except_cause;
  riscv_pkg::xlen_t    [scariv_conf_pkg::DISP_SIZE-1: 0] tlb_except_tval;
  scariv_pkg::resource_cnt_t                             resource_cnt;
  // Counter for each dispatch Resources
  scariv_pkg::disp_t [scariv_conf_pkg::DISP_SIZE-1:0] inst;
  logic                          is_br_included; // When Branch Instruction is included
  logic                          int_inserted;
`ifdef SIMULATION
  scariv_pkg::vaddr_t            pc_addr_debug;
`endif // SIMULATION
} front_t;

endpackage // scariv_front_pkg

interface scariv_front_if;
  logic                     valid;
  logic                     ready;
  scariv_front_pkg::front_t payload;

// `ifdef SIMULATION
//   assign payload.pc_addr_debug = {payload.pc_addr, 1'b0};
// `endif // SIMULATION

  modport master(
    output valid,
    output payload,
    input  ready
  );
  modport slave(
    input  valid,
    input  payload,
    output ready
  );
  modport watch(
    input  valid,
    input  payload,
    input  ready
  );

endinterface // scariv_front_if
