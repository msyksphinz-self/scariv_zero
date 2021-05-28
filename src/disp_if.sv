interface disp_if;
  /* verilator lint_off UNOPTFLAT */
  logic [msrh_pkg::CMT_ID_W-1:0]                  cmt_id;
  logic [riscv_pkg::VADDR_W-1:1]                  pc_addr;
  logic [msrh_conf_pkg::DISP_SIZE-1:0]            tlb_except_valid;
  msrh_pkg::except_t                              tlb_except_cause[msrh_conf_pkg::DISP_SIZE] ;
  msrh_pkg::resource_cnt_t                        resource_cnt;
  // Counter for each dispatch Resources
  msrh_pkg::disp_t [msrh_conf_pkg::DISP_SIZE-1:0] inst;
  logic                                           is_br_included; // When Branch Instruction is included
  logic                                           valid;
  logic                                           ready;

`ifdef SIMULATION
  logic [riscv_pkg::VADDR_W-1:0]  pc_addr_debug;
  assign pc_addr_debug = {pc_addr, 1'b0};
`endif // SIMULATION
  modport master(
    output valid,
    output pc_addr,
    output tlb_except_valid,
    output tlb_except_cause,
    output cmt_id,
    output resource_cnt,
    output inst,
    output is_br_included,
    input  ready
  );
  modport slave(
    input  valid,
    input  pc_addr,
    input  tlb_except_valid,
    input  tlb_except_cause,
    input  cmt_id,
    input  resource_cnt,
    input  inst,
    input  is_br_included,
    output ready
  );
  modport watch(
    input  valid,
    input  pc_addr,
    input  tlb_except_valid,
    input  tlb_except_cause,
    input  cmt_id,
    input  resource_cnt,
    input  inst,
    input  is_br_included,
    input  ready
  );

endinterface
