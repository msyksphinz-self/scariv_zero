// ------------------------------------------------------------------------
// NAME : SCARIV CSR Interface & Package
// TYPE : package
// ------------------------------------------------------------------------
// CSR Intarfec & Package
// ------------------------------------------------------------------------
// CSR Instruction Scheduler
// CSR Pipeline
// ------------------------------------------------------------------------

interface csr_rd_if;

  logic valid;
  logic [11: 0] addr;
  riscv_pkg::xlen_t data;
  logic                          resp_error;

  modport master (
    output valid,
    output addr,
    input  data,
    input  resp_error
  );

  modport slave (
    input  valid,
    input  addr,
    output data,
    output resp_error
  );

endinterface // csr_rd_if


interface csr_wr_if;

  logic                          valid;
  logic [11: 0]                  addr;
  riscv_pkg::xlen_t data;
  logic                          resp_error;

  modport master (
    output valid,
    output addr,
    output data,
    input  resp_error
  );

  modport slave (
    input  valid,
    input  addr,
    input  data,
    output resp_error
  );

endinterface // csr_wr_if


interface csr_info_if;

logic      update;
riscv_common_pkg::priv_t       priv;
riscv_pkg::xlen_t mstatus;
riscv_pkg::xlen_t mepc;
riscv_pkg::xlen_t mtvec;
riscv_pkg::xlen_t stvec;
riscv_pkg::xlen_t utvec;
riscv_pkg::xlen_t sepc;
riscv_pkg::xlen_t uepc;
riscv_pkg::xlen_t satp;
riscv_pkg::xlen_t medeleg;
riscv_pkg::xlen_t sedeleg;
logic [31: 0] fcsr;


modport master (
  output update,
  output priv,
  output mstatus,
  output mepc,
  output mtvec,
  output stvec,
  output utvec,
  output sepc,
  output uepc,
  output satp,
  output medeleg,
  output sedeleg,
  output fcsr
);

modport slave (
  input update,
  input priv,
  input mstatus,
  input mepc,
  input mtvec,
  input stvec,
  input utvec,
  input sepc,
  input uepc,
  input satp,
  input medeleg,
  input sedeleg,
  input fcsr
);

endinterface // csr_info_if

interface interrupt_if;

logic   s_software_int_valid;
logic   s_timer_int_valid;
logic   s_external_int_valid;

logic   m_software_int_valid;
logic   m_timer_int_valid;
logic   m_external_int_valid;

modport master (
   output s_software_int_valid,
   output s_timer_int_valid,
   output s_external_int_valid,
   output m_software_int_valid,
   output m_timer_int_valid,
   output m_external_int_valid
);

modport slave (
   input s_software_int_valid,
   input s_timer_int_valid,
   input s_external_int_valid,
   input m_software_int_valid,
   input m_timer_int_valid,
   input m_external_int_valid
);

endinterface // interrupt_if

package scariv_csu_pkg;

typedef struct packed {
  logic                  valid;
  scariv_pkg::vaddr_t    pc_addr;
  logic [31: 0]          inst;
  scariv_pkg::inst_cat_t cat;
  logic                  is_rvc;
  scariv_pkg::brtag_t    brtag;

  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;

  logic                  oldest_valid;

  scariv_pkg::reg_wr_issue_t         wr_reg;
  scariv_pkg::reg_rd_issue_t [ 2: 0] rd_regs;

  logic                          except_valid;
  scariv_pkg::except_t           except_type;
  riscv_pkg::xlen_t              except_tval;

  logic                fflags_update_valid;
  scariv_pkg::fflags_t fflags;

  scariv_vec_pkg::vlvtype_ren_idx_t vlvtype_ren_idx;
`ifdef SIMULATION
  logic [63: 0]                     kanata_id;
`endif // SIMULATION
} issue_t;

function automatic issue_t assign_issue_entry (scariv_pkg::disp_t in,
                                               scariv_pkg::cmt_id_t cmt_id,
                                               scariv_pkg::grp_id_t grp_id,
                                               logic [ 2: 0] rs_rel_hit, logic [ 2: 0] rs_phy_hit, logic [ 2: 0] rs_may_mispred);
  issue_t ret;

  ret.valid = in.valid;
  ret.inst = in.inst;
  ret.pc_addr = in.pc_addr;

  ret.cat = in.cat;
  ret.is_rvc = in.rvc_inst_valid;

  ret.brtag   = in.brtag;

  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;

  ret.oldest_valid = (in.cat == decoder_inst_cat_pkg::INST_CAT_ST) & (in.subcat == decoder_inst_cat_pkg::INST_SUBCAT_RMW) |
                     (in.cat == decoder_inst_cat_pkg::INST_CAT_CSU);

  ret.wr_reg.valid = in.wr_reg.valid;
  ret.wr_reg.typ = in.wr_reg.typ;
  ret.wr_reg.regidx = in.wr_reg.regidx;
  ret.wr_reg.rnid = in.wr_reg.rnid;

  ret.except_valid = 1'b0;
  ret.except_type  = scariv_pkg::INST_ADDR_MISALIGN;

  ret.fflags_update_valid = 1'b0;
  ret.fflags = 'h0;

  for (int rs_idx = 0; rs_idx < 3; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready = rs_rel_hit[rs_idx] & rs_may_mispred[rs_idx];
  end

`ifdef SIMULATION
  ret.kanata_id = in.kanata_id;
`endif // SIMULATION
  return ret;

endfunction // assign_issue_common


typedef enum logic [ 1: 0] {
  TVEC_MODE_DIRECT = 2'b00,
  TVEC_MODE_VECTOR = 2'b01
} tvec_mode_t;

typedef struct packed {
  logic [riscv_pkg::XLEN_W-1: 2] base;
  tvec_mode_t                    mode;
} tvec_field_t;

typedef union packed {
  tvec_field_t                   field;
  riscv_pkg::xlen_t raw_bit;
} tvec_t;


typedef struct packed {
logic [31: 3]  hpm;
logic          ir;
logic          tm;
logic          cy;
} counteren_field_t;

typedef union packed {
  counteren_field_t field;
  logic [31: 0] raw_bit;
} counteren_t;

endpackage // scariv_csu_pkg
