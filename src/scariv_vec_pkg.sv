package scariv_vec_pkg;

parameter VLEN_W = riscv_vec_conf_pkg::VLEN_W;
parameter VLENB = VLEN_W / 8;
parameter VLENBMAX = VLENB * 8;
parameter VLENBMAX_W = $clog2(VLENBMAX);
typedef logic [$clog2(VLENBMAX): 0] vlenbmax_t;
typedef logic [VLENB-1: 0]          vlenb_t;
typedef logic [riscv_vec_conf_pkg::DLEN_W/8-1: 0] dlenb_t;
parameter DLENB = riscv_vec_conf_pkg::DLEN_W/8;
parameter VEC_STEP_W = riscv_vec_conf_pkg::DLEN_W == 0 ? 1 :
                       riscv_vec_conf_pkg::VLEN_W / riscv_vec_conf_pkg::DLEN_W;

typedef logic [$clog2(VEC_STEP_W)-1: 0]         vec_pos_t;
typedef logic [riscv_vec_conf_pkg::VLEN_W-1: 0] vlen_t;
typedef logic [riscv_vec_conf_pkg::DLEN_W-1: 0] dlen_t;

parameter VEC_RNID_SIZE = 128;
parameter VEC_RNID_W    = $clog2(VEC_RNID_SIZE);

parameter VLVTYPE_REN_SIZE = 8;
parameter VLVTYPE_REN_W = $clog2(VLVTYPE_REN_SIZE);
typedef logic [$clog2(VLVTYPE_REN_SIZE)-1: 0] vlvtype_ren_idx_t;

parameter VLSU_LDQ_ENTRY_SIZE = 32;
parameter VLSU_LDQ_BANK_SIZE = 4;
parameter VLSU_LDQ_SIZE = VLSU_LDQ_ENTRY_SIZE / VLSU_LDQ_BANK_SIZE;

parameter VLSU_STQ_ENTRY_SIZE = 32;
parameter VLSU_STQ_BANK_SIZE = 4;
parameter VLSU_STQ_SIZE = VLSU_STQ_ENTRY_SIZE / VLSU_STQ_BANK_SIZE;

parameter LMUL_CHANGE_HANDLER_BASE_ADDR = 'h02000;

// Vector FPU configuration
localparam fpnew_pkg::fpu_features_t FPNEW_VEC_CONFIG = '{
  Width:         unsigned'(riscv_vec_conf_pkg::DLEN_W),
  EnableVectors: 1'b1,
  EnableNanBox:  1'b1,
  FpFmtMask:     5'b11000,
  IntFmtMask:    4'b0011
};


localparam fpnew_pkg::fpu_implementation_t FPNEW_VEC_IMPL = '{
  // PipeRegs:   '{default: scariv_conf_pkg::FPNEW_LATENCY},
    PipeRegs:   '{default: {32'h4, 32'h4, 32'h4, 32'h4, 32'h4}},   // FP32,
  UnitTypes:  '{'{default: fpnew_pkg::MERGED}, // ADDMUL
                '{default: fpnew_pkg::MERGED}, // DIVSQRT
                '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                '{default: fpnew_pkg::MERGED}},  // CONV
  PipeConfig: fpnew_pkg::DISTRIBUTED
};


typedef enum logic [ 2: 0] {
   EW8  = 0,
   EW16 = 1,
   EW32 = 2,
   EW64 = 3
} ew_t;

localparam FpnewNumLanes = fpnew_pkg::max_num_lanes(scariv_vec_pkg::FPNEW_VEC_CONFIG.Width,
                                                    scariv_vec_pkg::FPNEW_VEC_CONFIG.FpFmtMask,
                                                    scariv_vec_pkg::FPNEW_VEC_CONFIG.EnableVectors);
typedef logic [FpnewNumLanes-1: 0] fpnew_lane_t;

typedef struct packed {
  decoder_valu_ctrl_pkg::op_t op;

  scariv_pkg::cmt_id_t   cmt_id;
  scariv_pkg::grp_id_t   grp_id;
  scariv_pkg::reg_t      reg_type;
  scariv_pkg::rnid_t     rnid;
  ew_t                   vsew;
  logic                  is_mask_inst;
  dlen_t                 old_wr_data;
  vec_pos_t              step_index;
  fpnew_lane_t           simd_mask;
  vlenbmax_t             vl;
  logic                  vcomp_fin;
} aux_fpnew_t;


typedef struct packed {
  logic          vma;    // bit[    7]
  logic          vta;    // bit[    6]
  ew_t           vsew;   // bit[ 5: 3]
  logic [ 2: 0]  vlmul;  // bit[ 2: 0]
} vtype_t;

typedef struct packed {
`ifdef SIMULATION
  scariv_pkg::cmt_id_t sim_cmt_id;
  scariv_pkg::grp_id_t sim_grp_id;
`endif // SIMULATION
  vlenbmax_t vl;
  vtype_t    vtype;
} vlvtype_t;

typedef struct packed {
  logic          valid;
  vtype_t        vtype;
  logic          vill;
  vlenbmax_t     vl;
} csr_write_t;
typedef struct packed {
  vlenbmax_t    vl;
  vlenbmax_t    vlmax;
  logic [ 2: 0] vlmul;
} csr_info_t;

function automatic vlenbmax_t calc_vlmax(logic [ 2: 0] vlmul,
                                         logic [ 2: 0] vsew);
  return vlmul == 3'b101 ? (VLENB / 8) >> vsew :
         vlmul == 3'b110 ? (VLENB / 4) >> vsew :
         vlmul == 3'b111 ? (VLENB / 2) >> vsew :
         (VLENB << vlmul[ 1: 0]) >> vsew;

endfunction // calc_vlmax

typedef struct packed {
  logic                 valid;
  scariv_pkg::vaddr_t    pc_addr;
  logic [31:0]          inst;
  decoder_inst_cat_pkg::inst_cat_t    cat;
  decoder_inst_cat_pkg::inst_subcat_t subcat;
  scariv_pkg::brtag_t      brtag;

  scariv_pkg::cmt_id_t     cmt_id;
  scariv_pkg::grp_id_t     grp_id;

  scariv_pkg::reg_wr_issue_t         wr_reg;
  scariv_pkg::reg_rd_issue_t         wr_old_reg;
  scariv_pkg::rnid_t                 wr_origin_rnid;
  scariv_pkg::reg_rd_issue_t [ 2: 0] rd_regs;
  scariv_pkg::reg_rd_issue_t         v0_reg;

  logic [ 2: 0]        vec_lmul_index;
  vec_pos_t            vec_step_index;
  logic                vcomp_fin;

  logic                except_valid;
  scariv_pkg::except_t except_type;
  riscv_pkg::xlen_t   except_tval;

  logic                fflags_update_valid;
  scariv_pkg::fflags_t fflags;

  logic             vlvtype_ready;
  vlvtype_ren_idx_t vlvtype_index;
  vlvtype_t         vlvtype;
`ifdef SIMULATION
  logic [63: 0] kanata_id;
`endif // SIMULATION
} issue_t;

function automatic logic [ 3: 0] calc_num_req(issue_t issue);
  return issue.subcat == decoder_inst_cat_pkg::INST_SUBCAT_WHOLE ? issue.inst[31:29] + 'h1 :
         issue.vlvtype.vtype.vlmul[2]                            ? 'h1 :
         1 << issue.vlvtype.vtype.vlmul;
endfunction // calc_num_req



function issue_t assign_issue_common (scariv_pkg::disp_t in,
                                      scariv_pkg::cmt_id_t cmt_id,
                                      scariv_pkg::grp_id_t grp_id);
  issue_t ret;

  ret.valid = in.valid;
  ret.inst  = in.inst;
  ret.pc_addr = in.pc_addr;

  ret.cat    = in.cat;
  ret.subcat = in.subcat;
  ret.brtag  = in.brtag;

  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;

  ret.vec_lmul_index = 'h0;
  ret.vec_step_index = 'h0;
  ret.vcomp_fin      = 'h0;

  ret.wr_reg.valid = in.wr_reg.valid;
  ret.wr_reg.typ = in.wr_reg.typ;
  ret.wr_reg.regidx = in.wr_reg.regidx;
  ret.wr_reg.rnid = in.wr_reg.rnid;
  ret.wr_origin_rnid = in.wr_reg.rnid;

  ret.wr_old_reg.valid  = in.wr_reg.valid;
  ret.wr_old_reg.typ    = in.wr_reg.typ;
  ret.wr_old_reg.regidx = in.wr_reg.regidx;
  ret.wr_old_reg.rnid   = in.wr_reg.old_rnid;

  ret.v0_reg.valid  = in.v0_reg.valid;
  ret.v0_reg.typ    = in.v0_reg.typ;
  ret.v0_reg.regidx = in.v0_reg.regidx;
  ret.v0_reg.rnid   = in.v0_reg.rnid;

  ret.except_valid = 1'b0;
  ret.except_type  = scariv_pkg::INST_ADDR_MISALIGN;

  ret.fflags_update_valid = 1'b0;
  ret.fflags = 'h0;

`ifdef SIMULATION
  ret.kanata_id = in.kanata_id;
`endif // SIMULATION
  return ret;

endfunction // assign_issue_common


function issue_t assign_issue_op2 (scariv_pkg::disp_t in,
                                   scariv_pkg::cmt_id_t cmt_id,
                                   scariv_pkg::grp_id_t grp_id,
                                   logic [ 1: 0] rs_rel_hit, logic [ 1: 0] rs_phy_hit, logic [ 1: 0] rs_may_mispred, scariv_pkg::rel_bus_idx_t rs_rel_index[2]);
  issue_t ret;
  ret = assign_issue_common (in, cmt_id, grp_id);

  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[0] = in.rd_regs[rs_idx].valid & rs_rel_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[1] = 1'b0;
    if (ret.rd_regs[rs_idx].predict_ready[0]) begin
      ret.rd_regs[rs_idx].early_index = rs_rel_index[rs_idx];
    end
  end

  for (int rs_idx = 2; rs_idx < 3; rs_idx++) begin
    ret.rd_regs[rs_idx].valid = 1'b0;
  end

  return ret;

endfunction // assign_issue_op2


function issue_t assign_issue_op3 (scariv_pkg::disp_t in,
                                   scariv_pkg::cmt_id_t cmt_id,
                                   scariv_pkg::grp_id_t grp_id,
                                   logic [ 2: 0] rs_rel_hit, logic [ 2: 0] rs_phy_hit, logic [ 2: 0] rs_may_mispred, scariv_pkg::rel_bus_idx_t rs_rel_index[3]);
  issue_t ret;
  ret = assign_issue_common (in, cmt_id, grp_id);

  for (int rs_idx = 0; rs_idx < 3; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[0] = in.rd_regs[rs_idx].valid & rs_rel_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[1] = 1'b0;
    if (ret.rd_regs[rs_idx].predict_ready[0]) begin
      ret.rd_regs[rs_idx].early_index = rs_rel_index[rs_idx];
    end
  end

  return ret;

endfunction // assign_issue_op3

typedef struct packed {
  scariv_pkg::paddr_t        paddr;
  logic [ 1: 0]              req_splitted;
  logic                      haz_1st_req;
  logic [$clog2(DLENB)-1: 0] reg_offset;
} vlsu_replay_info_t;

// VLSU Replay Queue
typedef struct packed {
  logic [31: 0]                  inst;
  decoder_inst_cat_pkg::inst_cat_t    cat;
  decoder_inst_cat_pkg::inst_subcat_t subcat;
  vlvtype_t                      vlvtype;
  logic                          oldest_valid;
  scariv_pkg::reg_rd_issue_t[2:0]  rd_regs;
  scariv_pkg::reg_wr_issue_t     wr_reg;
  scariv_pkg::reg_rd_issue_t     wr_old_reg;
  scariv_pkg::rnid_t             wr_origin_rnid;
  logic                          is_uc;
  scariv_lsu_pkg::ex2_haz_t      hazard_typ;
  logic [scariv_lsu_pkg::HAZARD_INDEX_SIZE-1: 0] hazard_index;
  vec_pos_t                      vec_step_index;
  logic [ 2: 0]                  vec_lmul_index;
  vlsu_replay_info_t             replay_info;
} vlsu_replay_queue_t;

typedef enum logic [ 1: 0] {
   VSTQ_RESP_ACCEPTED  = 0,
   VSTQ_RESP_FULL_WAIT = 1,   // VSTQ is full and some older entries remained
   VSTQ_RESP_FULL_FLUSH = 2   // VSTQ is full and all entries are younger
} vstq_resp_t;


endpackage // scariv_vec_pkg


// ======================
// Vector Interfaces
// ======================
interface vec_csr_if;

  import scariv_vec_pkg::*;

  vlvtype_ren_idx_t index;
  vlvtype_t         vlvtype;

  modport master (
    output index,
    input  vlvtype
  );

  modport slave (
    input  index,
    output vlvtype
  );

endinterface // vec_csr_if


interface vlvtype_upd_if;
  import scariv_vec_pkg::*;

  logic             valid;
  vlvtype_t         vlvtype;
  vlvtype_ren_idx_t index;
`ifdef SIMULATION
  scariv_pkg::cmt_id_t sim_cmt_id;
  scariv_pkg::grp_id_t sim_grp_id;
`endif // SIMULATION

  modport master (
    output valid,
`ifdef SIMULATION
    output sim_cmt_id,
    output sim_grp_id,
`endif // SIMULATION
    output vlvtype,
    output index
  );

  modport slave (
    input valid,
`ifdef SIMULATION
    input sim_cmt_id,
    input sim_grp_id,
`endif // SIMULATION
    input vlvtype,
    input index
  );

endinterface // vlvtype_upd_if


interface vlmul_upd_if;
  logic         valid;
  logic [ 2: 0] vlmul;

  modport master (
    output valid,
    output vlmul
  );

  modport slave (
    input  valid,
    input  vlmul
  );

endinterface // vlmul_upd_if


interface vlvtype_commit_if;
  import scariv_vec_pkg::*;

  logic             valid;
  logic             lmul_change_valid;
  logic             dead;

  modport master (
    output valid,
    output lmul_change_valid,
    output dead
  );

  modport slave (
    input valid,
    input lmul_change_valid,
    input dead
  );

endinterface // vlvtype_commit_if


interface vlvtype_info_if;

  import scariv_vec_pkg::*;

  vlvtype_t         vlvtype;
  vlvtype_ren_idx_t index;
  vlvtype_ren_idx_t vsetvl_index;
  logic             ready;

  modport monitor (
    input vlvtype,
    input index,
    input vsetvl_index,
    input ready
  );

endinterface // vlvtype_resolve_if


interface vlvtype_req_if;

  import scariv_vec_pkg::*;

  logic             valid;
`ifdef SIMULATION
  scariv_pkg::cmt_id_t sim_cmt_id;
  scariv_pkg::grp_id_t sim_grp_id;
`endif // SIMULATION
  logic             checkpt_push_valid;
  logic             ready;
  logic             full;
  vlvtype_ren_idx_t vsetvl_index;
  vlvtype_ren_idx_t index;
  vlvtype_t         vlvtype;

  modport master (
    output valid,
`ifdef SIMULATION
    output sim_cmt_id,
    output sim_grp_id,
`endif // SIMULATION
    output checkpt_push_valid,
    input  ready,
    input  full,
    input  vsetvl_index,
    input  index,
    input  vlvtype
  );

  modport slave (
    input  valid,
`ifdef SIMULATION
    input sim_cmt_id,
    input sim_grp_id,
`endif // SIMULATION
    input  checkpt_push_valid,
    output ready,
    output full,
    output vsetvl_index,
    output index,
    output vlvtype
  );

endinterface // vlvtype_resolve_if


interface vec_regread_if;

  localparam WIDTH = riscv_vec_conf_pkg::DLEN_W;

  logic                      valid;
  scariv_pkg::rnid_t         rnid;
  scariv_vec_pkg::vec_pos_t  pos;
  logic [WIDTH-1: 0]         data;

  modport master(output valid, output rnid, output pos, input data);

  modport slave(input valid, input rnid, input pos, output data);

endinterface // vec_regread_if


interface vec_regwrite_if;

  localparam WIDTH = riscv_vec_conf_pkg::DLEN_W;

  logic                     valid;
  scariv_pkg::rnid_t        rd_rnid;
  scariv_vec_pkg::vec_pos_t rd_pos;
  logic [WIDTH-1: 0]        rd_data;

  modport master (
    output valid,
    output rd_rnid,
    output rd_pos,
    output rd_data
  );

  modport slave (
    input valid,
    input rd_rnid,
    input rd_pos,
    input rd_data
  );

endinterface // vec_regwrite_if


interface vec_phy_fwd_if;

  logic                     valid;
  scariv_pkg::rnid_t        rd_rnid;

  modport master (
    output valid,
    output rd_rnid
  );

  modport slave (
    input valid,
    input rd_rnid
  );

endinterface // vec_phy_fwd_if


interface vlsu_lsq_req_if;
  logic                valid;
  scariv_pkg::paddr_t  paddr;
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  scariv_pkg::rnid_t   vs3_phy_idx;
  scariv_vec_pkg::vec_pos_t vs3_pos;
  scariv_vec_pkg::dlenb_t   strb;

  // Status
  scariv_vec_pkg::vstq_resp_t resp;

  modport master (
    output valid,
    output paddr,
    output cmt_id,
    output grp_id,
    output vs3_phy_idx,
    output vs3_pos,
    output strb,
    input resp
  );

  modport slave (
    input valid,
    input paddr,
    input cmt_id,
    input grp_id,
    input vs3_phy_idx,
    input vs3_pos,
    input strb,
    output resp
  );

endinterface // vlsu_lsq_req_if


interface vstq_haz_check_if;
logic                        ex2_valid;
scariv_pkg::paddr_t          ex2_paddr;
scariv_pkg::cmt_id_t         ex2_cmt_id;
scariv_pkg::grp_id_t         ex2_grp_id;
logic                        ex2_haz_valid;

modport master
  (
   output ex2_valid,
   output ex2_paddr,
   output ex2_cmt_id,
   output ex2_grp_id,
   input  ex2_haz_valid
   );

modport slave
  (
   input  ex2_valid,
   input  ex2_paddr,
   input  ex2_cmt_id,
   input  ex2_grp_id,
   output ex2_haz_valid
   );

endinterface // vstq_haz_check_if


interface scalar_ldq_haz_check_if;
  logic                valid;
  scariv_pkg::paddr_t  paddr;
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;

  logic                haz_valid;
  scariv_pkg::cmt_id_t haz_cmt_id;
  scariv_pkg::grp_id_t haz_grp_id;

  modport master (
    output valid,
    output paddr,
    output cmt_id,
    output grp_id,
    input  haz_valid,
    input  haz_cmt_id,
    input  haz_grp_id
  );

  modport slave (
    input  valid,
    input  paddr,
    input  cmt_id,
    input  grp_id,
    output haz_valid,
    output haz_cmt_id,
    output haz_grp_id
  );

endinterface // scalar_ldq_haz_check_if
