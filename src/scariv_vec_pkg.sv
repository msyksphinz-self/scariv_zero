package scariv_vec_pkg;

parameter VLEN_W = riscv_vec_conf_pkg::VLEN_W;
parameter VLENB = VLEN_W / 8;
parameter VLENBMAX = VLENB * 8;
parameter VLENBMAX_W = $clog2(VLENBMAX);
typedef logic [$clog2(VLENBMAX)-1: 0] vlenbmax_t;
typedef logic [VLENB-1: 0]            vlenb_t;
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


// Vector FPU configuration
localparam fpnew_pkg::fpu_features_t FPNEW_VEC_CONFIG = '{
  Width:         unsigned'(riscv_vec_conf_pkg::DLEN_W),
  EnableVectors: 1'b1,
  EnableNanBox:  1'b1,
  FpFmtMask:     5'b11000,
  IntFmtMask:    4'b0011
};


typedef enum logic [ 2: 0] {
   EW8  = 0,
   EW16 = 1,
   EW32 = 2,
   EW64 = 3
} ew_t;


typedef struct packed {
  logic          vma;    // bit[    7]
  logic          vta;    // bit[    6]
  ew_t           vsew;   // bit[ 5: 3]
  logic [ 2: 0]  vlmul;  // bit[ 2: 0]
} vtype_t;

typedef struct packed {
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
  vlenbmax_t vl;
  vlenbmax_t vlmax;
} csr_info_t;

function automatic vlenbmax_t calc_vlmax(logic [ 2: 0] vlmul,
                                         logic [ 2: 0] vsew);
  return (VLENB << vlmul) >> vsew;

endfunction


typedef struct packed {
  logic                 valid;
  scariv_pkg::vaddr_t    pc_addr;
  logic [31:0]          inst;
  scariv_pkg::inst_cat_t cat;
  scariv_pkg::inst_subcat_t subcat;
  scariv_pkg::brtag_t      brtag;

  scariv_pkg::cmt_id_t     cmt_id;
  scariv_pkg::grp_id_t     grp_id;

  scariv_pkg::reg_wr_issue_t         wr_reg;
  scariv_pkg::reg_rd_issue_t         wr_old_reg;
  scariv_pkg::reg_rd_issue_t [ 2: 0] rd_regs;

  vec_pos_t            vec_step_index;

  logic                except_valid;
  scariv_pkg::except_t except_type;
  scariv_pkg::xlen_t   except_tval;

  logic                fflags_update_valid;
  scariv_pkg::fflags_t fflags;

  logic             vlvtype_ready;
  vlvtype_ren_idx_t vlvtype_index;
  vlvtype_t         vlvtype;
`ifdef SIMULATION
  logic [63: 0] kanata_id;
`endif // SIMULATION
} issue_t;


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

  ret.wr_reg.valid = in.wr_reg.valid;
  ret.wr_reg.typ = in.wr_reg.typ;
  ret.wr_reg.regidx = in.wr_reg.regidx;
  ret.wr_reg.rnid = in.wr_reg.rnid;

  ret.wr_old_reg.valid  = in.wr_reg.valid;
  ret.wr_old_reg.typ    = in.wr_reg.typ;
  ret.wr_old_reg.regidx = in.wr_reg.regidx;
  ret.wr_old_reg.rnid   = in.wr_reg.old_rnid;

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
                                   logic [ 1: 0] rs_rel_hit, logic [ 1: 0] rs_phy_hit, logic [ 1: 0] rs_may_mispred, scariv_pkg::rel_bus_idx_t rs_rel_index[2],
                                   vlvtype_t vlvtype);
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

  for (int rs_idx = 2; rs_idx < 3; rs_idx++) begin
    ret.rd_regs[rs_idx].valid = 1'b0;
  end

  return ret;

endfunction // assign_issue_op3


endpackage // scariv_vec_pkg


// ======================
// Vector Interfaces
// ======================
interface vec_csr_if;

  import scariv_vec_pkg::*;

  csr_write_t write;
  csr_info_t  info;

  modport master (
    input  write,
    output info
  );

  modport slave (
    output write,
    input  info
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


interface vlvtype_commit_if;
  import scariv_vec_pkg::*;

  logic             valid;
// vlvtype_ren_idx_t index;

  modport master (
    output valid
   //  output index
  );

  modport slave (
    input valid
    // input index
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
  logic             checkpt_push_valid;
  logic             ready;
  logic             full;
  vlvtype_ren_idx_t vsetvl_index;
  vlvtype_ren_idx_t index;
  vlvtype_t         vlvtype;

  modport master (
    output valid,
    output checkpt_push_valid,
    input  ready,
    input  full,
    input  vsetvl_index,
    input  index,
    input  vlvtype
  );

  modport slave (
    input  valid,
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
