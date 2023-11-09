// ------------------------------------------------------------------------
// NAME : scariv_vec_alu_pipe
// TYPE : module
// ------------------------------------------------------------------------
// Arithmetic Unit
// ------------------------------------------------------------------------
// ex0: Decode instruction
// ex1: Send Early-release
// ex2: Get Forwarding data
// ex3: Write Data / Done Report
// ------------------------------------------------------------------------

module scariv_vec_alu_pipe
  import decoder_valu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
 input logic i_clk,
 input logic i_reset_n,

 /* CSR information */
 csr_info_if.slave  csr_info,

 // Commit notification
 input scariv_pkg::commit_blk_t i_commit,
 br_upd_if.slave                br_upd_if,

 input scariv_vec_pkg::issue_t  i_ex0_issue,
 input scariv_pkg::phy_wr_t ex1_i_phy_wr[scariv_pkg::TGT_BUS_SIZE],

 regread_if.master      ex0_xpr_regread_rs1,
 regread_if.master      ex0_fpr_regread_rs1,

 vec_regread_if.master  vec_phy_rd_if[3],
 vec_regread_if.master  vec_phy_old_wr_if,
 vec_regwrite_if.master vec_phy_wr_if [2],
 vec_phy_fwd_if.master  vec_phy_fwd_if[2],

 output scariv_pkg::done_rpt_t o_done_report[2]
);

pipe_ctrl_t    w_ex0_pipe_ctrl;
logic          w_ex0_commit_flush;
logic          w_ex0_br_flush;
logic          w_ex0_flush;

pipe_ctrl_t             r_ex1_pipe_ctrl;
scariv_vec_pkg::issue_t r_ex1_issue;
scariv_vec_pkg::issue_t w_ex1_issue_next;
logic                   w_ex1_commit_flush;
logic                   w_ex1_br_flush;
logic                   w_ex1_flush;
riscv_pkg::xlen_t       r_ex1_rs1_data;
scariv_vec_pkg::dlen_t  r_ex1_vpr_rs_data[3];
scariv_vec_pkg::dlen_t  r_ex1_vpr_wr_old_data;
riscv_pkg::xlen_t       w_ex1_rs1_selected_data;
scariv_vec_pkg::dlen_t  r_ex1_vpr_wr_old_data_step0;
logic                   w_ex1_is_vmask_inst;
scariv_vec_pkg::dlen_t  w_fpnew_calc_result;
fpnew_pkg::status_t     w_fpnew_status;
logic                   w_fpnew_out_valid;

pipe_ctrl_t             r_ex2_pipe_ctrl;
scariv_vec_pkg::issue_t r_ex2_issue;
scariv_vec_pkg::issue_t w_ex2_issue_next;
logic                   r_ex2_wr_valid;
scariv_vec_pkg::dlen_t  r_ex2_vec_result;
scariv_vec_pkg::dlen_t  r_ex2_vec_mask_result;
logic                   r_ex2_is_vmask_inst;

assign w_ex0_commit_flush = scariv_pkg::is_commit_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, i_commit);
assign w_ex0_br_flush     = scariv_pkg::is_br_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                          br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex0_flush = w_ex0_commit_flush | w_ex0_br_flush;

// ---------------------
// EX0
// ---------------------

decoder_vec_ctrl u_pipe_ctrl (
    .inst         (i_ex0_issue.inst),
    .op           (w_ex0_pipe_ctrl.op          ),
    .is_mask_inst (w_ex0_pipe_ctrl.is_mask_inst)
);

assign ex0_xpr_regread_rs1.valid = i_ex0_issue.valid & (i_ex0_issue.rd_regs[0].typ == scariv_pkg::GPR) & i_ex0_issue.rd_regs[0].valid;
assign ex0_xpr_regread_rs1.rnid  = i_ex0_issue.rd_regs[0].rnid;

assign ex0_fpr_regread_rs1.valid = i_ex0_issue.valid & (i_ex0_issue.rd_regs[0].typ == scariv_pkg::FPR) & i_ex0_issue.rd_regs[0].valid;
assign ex0_fpr_regread_rs1.rnid  = i_ex0_issue.rd_regs[0].rnid;

generate for (genvar rs_idx = 0; rs_idx < 3; rs_idx++) begin : rs_vec_rd_loop
  assign vec_phy_rd_if[rs_idx].valid = i_ex0_issue.valid & (i_ex0_issue.rd_regs[rs_idx].typ == scariv_pkg::VPR) & i_ex0_issue.rd_regs[rs_idx].valid;
  assign vec_phy_rd_if[rs_idx].rnid  = i_ex0_issue.rd_regs[rs_idx].rnid;
  assign vec_phy_rd_if[rs_idx].pos   = i_ex0_issue.vec_step_index;
end endgenerate

assign vec_phy_old_wr_if.valid = i_ex0_issue.valid & (i_ex0_issue.wr_old_reg.typ == scariv_pkg::VPR);
assign vec_phy_old_wr_if.rnid  = i_ex0_issue.wr_old_reg.rnid;
assign vec_phy_old_wr_if.pos   = w_ex0_pipe_ctrl.is_mask_inst ? 'h0 : i_ex0_issue.vec_step_index;

assign w_ex0_commit_flush = scariv_pkg::is_commit_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, i_commit);
assign w_ex0_br_flush     = scariv_pkg::is_br_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex0_flush = w_ex0_commit_flush | w_ex0_br_flush;

// ---------------------
// EX1
// ---------------------

always_comb begin
  w_ex1_issue_next = i_ex0_issue;
  w_ex1_issue_next.valid = i_ex0_issue.valid & !w_ex0_flush;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue.valid <= 1'b0;
  end else begin
    r_ex1_issue <= w_ex1_issue_next;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;

    r_ex1_rs1_data <= i_ex0_issue.rd_regs[0].valid & (i_ex0_issue.rd_regs[0].typ == scariv_pkg::FPR) ? ex0_fpr_regread_rs1.data :
                      i_ex0_issue.rd_regs[0].valid & (i_ex0_issue.rd_regs[0].typ == scariv_pkg::GPR) ? ex0_xpr_regread_rs1.data :
                      i_ex0_issue.inst[19:15];
    r_ex1_vpr_rs_data[0] <= (i_ex0_issue.rd_regs[0].typ == scariv_pkg::FPR) & (i_ex0_issue.vlvtype.vtype.vsew == scariv_vec_pkg::EW32) ? {(riscv_vec_conf_pkg::DLEN_W/32){ex0_fpr_regread_rs1.data[31: 0]}} :
                            (i_ex0_issue.rd_regs[0].typ == scariv_pkg::FPR) & (i_ex0_issue.vlvtype.vtype.vsew == scariv_vec_pkg::EW64) ? {(riscv_vec_conf_pkg::DLEN_W/64){ex0_fpr_regread_rs1.data[63: 0]}} :
                            vec_phy_rd_if[0].data;
    r_ex1_vpr_rs_data[1] <= vec_phy_rd_if[1].data;
    r_ex1_vpr_rs_data[2] <= vec_phy_rd_if[2].data;
    r_ex1_vpr_wr_old_data <= vec_phy_old_wr_if.data;

    if (i_ex0_issue.vec_step_index == 'h0) begin
      r_ex1_vpr_wr_old_data_step0 <= vec_phy_old_wr_if.data;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

// -----------------------------
// EX2
// -----------------------------

assign w_ex1_rs1_selected_data = r_ex1_rs1_data;

logic                                      w_ex2_commit_flush;
logic                                      w_ex2_br_flush;
logic                                      w_ex2_flush;
assign w_ex2_commit_flush = scariv_pkg::is_commit_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, i_commit);
assign w_ex2_br_flush     = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex2_flush = w_ex2_commit_flush | w_ex2_br_flush;

always_comb begin
  w_ex2_issue_next = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & !w_ex1_flush;
end

scariv_vec_pkg::dlen_t w_ex1_vec_result;
logic [riscv_pkg::XLEN_W/8-1: 0] w_ex1_vec_mask_lane[riscv_vec_conf_pkg::DLEN_W/64];

assign w_ex1_is_vmask_inst = r_ex1_issue.subcat == decoder_inst_cat_pkg::INST_SUBCAT_VMASK;

scariv_vec_pkg::aux_fpnew_t w_ex1_fpnew_tag_in;
scariv_vec_pkg::aux_fpnew_t w_fpnew_tag_out;


generate for (genvar d_idx = 0; d_idx < riscv_vec_conf_pkg::DLEN_W / 64; d_idx++) begin : datapath_loop
  logic [ 7: 0] w_ex1_en_mask;
  logic [riscv_vec_conf_pkg::DLEN_W-1: 0] w_ex1_mm_mask;
  logic [ 3: 0] temp_vl;
  logic [ 7: 0] w_ex1_vr_mask_old_data;

  scariv_vec_pkg::vlenbmax_t w_vl_ew8;
  scariv_vec_pkg::vlenbmax_t w_vl_ew16;
  scariv_vec_pkg::vlenbmax_t w_vl_ew32;
  scariv_vec_pkg::vlenbmax_t w_vl_ew64;

  assign w_vl_ew8  = d_idx * 8 + r_ex1_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W /  8);
  assign w_vl_ew16 = d_idx * 4 + r_ex1_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W / 16);
  assign w_vl_ew32 = d_idx * 2 + r_ex1_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W / 32);
  assign w_vl_ew64 = d_idx * 1 + r_ex1_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W / 64);


  always_comb begin
    if (d_idx == 0) begin
      unique case (r_ex1_issue.vlvtype.vtype.vsew)
        scariv_vec_pkg::EW8  : begin w_ex1_mm_mask = (1 << r_ex1_issue.vlvtype.vl) - 1; end
        scariv_vec_pkg::EW16 : begin w_ex1_mm_mask = (1 << r_ex1_issue.vlvtype.vl) - 1; end
        scariv_vec_pkg::EW32 : begin w_ex1_mm_mask = (1 << r_ex1_issue.vlvtype.vl) - 1; end
        scariv_vec_pkg::EW64 : begin w_ex1_mm_mask = (1 << r_ex1_issue.vlvtype.vl) - 1; end
        default              : begin w_ex1_mm_mask = 'h0; end
      endcase // unique case (r_ex1_issue.vlvtype.vtype.vsew)
    end else begin
      w_ex1_mm_mask = 'h0;
    end // else: !if(d_idx == 0)
  end // always_comb

  always_comb begin
    unique case (r_ex1_issue.vlvtype.vtype.vsew)
      scariv_vec_pkg::EW8 : begin
        temp_vl       = r_ex1_issue.vlvtype.vl > w_vl_ew8      ? r_ex1_issue.vlvtype.vl - w_vl_ew8  : 0;
        w_ex1_en_mask = r_ex1_issue.vlvtype.vl > w_vl_ew8 +  8 ? {8{1'b1}} : (1 << temp_vl) - 1;
        w_ex1_vr_mask_old_data = r_ex1_vpr_wr_old_data_step0[d_idx*8 +: 8];
      end
      scariv_vec_pkg::EW16: begin
        temp_vl       = r_ex1_issue.vlvtype.vl > w_vl_ew16     ? r_ex1_issue.vlvtype.vl - w_vl_ew16 : 0;
        w_ex1_en_mask = r_ex1_issue.vlvtype.vl > w_vl_ew16 + 4 ? {4{1'b1}} : (1 << temp_vl) - 1;
        w_ex1_vr_mask_old_data = r_ex1_vpr_wr_old_data_step0[d_idx*4 +: 4];
      end
      scariv_vec_pkg::EW32: begin
        temp_vl       = r_ex1_issue.vlvtype.vl > w_vl_ew32     ? r_ex1_issue.vlvtype.vl - w_vl_ew32 : 0;
        w_ex1_en_mask = r_ex1_issue.vlvtype.vl > w_vl_ew32 + 2 ? {2{1'b1}} : (1 << temp_vl) - 1;
        w_ex1_vr_mask_old_data = r_ex1_vpr_wr_old_data_step0[d_idx*2 +: 2];
      end
      scariv_vec_pkg::EW64: begin
        temp_vl       = r_ex1_issue.vlvtype.vl > w_vl_ew64     ? r_ex1_issue.vlvtype.vl - w_vl_ew64 : 0;
        w_ex1_en_mask = r_ex1_issue.vlvtype.vl > w_vl_ew64 + 1 ? {1{1'b1}} : (1 << temp_vl) - 1;
        w_ex1_vr_mask_old_data = r_ex1_vpr_wr_old_data_step0[d_idx*1 +: 1];
      end
      default             : begin
        temp_vl = 0;
        w_ex1_en_mask = 'h0;
        w_ex1_vr_mask_old_data = 'h0;
      end
    endcase // unique case (i_sew)
  end // always_comb

  scariv_vec_alu_datapath
  u_vec_alu_datapath
    (
     .i_op            (r_ex1_pipe_ctrl.op                            ),
     .i_is_vmask_op   (w_ex1_is_vmask_inst                           ),
     .i_sew           (r_ex1_issue.vlvtype.vtype.vsew                ),
     .i_vs1           (r_ex1_vpr_rs_data[0][d_idx*64 +: 64]          ),
     .i_rs1_valid     (r_ex1_issue.rd_regs[0].typ != scariv_pkg::VPR ),
     .i_rs1           (r_ex1_rs1_data                                ),
     .i_vs2           (r_ex1_vpr_rs_data[1][d_idx*64 +: 64]          ),
     .i_wr_old        (r_ex1_vpr_wr_old_data[d_idx*64 +: 64]         ),
     .i_wr_mask_old   (w_ex1_vr_mask_old_data                        ),
     .i_en_mask       (w_ex1_en_mask                                 ),
     .i_mm_mask       (w_ex1_mm_mask                                 ),
     .i_v0            ('h0                                           ),
     .o_alu_res       (w_ex1_vec_result [d_idx*64 +: 64]             ),
     .o_mask_res      (w_ex1_vec_mask_lane [d_idx]                   )
     );
end endgenerate // block: datapath_loop


logic                   w_ex1_fpnew_valid;
fpnew_pkg::operation_e  w_ex1_fpnew_op;
logic                   w_ex1_fpnew_op_mod;
fpnew_pkg::fp_format_e  w_ex1_fpnew_dst_fp_fmt;
fpnew_pkg::fp_format_e  w_ex1_fpnew_src_fp_fmt;
fpnew_pkg::int_format_e w_ex1_fpnew_int_fmt;
logic                   w_ex1_fpnew_src_int;
logic                   w_ex1_fpnew_dst_fp;
fpnew_pkg::roundmode_e  w_ex1_fpnew_rnd_mode;

logic                   r_ex2_fpnew_valid;

always_comb begin
  case (r_ex1_pipe_ctrl.op)
    OP_FMADD , OP_FMACC    : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::FMADD   };
    OP_FMSUB , OP_FMSAC    : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b1, fpnew_pkg::FMADD   };
    OP_FNMSUB, OP_FNMSAC   : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::FNMSUB  };
    OP_FNMADD, OP_FNMACC   : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b1, fpnew_pkg::FNMSUB  };
    OP_FADD      : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::ADD     };
    OP_FSUB      : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b1, fpnew_pkg::ADD     };
    OP_FMUL      : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::MUL     };
    OP_FDIV      : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::DIV     };
    // OP_FSQRT     : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::SQRT    };
    OP_FSGNJ     : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJN    : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJX    : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::SGNJ    };
    OP_FMIN      : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::MINMAX  };
    OP_FMAX      : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::MINMAX  };
    // OP_FCVT_W_S  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::F2I     };
    // OP_FCVT_WU_S : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FEQ       : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::CMP     };
    OP_FLT       : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::CMP     };
    OP_FLE       : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::CMP     };
    OP_FNE       : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::CMP     };
    OP_FGT       : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::CMP     };
    OP_FGE       : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::CMP     };
    // OP_FCLASS    : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::CLASSIFY};
    // OP_FCVT_S_W  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::I2F     };
    // OP_FCVT_S_WU : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::I2F     };
    // OP_FSGNJ_D   : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::SGNJ    };
    // OP_FSGNJN_D  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::SGNJ    };
    // OP_FSGNJX_D  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b1, 1'b0, fpnew_pkg::SGNJ    };
    // OP_FCVT_S_D  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::F2F     };
    // OP_FCVT_D_S  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::F2F     };
    // OP_FCVT_W_D  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::F2I     };
    // OP_FCVT_WU_D : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::F2I     };
    // OP_FCVT_D_W  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::I2F     };
    // OP_FCVT_D_WU : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::I2F     };
    // OP_FCVT_L_D  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::F2I     };
    // OP_FCVT_LU_D : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::F2I     };
    // OP_FCVT_D_L  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::I2F     };
    // OP_FCVT_D_LU : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::I2F     };
    // OP_FCVT_L_S  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::F2I     };
    // OP_FCVT_LU_S : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::F2I     };
    // OP_FCVT_S_L  : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::I2F     };
    // OP_FCVT_S_LU : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b1, fpnew_pkg::I2F     };
    default      : {w_ex1_fpnew_valid, w_ex1_fpnew_op_mod, w_ex1_fpnew_op} = {1'b0, 1'b0, fpnew_pkg::FMADD   };
  endcase // case (i_op)

  // case (i_pipe_ctrl.op)
  //   OP_FCVT_W_S  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   OP_FCVT_WU_S : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   OP_FCVT_S_W  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   OP_FCVT_S_WU : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   OP_FCVT_S_D  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
  //   OP_FCVT_D_S  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP32};
  //   OP_FCVT_W_D  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP64};
  //   OP_FCVT_WU_D : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP64};
  //   OP_FCVT_D_W  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP32};
  //   OP_FCVT_D_WU : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP32};
  //   OP_FCVT_L_D  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
  //   OP_FCVT_LU_D : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
  //   OP_FCVT_D_L  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP64};
  //   OP_FCVT_D_LU : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP64};
  //   OP_FCVT_L_S  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   OP_FCVT_LU_S : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   OP_FCVT_S_L  : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   OP_FCVT_S_LU : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
  //   default      : {w_ex1_fpnew_dst_fp, w_ex1_fpnew_src_int, w_ex1_fpnew_int_fmt, w_ex1_fpnew_dst_fp_fmt, w_ex1_fpnew_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
  // endcase // case (i_pipe_ctrl.op)

  w_ex1_fpnew_rnd_mode = r_ex1_pipe_ctrl.op inside {OP_FGE, OP_FLE}     ? fpnew_pkg::RNE :
                         r_ex1_pipe_ctrl.op inside {OP_FGT, OP_FLT}     ? fpnew_pkg::RTZ :
                         r_ex1_pipe_ctrl.op inside {OP_FEQ, OP_FNE}     ? fpnew_pkg::RDN :
                         r_ex1_pipe_ctrl.op inside {OP_FSGNJ,  OP_FMIN} ? fpnew_pkg::RNE :
                         r_ex1_pipe_ctrl.op inside {OP_FSGNJN, OP_FMAX} ? fpnew_pkg::RTZ :
                         r_ex1_pipe_ctrl.op == OP_FSGNJX                ? fpnew_pkg::RDN :
                         fpnew_pkg::roundmode_e'(csr_info.fcsr[ 7: 5]);
end // always_comb

logic [ 2: 0][riscv_vec_conf_pkg::DLEN_W-1: 0] w_fpnew_ex1_rs_data;
assign w_fpnew_ex1_rs_data[0] = r_ex1_pipe_ctrl.op inside {OP_FADD, OP_FSUB}                         ? 'h0                  :
                                // r_ex1_pipe_ctrl.op inside {OP_FMADD, OP_FMSUB, OP_FNMADD, OP_FNMSUB} ? r_ex1_vpr_rs_data[0] :
                                r_ex1_pipe_ctrl.op inside {OP_FSGNJ, OP_FSGNJN, OP_FSGNJX, OP_FLE, OP_FLT} ? r_ex1_vpr_rs_data[1] :
                                r_ex1_vpr_rs_data[0];
assign w_fpnew_ex1_rs_data[1] = r_ex1_pipe_ctrl.op inside {OP_FADD, OP_FSUB}                         ? r_ex1_vpr_rs_data[1] :
                                r_ex1_pipe_ctrl.op inside {OP_FMADD, OP_FMSUB, OP_FNMADD, OP_FNMSUB} ? r_ex1_vpr_rs_data[2] :
                                r_ex1_pipe_ctrl.op inside {OP_FSGNJ, OP_FSGNJN, OP_FSGNJX, OP_FLE, OP_FLT} ? r_ex1_vpr_rs_data[0] :
                                r_ex1_vpr_rs_data[1];
assign w_fpnew_ex1_rs_data[2] = r_ex1_pipe_ctrl.op inside {OP_FADD, OP_FSUB}                         ? r_ex1_vpr_rs_data[0] :
                                r_ex1_pipe_ctrl.op inside {OP_FMADD, OP_FMSUB, OP_FNMADD, OP_FNMSUB} ? r_ex1_vpr_rs_data[1] :
                                r_ex1_vpr_rs_data[2];

assign w_ex1_fpnew_src_fp_fmt = r_ex1_issue.vlvtype.vtype.vsew == scariv_vec_pkg::EW32 ? fpnew_pkg::FP32  : fpnew_pkg::FP64;
assign w_ex1_fpnew_dst_fp_fmt = r_ex1_issue.vlvtype.vtype.vsew == scariv_vec_pkg::EW32 ? fpnew_pkg::FP32  : fpnew_pkg::FP64;
assign w_ex1_fpnew_int_fmt    = r_ex1_issue.vlvtype.vtype.vsew == scariv_vec_pkg::EW32 ? fpnew_pkg::INT32 : fpnew_pkg::INT64;

assign w_ex1_fpnew_tag_in.op           = r_ex1_pipe_ctrl.op;
assign w_ex1_fpnew_tag_in.reg_type     = r_ex1_issue.wr_reg.typ;
assign w_ex1_fpnew_tag_in.rnid         = r_ex1_issue.wr_reg.rnid;
assign w_ex1_fpnew_tag_in.cmt_id       = r_ex1_issue.cmt_id;
assign w_ex1_fpnew_tag_in.grp_id       = r_ex1_issue.grp_id;
assign w_ex1_fpnew_tag_in.vsew         = r_ex1_issue.vlvtype.vtype.vsew;
assign w_ex1_fpnew_tag_in.is_mask_inst = r_ex1_pipe_ctrl.is_mask_inst;
assign w_ex1_fpnew_tag_in.old_wr_data  = r_ex1_vpr_wr_old_data;
assign w_ex1_fpnew_tag_in.step_index   = r_ex1_issue.vec_step_index;

// --------------
// FPU Pipeline
// --------------
fpnew_top
  #(
    // FPU configuration
    .Features       (scariv_vec_pkg::FPNEW_VEC_CONFIG),
    .Implementation (scariv_vec_pkg::FPNEW_VEC_IMPL),
    .TagType        (scariv_vec_pkg::aux_fpnew_t)
    )
u_fpnew_top
(
 .clk_i  (i_clk),
 .rst_ni (i_reset_n),
 // Input signals
 .operands_i    (w_fpnew_ex1_rs_data    ),
 .rnd_mode_i    (w_ex1_fpnew_rnd_mode   ),
 .op_i          (w_ex1_fpnew_op         ),
 .op_mod_i      (w_ex1_fpnew_op_mod     ),
 .src_fmt_i     (w_ex1_fpnew_src_fp_fmt ),
 .dst_fmt_i     (w_ex1_fpnew_dst_fp_fmt ),
 .int_fmt_i     (w_ex1_fpnew_int_fmt    ),
 .vectorial_op_i(1'b1                   ),
 .tag_i         (w_ex1_fpnew_tag_in     ),
 .simd_mask_i   (1'b0                   ),
 // Input Handshake
 .in_valid_i (w_ex1_fpnew_valid ),
 .in_ready_o (                  ),
 .flush_i    (w_ex1_commit_flush),
 // Output signals
 .result_o (w_fpnew_calc_result),
 .status_o (w_fpnew_status     ),
 .tag_o    (w_fpnew_tag_out    ),
 // Output handshake
 .out_valid_o (w_fpnew_out_valid),
 .out_ready_i (1'b1              ),
 // Indication of valid data in flight
 .busy_o ()
);


logic [riscv_vec_conf_pkg::DLEN_W-1: 0]     w_fpnew_mask_result;

always_comb begin
  w_fpnew_mask_result = 'h0;
  case (w_fpnew_tag_out.vsew)
    scariv_vec_pkg::EW32 : begin
      for (int d_idx = 0; d_idx < riscv_vec_conf_pkg::DLEN_W / 32; d_idx++) begin
        w_fpnew_mask_result [d_idx] = w_fpnew_tag_out.op == OP_FNE ? ~w_fpnew_calc_result[32*d_idx] : w_fpnew_calc_result[32*d_idx];
      end
    end
    scariv_vec_pkg::EW64 : begin
      for (int d_idx = 0; d_idx < riscv_vec_conf_pkg::DLEN_W / 64; d_idx++) begin
        w_fpnew_mask_result [d_idx] = w_fpnew_tag_out.op == OP_FNE ? ~w_fpnew_calc_result[64*d_idx] : w_fpnew_calc_result[64*d_idx];
      end
    end
    default : begin
      w_fpnew_mask_result = 'h0;
    end
  endcase // case (r_ex1_issue.vlvtype.vtype.vsew)
end // always_comb

scariv_vec_pkg::dlen_t w_fpnew_mask_wr_result;
scariv_vec_pkg::dlen_t r_fpnew_mask_wr_result;
scariv_vec_pkg::dlen_t w_fpnew_mask_wr_result_next;

generate if (scariv_vec_pkg::VEC_STEP_W == 1) begin : fpnew_mask_vstep_1
  always_comb begin
    case (w_fpnew_tag_out.vsew)
      scariv_vec_pkg::EW32 :
        w_fpnew_mask_wr_result_next = {w_fpnew_tag_out.old_wr_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/4],
                                       w_fpnew_mask_result[riscv_vec_conf_pkg::DLEN_W/32-1: 0]};
      scariv_vec_pkg::EW64 :
        w_fpnew_mask_wr_result_next = {w_fpnew_tag_out.old_wr_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/8],
                                       w_fpnew_mask_result[riscv_vec_conf_pkg::DLEN_W/64-1: 0]};
      default : w_fpnew_mask_wr_result_next = 'h0;
    endcase // case (w_fpnew_tag_out.vsew)
  end // always_comb
end else begin : mask_vstep_n0 // if (scariv_vec_pkg::VEC_STEP_W == 1)
  always_comb begin
    case (w_fpnew_tag_out.vsew)
      scariv_vec_pkg::EW32 :
        w_fpnew_mask_wr_result_next = {w_fpnew_tag_out.old_wr_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/4],
                                       w_fpnew_mask_result        [riscv_vec_conf_pkg::DLEN_W/32-1: 0],
                                       r_fpnew_mask_wr_result     [scariv_vec_pkg::VLENB/4 -1: riscv_vec_conf_pkg::DLEN_W/32]};
      scariv_vec_pkg::EW64 :
        w_fpnew_mask_wr_result_next = {w_fpnew_tag_out.old_wr_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/8],
                                       w_fpnew_mask_result        [riscv_vec_conf_pkg::DLEN_W/64-1: 0],
                                       r_fpnew_mask_wr_result     [scariv_vec_pkg::VLENB/8 -1: riscv_vec_conf_pkg::DLEN_W/64]};
      default : w_fpnew_mask_wr_result_next = 'h0;
    endcase // case (w_fpnew_tag_out.vsew)
  end // always_comb

  always_ff @ (posedge i_clk) begin
    r_fpnew_mask_wr_result <= w_fpnew_mask_wr_result_next;
  end

end endgenerate


scariv_vec_pkg::dlen_t w_ex1_vec_mask_result;

always_comb begin
  case (r_ex1_issue.vlvtype.vtype.vsew)
    scariv_vec_pkg::EW8  : begin
      for (int d_idx = 0; d_idx < riscv_vec_conf_pkg::DLEN_W / 64; d_idx++) begin
        w_ex1_vec_mask_result [d_idx * riscv_pkg::XLEN_W/ 8 +: riscv_pkg::XLEN_W/ 8] = w_ex1_vec_mask_lane[d_idx][riscv_pkg::XLEN_W/8-1: 0];
      end
    end
    scariv_vec_pkg::EW16 : begin
      for (int d_idx = 0; d_idx < riscv_vec_conf_pkg::DLEN_W / 64; d_idx++) begin
        w_ex1_vec_mask_result [d_idx * riscv_pkg::XLEN_W/16 +: riscv_pkg::XLEN_W/16] = w_ex1_vec_mask_lane[d_idx][riscv_pkg::XLEN_W/16-1: 0];
      end
    end
    scariv_vec_pkg::EW32 : begin
      for (int d_idx = 0; d_idx < riscv_vec_conf_pkg::DLEN_W / 64; d_idx++) begin
        w_ex1_vec_mask_result [d_idx * riscv_pkg::XLEN_W/32 +: riscv_pkg::XLEN_W/32] = w_ex1_vec_mask_lane[d_idx][riscv_pkg::XLEN_W/32-1: 0];
      end
    end
    scariv_vec_pkg::EW64 : begin
      for (int d_idx = 0; d_idx < riscv_vec_conf_pkg::DLEN_W / 64; d_idx++) begin
        w_ex1_vec_mask_result [d_idx * riscv_pkg::XLEN_W/64 +: riscv_pkg::XLEN_W/64] = w_ex1_vec_mask_lane[d_idx][riscv_pkg::XLEN_W/64-1: 0];
      end
    end
    default :
      w_ex1_vec_mask_result = 'h0;
  endcase // case (r_ex1_issue.vlvtype.vtype.vsew)
end // always_comb

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_issue <= 'h0;
    r_ex2_wr_valid <= 1'b0;
    r_ex2_fpnew_valid <= 1'b0;
  end else begin
    r_ex2_issue <= w_ex2_issue_next;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    r_ex2_is_vmask_inst <= w_ex1_is_vmask_inst;

    r_ex2_fpnew_valid <= w_ex1_fpnew_valid;
    r_ex2_wr_valid <= r_ex1_issue.wr_reg.valid;

    r_ex2_vec_result <= w_ex1_vec_result;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

generate if (scariv_vec_pkg::VEC_STEP_W == 1) begin : mask_vstep_1
  always_ff @(posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ex2_vec_mask_result <= 'h0;
    end else begin
      if (r_ex1_pipe_ctrl.is_mask_inst) begin
        case (r_ex1_issue.vlvtype.vtype.vsew)
          scariv_vec_pkg::EW8 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB],
                                      w_ex1_vec_mask_result[riscv_vec_conf_pkg::DLEN_W/ 8-1: 0]};
          scariv_vec_pkg::EW16 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/2],
                                      w_ex1_vec_mask_result[riscv_vec_conf_pkg::DLEN_W/16-1: 0]};
          scariv_vec_pkg::EW32 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/4],
                                      w_ex1_vec_mask_result[riscv_vec_conf_pkg::DLEN_W/32-1: 0]};
          scariv_vec_pkg::EW64 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/8],
                                      w_ex1_vec_mask_result[riscv_vec_conf_pkg::DLEN_W/64-1: 0]};
          default : r_ex2_vec_mask_result <= 'h0;
        endcase // case (r_ex1_issue.vlvtype.vtype.vsew)
      end // if (r_ex1_pipe_ctrl.is_mask_inst)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end else begin : mask_vstep_n0 // if (scariv_vec_pkg::VEC_STEP_W == 1)

  always_ff @(posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ex2_vec_mask_result <= 'h0;
    end else begin
      if (r_ex1_pipe_ctrl.is_mask_inst) begin
        case (r_ex1_issue.vlvtype.vtype.vsew)
          scariv_vec_pkg::EW8 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data_step0[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB],
                                      w_ex1_vec_mask_result      [riscv_vec_conf_pkg::DLEN_W/ 8-1: 0],
                                      r_ex2_vec_mask_result      [scariv_vec_pkg::VLENB   -1: riscv_vec_conf_pkg::DLEN_W/ 8]};
          scariv_vec_pkg::EW16 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data_step0[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/2],
                                      w_ex1_vec_mask_result      [riscv_vec_conf_pkg::DLEN_W/16-1: 0],
                                      r_ex2_vec_mask_result      [scariv_vec_pkg::VLENB/2 -1: riscv_vec_conf_pkg::DLEN_W/16]};
          scariv_vec_pkg::EW32 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data_step0[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/4],
                                      w_ex1_vec_mask_result      [riscv_vec_conf_pkg::DLEN_W/32-1: 0],
                                      r_ex2_vec_mask_result      [scariv_vec_pkg::VLENB/4 -1: riscv_vec_conf_pkg::DLEN_W/32]};
          scariv_vec_pkg::EW64 :
            r_ex2_vec_mask_result <= {r_ex1_vpr_wr_old_data_step0[riscv_vec_conf_pkg::DLEN_W   -1: scariv_vec_pkg::VLENB/8],
                                      w_ex1_vec_mask_result      [riscv_vec_conf_pkg::DLEN_W/64-1: 0],
                                      r_ex2_vec_mask_result      [scariv_vec_pkg::VLENB/8 -1: riscv_vec_conf_pkg::DLEN_W/64]};
          default : r_ex2_vec_mask_result <= 'h0;
        endcase // case (r_ex1_issue.vlvtype.vtype.vsew)
      end // if (r_ex1_pipe_ctrl.is_mask_inst)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end endgenerate // block: mask_vstep_n0


always_comb begin
  vec_phy_wr_if[0].valid   = r_ex2_wr_valid & ~r_ex2_fpnew_valid & (r_ex2_pipe_ctrl.is_mask_inst ? (r_ex2_issue.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1) : 1'b1);
  vec_phy_wr_if[0].rd_rnid = r_ex2_issue.wr_reg.rnid;
  vec_phy_wr_if[0].rd_data = r_ex2_pipe_ctrl.is_mask_inst ? r_ex2_vec_mask_result : r_ex2_vec_result;
  vec_phy_wr_if[0].rd_pos  = r_ex2_pipe_ctrl.is_mask_inst ? 'h0 : r_ex2_issue.vec_step_index;

  vec_phy_fwd_if[0].valid   = vec_phy_wr_if[0].valid;
  vec_phy_fwd_if[0].rd_rnid = r_ex2_issue.wr_reg.rnid;

  o_done_report[0].valid  = r_ex2_issue.valid & ~r_ex2_fpnew_valid & (r_ex2_is_vmask_inst | (r_ex2_issue.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1));
  o_done_report[0].cmt_id = r_ex2_issue.cmt_id;
  o_done_report[0].grp_id = r_ex2_issue.grp_id;
  o_done_report[0].fflags_update_valid = 1'b0;
  o_done_report[0].fflags = 'h0;

  vec_phy_wr_if[1].valid   = w_fpnew_out_valid;
  vec_phy_wr_if[1].rd_rnid = w_fpnew_tag_out.rnid;
  vec_phy_wr_if[1].rd_data = w_fpnew_tag_out.is_mask_inst ? ((w_fpnew_tag_out.step_index == scariv_vec_pkg::VEC_STEP_W-1) ? w_fpnew_mask_wr_result_next : 'h0) :
                             w_fpnew_calc_result;
  vec_phy_wr_if[1].rd_pos  = w_fpnew_tag_out.is_mask_inst & (w_fpnew_tag_out.step_index == scariv_vec_pkg::VEC_STEP_W-1) ? 'h0 : w_fpnew_tag_out.step_index;

  vec_phy_fwd_if[1].valid   = vec_phy_wr_if[1].valid;
  vec_phy_fwd_if[1].rd_rnid = w_fpnew_tag_out.rnid;

  o_done_report[1].valid  = w_fpnew_out_valid & (w_fpnew_tag_out.step_index == scariv_vec_pkg::VEC_STEP_W-1);
  o_done_report[1].cmt_id = w_fpnew_tag_out.cmt_id;
  o_done_report[1].grp_id = w_fpnew_tag_out.grp_id;
  o_done_report[1].fflags_update_valid = 1'b0;
  o_done_report[1].fflags = 'h0;

end // always_comb


`ifdef SIMULATION
// Kanata
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (i_ex0_issue.valid) begin
      log_stage (i_ex0_issue.kanata_id, "EX0");
    end
    if (r_ex1_issue.valid) begin
      log_stage (r_ex1_issue.kanata_id, "EX1");
    end
    if (r_ex2_issue.valid) begin
      log_stage (r_ex2_issue.kanata_id, "EX2");
    end
  end
end

`endif // SIMULATION

endmodule // scariv_vec_alu_pipe
