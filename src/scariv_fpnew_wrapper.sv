// ------------------------------------------------------------------------
// NAME : scariv_fpnew_wrapper
// TYPE : module
// ------------------------------------------------------------------------
// Wrapper for FPNew
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_fpnew_wrapper
  import decoder_fpu_ctrl_pkg::*;
  import scariv_fpu_pkg::*;
#(
  parameter SCHED_ENTRY_SIZE = 8
  )
(
   input logic               i_clk,
   input logic               i_reset_n,

   // Commit notification
   commit_if.monitor commit_if,
   br_upd_if.slave                br_upd_if,

   input logic                i_valid,
   input pipe_ctrl_t          i_pipe_ctrl,
   input scariv_pkg::cmt_id_t i_cmt_id,
   input scariv_pkg::grp_id_t i_grp_id,
   input scariv_pkg::rnid_t   i_rnid,
   input scariv_pkg::reg_t    i_reg_type,
   input logic                i_frm_invalid,
   input logic [ 2: 0]        i_rnd_mode,

   input scariv_pkg::alen_t    i_rs1,
   input scariv_pkg::alen_t    i_rs2,
   input scariv_pkg::alen_t    i_rs3,

   output logic                o_busy,

   output logic                o_valid,
   output scariv_pkg::alen_t   o_result,
   output logic [ 4: 0]        o_fflags,
   output scariv_pkg::cmt_id_t o_cmt_id,
   output scariv_pkg::grp_id_t o_grp_id,
   output scariv_pkg::rnid_t   o_rnid,
   output logic                o_frm_invalid,
   output scariv_pkg::reg_t    o_reg_type
   );

logic     w_fma64_ready;
logic     w_fma32_ready;

// assign o_ready = w_fma64_ready & w_fma32_ready;

typedef struct packed {
  fpnew_pkg::operation_e op;
  logic                  op_mod;
  scariv_pkg::reg_t      reg_type;
  scariv_pkg::rnid_t     rnid;
  logic                  frm_invalid;
  logic                  output_is_int32;
} aux_fpnew_t;

logic                                    w_fma32_in_valid;
logic                                    w_noncomp32_in_valid;

logic                                    w_fma_valid;
logic                                    w_noncomp_valid;
logic                                    w_fdiv_valid;

fpnew_pkg::operation_e                   w_fpnew_op;
logic                                    w_fpnew_op_mod;
aux_fpnew_t                              w_fpnew_in_aux;
aux_fpnew_t                              w_fpnew_out_aux;

logic [2:0][31:0]                        w_fma32_rs;
logic [2: 0]                             w_fma32_boxed;
logic [31: 0]                            w_fma32_result;
fpnew_pkg::status_t                      w_fma32_fflags;
logic                                    w_fma32_out_valid;
logic [ 4: 0]                            w_fma32_out_fflags;
aux_fpnew_t                              w_fma32_aux;

logic [ 1: 0][31: 0]                     w_noncomp32_rs;
logic [ 1: 0]                            w_noncomp32_boxed;
logic                                    w_noncomp32_out_valid;
logic [31: 0]                            w_noncomp32_result;
fpnew_pkg::status_t                      w_noncomp32_status;
fpnew_pkg::classmask_e                   w_noncomp32_class_mask;
logic [ 4: 0]                            w_noncomp32_out_fflags;
aux_fpnew_t                              w_noncomp32_aux;

fpnew_pkg::fp_format_e                   w_dst_fp_fmt;
fpnew_pkg::fp_format_e                   w_src_fp_fmt;
fpnew_pkg::int_format_e                  w_int_fmt;
logic                                    w_out_fp;
logic                                    w_cvt_valid;
logic [ 4: 0]                            w_cast_out_fflags;
aux_fpnew_t                              w_cast_aux;

/* verilator lint_off UNOPTFLAT */
logic [ 1: 0][riscv_fpu_pkg::FLEN_W-1: 0]    w_fdiv_rs;
logic [ 1: 0]                            w_fdiv_boxed;
logic                                    w_fdiv_out_valid;
logic [riscv_fpu_pkg::FLEN_W-1: 0]           w_fdiv_result;
fpnew_pkg::status_t                      w_fdiv_status;
fpnew_pkg::classmask_e                   w_fdiv_class_mask;
logic [ 4: 0]                            w_fdiv_out_fflags;
aux_fpnew_t                              w_fdiv_aux;

logic                                    w_commit_flush;
logic                                    w_in_br_flush;
logic                                    w_in_flush;

aux_fpnew_t w_aux_fpnew_in;
aux_fpnew_t w_aux_fpnew_out;

logic [riscv_fpu_pkg::FLEN_W-1: 0] w_result;

fpnew_pkg::status_t                w_fpnew_fflags;
logic                              w_fpnew_out_valid;

typedef struct packed {
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  logic                dead;
} aux_fpnew_age_t;

aux_fpnew_age_t r_age_fifo[scariv_conf_pkg::FPNEW_LATENCY];
aux_fpnew_age_t r_longfpu_age;
aux_fpnew_age_t w_longfpu_age_next;
logic                  w_longfpu_valid_next;
logic                  r_longfpu_valid;

logic                  w_age_fifo_last_br_flush_valid;
logic                  w_age_fifo_last_dead;

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::FPNEW_LATENCY; l_idx++) begin : age_fifo_loop
  if (l_idx == 0) begin
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_age_fifo[l_idx].dead <= 1'b0;
      end else begin
        r_age_fifo[l_idx].cmt_id <= i_cmt_id;
        r_age_fifo[l_idx].grp_id <= i_grp_id;
        r_age_fifo[l_idx].dead <= 1'b0;
      end
    end

  end else begin // if (l_idx == 0)
    logic w_br_flush;
    assign w_br_flush = scariv_pkg::is_br_flush_target(r_age_fifo[l_idx-1].cmt_id, r_age_fifo[l_idx-1].grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;

    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_age_fifo[l_idx].dead <= 1'b0;
      end else begin
        r_age_fifo[l_idx] <= r_age_fifo[l_idx-1];
        if (w_br_flush) begin
          r_age_fifo[l_idx].dead <= 1'b1;
        end
      end
    end
  end // else: !if(l_idx == 0)
end endgenerate

assign w_age_fifo_last_br_flush_valid = scariv_pkg::is_br_flush_target(r_age_fifo[scariv_conf_pkg::FPNEW_LATENCY-1].cmt_id, r_age_fifo[scariv_conf_pkg::FPNEW_LATENCY-1].grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_age_fifo_last_dead = r_age_fifo[scariv_conf_pkg::FPNEW_LATENCY-1].dead | w_age_fifo_last_br_flush_valid;


always_comb begin
  w_longfpu_age_next = r_longfpu_age;
  w_longfpu_valid_next = r_longfpu_valid;

  if (scariv_pkg::is_br_flush_target(r_longfpu_age.cmt_id, r_longfpu_age.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update) begin
    w_longfpu_age_next.dead = 1'b1;
  end

  if (w_fpnew_out_valid & (w_aux_fpnew_out.op inside {fpnew_pkg::DIV, fpnew_pkg::SQRT}) | w_commit_flush) begin
    w_longfpu_valid_next = 1'b0;
  end
  if (i_valid & ~w_in_flush & w_fdiv_valid) begin
    w_longfpu_valid_next = 1'b1;

    w_longfpu_age_next.cmt_id = i_cmt_id;
    w_longfpu_age_next.grp_id = i_grp_id;
    w_longfpu_age_next.dead   = 1'b0;
  end
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_longfpu_valid <= 1'b0;
    r_longfpu_age.dead <= 1'b0;
  end else begin
    r_longfpu_valid <= w_longfpu_valid_next;
    r_longfpu_age <= w_longfpu_age_next;
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign w_aux_fpnew_in.op          = w_fpnew_op;
assign w_aux_fpnew_in.op_mod      = w_fpnew_op_mod;
assign w_aux_fpnew_in.reg_type    = i_reg_type;
assign w_aux_fpnew_in.rnid        = i_rnid;
assign w_aux_fpnew_in.frm_invalid = i_frm_invalid;
assign w_aux_fpnew_in.output_is_int32 = i_pipe_ctrl.op inside {OP_FCVT_W_S, OP_FCVT_W_D};

assign w_fma32_rs[0] = (w_fpnew_op == fpnew_pkg::ADD) ? 'h0          : i_rs1[31: 0];
assign w_fma32_rs[1] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs1[31: 0] : i_rs2[31: 0];
assign w_fma32_rs[2] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs2[31: 0] : i_rs3[31: 0];
generate if (riscv_fpu_pkg::FLEN_W == 64) begin
  assign w_fma32_boxed[0] = (w_fpnew_op == fpnew_pkg::ADD) ? 1'b1          : &i_rs1[63:32];
  assign w_fma32_boxed[1] = (w_fpnew_op == fpnew_pkg::ADD) ? &i_rs1[63:32] : &i_rs2[63:32];
  assign w_fma32_boxed[2] = (w_fpnew_op == fpnew_pkg::ADD) ? &i_rs2[63:32] : &i_rs3[63:32];
end else begin
  assign w_fma32_boxed[2:0] = 3'b111;
end
endgenerate

assign w_noncomp32_rs[0] = i_rs1[31: 0];
assign w_noncomp32_rs[1] = i_rs2[31: 0];
generate if (riscv_fpu_pkg::FLEN_W == 64) begin
  assign w_noncomp32_boxed = {&i_rs2[63:32], &i_rs1[63:32]};
end else begin
  assign w_noncomp32_boxed = 2'b11;
end
endgenerate


generate if (riscv_fpu_pkg::FLEN_W == 64) begin
  assign w_fdiv_rs[0] = i_pipe_ctrl.size == SIZE_DW ? i_rs1 :
                        &i_rs1[63:32] ? i_rs1 : 64'hffffffff7fc00000;
  assign w_fdiv_rs[1] = i_pipe_ctrl.op == OP_FSQRT_S || i_pipe_ctrl.op == OP_FSQRT_D ? w_fdiv_rs[0] :
                        i_pipe_ctrl.size == SIZE_DW ? i_rs2 :
                        &i_rs2[63:32] ? i_rs2 : 64'hffffffff7fc00000;
  assign w_fdiv_boxed = 2'b11;
end else begin
  assign w_fdiv_rs[0] = i_rs1;
  assign w_fdiv_rs[1] = i_pipe_ctrl.op == OP_FSQRT_S || i_pipe_ctrl.op == OP_FSQRT_D ? i_rs1 : i_rs2;
  assign w_fdiv_boxed = 2'b11;
end
endgenerate


always_comb begin
  case (i_pipe_ctrl.op)
    OP_FMADD_S , OP_FMADD_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::FMADD   };
    OP_FMSUB_S , OP_FMSUB_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b1, fpnew_pkg::FMADD   };
    OP_FNMSUB_S, OP_FNMSUB_D : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::FNMSUB  };
    OP_FNMADD_S, OP_FNMADD_D : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b1, fpnew_pkg::FNMSUB  };
    OP_FADD_S  , OP_FADD_D   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::ADD     };
    OP_FSUB_S  , OP_FSUB_D   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b1, fpnew_pkg::ADD     };
    OP_FMUL_S  , OP_FMUL_D   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::MUL     };
    OP_FDIV_S  , OP_FDIV_D   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b1, 1'b0, fpnew_pkg::DIV     };
    OP_FSQRT_S , OP_FSQRT_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b1, 1'b0, fpnew_pkg::SQRT    };
    OP_FSGNJ_S               : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJN_S              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJX_S              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FMIN_S  , OP_FMIN_D   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::MINMAX  };
    OP_FMAX_S  , OP_FMAX_D   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::MINMAX  };
    OP_FCVT_W_S              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_WU_S             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FEQ_S   , OP_FEQ_D    : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FLT_S   , OP_FLT_D    : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FLE_S   , OP_FLE_D    : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FCLASS_S, OP_FCLASS_D : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CLASSIFY};
    OP_FCVT_S_W              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_S_WU             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    OP_FSGNJ_D               : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJN_D              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJX_D              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FCVT_S_D              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2F     };
    OP_FCVT_D_S              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2F     };
    OP_FCVT_W_D              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_WU_D             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FCVT_D_W              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_D_WU             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    OP_FCVT_L_D              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_LU_D             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FCVT_D_L              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_D_LU             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    OP_FCVT_L_S              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_LU_S             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FCVT_S_L              : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_S_LU             : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    default                  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::FMADD   };
  endcase // case (i_op)

  case (i_pipe_ctrl.op)
    OP_FMADD_S     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FMSUB_S     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FNMSUB_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FNMADD_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FADD_S      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FSUB_S      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FMUL_S      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FDIV_S      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FSQRT_S     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FSGNJ_S     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FSGNJN_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FSGNJX_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FMIN_S      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FMAX_S      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FMADD_D     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FMSUB_D     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FNMSUB_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FNMADD_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FADD_D      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FSUB_D      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FMUL_D      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FDIV_D      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FSQRT_D     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FSGNJ_D     : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FSGNJN_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FSGNJX_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FMIN_D      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FMAX_D      : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FCVT_W_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_WU_S   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FEQ_S       : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FLT_S       : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FLE_S       : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCLASS_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FEQ_D       : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FLT_D       : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FLE_D       : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FCLASS_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FCVT_S_W    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_WU   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_D_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP32};
    OP_FCVT_W_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_WU_D   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_D_W    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP32};
    OP_FCVT_D_WU   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP32};
    OP_FCVT_L_D    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_LU_D   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_D_L    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FCVT_D_LU   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FCVT_L_S    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_LU_S   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_L    : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_LU   : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    default        : {w_cvt_valid, w_out_fp, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, 1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
  endcase // case (i_pipe_ctrl.op)

end // always_comb

assign w_commit_flush = commit_if.is_flushed_commit();
assign w_in_br_flush  = scariv_pkg::is_br_flush_target(i_cmt_id, i_grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & i_valid;
assign w_in_flush     = w_commit_flush | w_in_br_flush;

assign w_fma32_in_valid     = i_valid & ~w_in_flush & w_fma_valid     & (i_pipe_ctrl.size == SIZE_W);
assign w_noncomp32_in_valid = i_valid & ~w_in_flush & w_noncomp_valid & (i_pipe_ctrl.size == SIZE_W);

logic [ 2: 0][riscv_fpu_pkg::FLEN_W-1: 0] w_fpnew_rs;
generate if (riscv_fpu_pkg::FLEN_W == 64) begin
  assign w_fpnew_rs[0] = (w_fpnew_op == fpnew_pkg::ADD)                 ? 'h0   :
                         (w_fpnew_op == fpnew_pkg::DIV) & (i_pipe_ctrl.size == SIZE_W) & ~&i_rs1[63:32] ? 64'hffffffff7fc00000 :
                         i_rs1;
  assign w_fpnew_rs[1] = (w_fpnew_op == fpnew_pkg::SQRT) ? ((i_pipe_ctrl.size == SIZE_W) & ~&i_rs1[63:32] ? 64'hffffffff7fc00000 : i_rs1) :
                         (w_fpnew_op == fpnew_pkg::ADD ) ? i_rs1 :
                         (w_fpnew_op == fpnew_pkg::DIV ) & (i_pipe_ctrl.size == SIZE_W) & ~&i_rs2[63:32] ? 64'hffffffff7fc00000 :
                         i_rs2;
  assign w_fpnew_rs[2] = (w_fpnew_op == fpnew_pkg::ADD)  ? i_rs2 : i_rs3;
end else begin
  assign w_fpnew_rs[0] = (w_fpnew_op == fpnew_pkg::ADD)                 ? 'h0   :
                         i_rs1;
  assign w_fpnew_rs[1] = (w_fpnew_op == fpnew_pkg::SQRT) ? i_rs1 :
                         (w_fpnew_op == fpnew_pkg::ADD ) ? i_rs1 :
                         (w_fpnew_op == fpnew_pkg::DIV ) & i_rs2;
  assign w_fpnew_rs[2] = (w_fpnew_op == fpnew_pkg::ADD)  ? i_rs2 : i_rs3;
end endgenerate // else: !if(riscv_fpu_pkg::FLEN_W == 64)

// --------------
// FPU Pipeline
// --------------
fpnew_top
  #(
    // FPU configuration
    .Features       (scariv_fpu_pkg::SCARIV_FPNEW_FEATURE),
    .Implementation (scariv_fpu_pkg::SCARIV_FPNEW_IMPL),
    .TagType        (aux_fpnew_t)
    )
u_fpnew_top
  (
   .clk_i  (i_clk),
   .rst_ni (i_reset_n),
   // Input signals
   .operands_i    (w_fpnew_rs     ),
   .rnd_mode_i    (fpnew_pkg::roundmode_e'(i_rnd_mode)     ),
   .op_i          (w_fpnew_op     ),
   .op_mod_i      (w_fpnew_op_mod ),
   .src_fmt_i     (w_src_fp_fmt   ),
   .dst_fmt_i     (w_dst_fp_fmt   ),
   .int_fmt_i     (w_int_fmt      ),
   .vectorial_op_i(1'b0           ),
   .tag_i         (w_aux_fpnew_in ),
   .simd_mask_i   (1'b0           ),
   // Input Handshake
   .in_valid_i (i_valid & ~w_in_flush),
   .in_ready_o ( ),
   .flush_i    (w_commit_flush),
   // Output signals
   .result_o (w_result        ),
   .status_o (w_fpnew_fflags  ),
   .tag_o    (w_aux_fpnew_out ),
   // Output handshake
   .out_valid_o (w_fpnew_out_valid),
   .out_ready_i (1'b1   ),
   // Indication of valid data in flight
   .busy_o ()
   );

assign o_busy = w_fdiv_valid | r_longfpu_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_valid     <= 1'b0;
    o_result    <= 'h0;
    o_fflags    <= 'h0;
    o_cmt_id    <= 'h0;
    o_grp_id    <= 'h0;
    o_rnid      <= 'h0;
    o_frm_invalid <= 1'b0;
    o_reg_type  <= scariv_pkg::FPR;
  end else begin
    o_valid <= w_fpnew_out_valid & ~w_commit_flush &
               (w_aux_fpnew_out.op inside {fpnew_pkg::DIV, fpnew_pkg::SQRT} ? ~w_longfpu_age_next.dead : ~w_age_fifo_last_dead);
    o_fflags <= {w_fpnew_fflags.NV,
                 w_fpnew_fflags.DZ,
                 w_fpnew_fflags.OF,
                 w_fpnew_fflags.UF,
                 w_fpnew_fflags.NX};

    o_result      <= w_aux_fpnew_out.output_is_int32 ? {{32{w_result[31]}}, w_result[31: 0]} : w_result;
    o_cmt_id      <= w_aux_fpnew_out.op inside {fpnew_pkg::DIV,fpnew_pkg::SQRT} ? r_longfpu_age.cmt_id : r_age_fifo[scariv_conf_pkg::FPNEW_LATENCY-1].cmt_id;
    o_grp_id      <= w_aux_fpnew_out.op inside {fpnew_pkg::DIV,fpnew_pkg::SQRT} ? r_longfpu_age.grp_id : r_age_fifo[scariv_conf_pkg::FPNEW_LATENCY-1].grp_id;
    o_rnid        <= w_aux_fpnew_out.rnid;
    o_frm_invalid <= w_aux_fpnew_out.frm_invalid;
    o_reg_type    <= w_aux_fpnew_out.reg_type;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

// fpnew_fma
//   #(
//     .FpFormat   (fpnew_pkg::FP32),
//     .NumPipeRegs(scariv_conf_pkg::FPNEW_LATENCY),
//     .PipeConfig (fpnew_pkg::DISTRIBUTED),
//     .TagType    (aux_fpnew_t),
//     .AuxType    (logic)
//     )
// fma32
// (
//  .clk_i  (i_clk    ),
//  .rst_ni (i_reset_n),
//  // Input signals
//  .operands_i      (w_fma32_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
//  .is_boxed_i      (w_fma32_boxed    ),  // input logic [2:0]                 // 3 operands
//  .rnd_mode_i      (i_rnd_mode       ),  // input fpnew_pkg::roundmode_e
//  .op_i            (w_fpnew_op       ),  // input fpnew_pkg::operation_e
//  .op_mod_i        (w_fpnew_op_mod   ),  // input logic
//  .tag_i           (w_aux_fpnew_in   ),  // input TagType
//  .aux_i           (                 ),  // input AuxType
//  // Input Handshake
//  .in_valid_i      (w_fma32_in_valid ),  // input  logic
//  .in_ready_o      (w_fma32_ready    ),  // output logic
//  .flush_i         (w_commit_flush          ),  // input  logic
//  // Output signals
//  .result_o        (w_fma32_result   ),  // output logic [WIDTH-1:0]
//  .status_o        (w_fma32_fflags   ),  // output fpnew_pkg::status_t
//  .extension_bit_o (                 ),  // output logic
//  .tag_o           (w_fma32_aux      ),  // output TagType
//  .aux_o           (                 ),  // output AuxType
//  // Output handshake
//  .out_valid_o     (w_fma32_out_valid),  // output logic
//  .out_ready_i     (1'b1             ),  // input  logic
//  // Indication of valid data in flight
//  .busy_o          (                 )   // output logic
//  );
//
// assign w_fma32_out_fflags = {w_fma32_fflags.NV,
//                             w_fma32_fflags.DZ,
//                             w_fma32_fflags.OF,
//                             w_fma32_fflags.UF,
//                             w_fma32_fflags.NX};
//
//
// fpnew_noncomp #(
//     .FpFormat   (fpnew_pkg::FP32),
//     .NumPipeRegs(scariv_conf_pkg::FPNEW_LATENCY),
//     .PipeConfig (fpnew_pkg::DISTRIBUTED),
//     .TagType    (aux_fpnew_t),
//     .AuxType    (logic)
// ) fpnew_noncomp32 (
//   .clk_i  (i_clk    ),
//   .rst_ni (i_reset_n),
//   .operands_i      ( w_noncomp32_rs         ),
//   .is_boxed_i      ( w_noncomp32_boxed      ),
//   .rnd_mode_i      ( i_pipe_ctrl.op == OP_FEQ  ? fpnew_pkg::RDN :
//                      ((i_pipe_ctrl.op == OP_FLT) | (i_pipe_ctrl.op == OP_FMAX))  ? fpnew_pkg::RTZ :
//                      /* ((i_pipe_ctrl.op == OP_FLE) | (i_pipe_ctrl.op == OP_FMIN))  ? */ fpnew_pkg::RNE),
//   .op_i            ( w_fpnew_op             ),
//   .op_mod_i        ( w_fpnew_op_mod         ),
//   .tag_i           ( w_aux_fpnew_in          ),
//   .aux_i           (                        ), // Remember whether operation was vectorial
//   .in_valid_i      ( w_noncomp32_in_valid   ),
//   .in_ready_o      (                        ),
//   .flush_i         ( w_commit_flush         ),
//   .result_o        ( w_noncomp32_result     ),
//   .status_o        ( w_noncomp32_status     ),
//   .extension_bit_o (                        ),
//   .class_mask_o    ( w_noncomp32_class_mask ),
//   .is_class_o      (                        ),
//   .tag_o           ( w_noncomp32_aux        ),
//   .aux_o           (                        ),
//   .out_valid_o     ( w_noncomp32_out_valid  ),
//   .out_ready_i     ( 1'b1                   ),
//   .busy_o          (                        )
// );
//
// assign w_noncomp32_out_fflags = {w_noncomp32_status.NV,
//                                 w_noncomp32_status.DZ,
//                                 w_noncomp32_status.OF,
//                                 w_noncomp32_status.UF,
//                                 w_noncomp32_status.NX};
//
//
//
// logic w_cvt_in_valid;
// logic [ 2: 0] [63: 0] w_multifmt_rs;
// logic [ 4: 0] [ 2: 0] w_multifmt_boxed;
// logic                 w_cast_out_valid;
// logic [63: 0]         w_cast_result;
// fpnew_pkg::status_t   w_cast_status;
//
// assign w_cvt_in_valid = i_valid & ~w_in_flush & w_cvt_valid;
// assign w_multifmt_rs[0] = /* w_src_fp_fmt == fpnew_pkg::FP32 ? {{32{1'b1}}, i_rs1[31: 0]} : */i_rs1;
// assign w_multifmt_rs[1] = /* w_src_fp_fmt == fpnew_pkg::FP32 ? {{32{1'b1}}, i_rs2[31: 0]} : */i_rs2;
// assign w_multifmt_rs[2] = /* w_src_fp_fmt == fpnew_pkg::FP32 ? {{32{1'b1}}, i_rs3[31: 0]} : */i_rs3;
// assign w_multifmt_boxed[0] = w_src_fp_fmt == fpnew_pkg::FP32 ? {&i_rs3[63:32], &i_rs2[63:32], &i_rs1[63:32]} : 3'b111;
// assign w_multifmt_boxed[1] = w_src_fp_fmt == fpnew_pkg::FP32 ? {&i_rs3[63:32], &i_rs2[63:32], &i_rs1[63:32]} : 3'b111;
// assign w_multifmt_boxed[2] = w_src_fp_fmt == fpnew_pkg::FP32 ? {&i_rs3[63:32], &i_rs2[63:32], &i_rs1[63:32]} : 3'b111;
// assign w_multifmt_boxed[3] = w_src_fp_fmt == fpnew_pkg::FP32 ? {&i_rs3[63:32], &i_rs2[63:32], &i_rs1[63:32]} : 3'b111;
// assign w_multifmt_boxed[4] = w_src_fp_fmt == fpnew_pkg::FP32 ? {&i_rs3[63:32], &i_rs2[63:32], &i_rs1[63:32]} : 3'b111;
//
//
// fpnew_opgroup_multifmt_slice /* #(
//   .OpGroup       ( OpGroup          ),
//   .Width         ( Width            ),
//   .FpFmtConfig   ( FpFmtMask        ),
//   .IntFmtConfig  ( IntFmtMask       ),
//   .EnableVectors ( EnableVectors    ),
//   .NumPipeRegs   ( REG              ),
//   .PipeConfig    ( PipeConfig       ),
//   .TagType       ( TagType          )
// ) */
//   #(
//     .NumPipeRegs(scariv_conf_pkg::FPNEW_LATENCY),
//     .PipeConfig (fpnew_pkg::DISTRIBUTED),
//     .TagType    (aux_fpnew_t)
//     ) fpnew_cvt (
//   .clk_i           ( i_clk     ),
//   .rst_ni          ( i_reset_n ),
//   .operands_i      ( w_multifmt_rs    ),
//   .is_boxed_i      ( w_multifmt_boxed ),
//   .rnd_mode_i      ( i_rnd_mode       ),
//   .op_i            ( w_fpnew_op       ),
//   .op_mod_i        ( w_fpnew_op_mod   ),
//   .src_fmt_i       ( w_src_fp_fmt     ),
//   .dst_fmt_i       ( w_dst_fp_fmt     ),
//   .int_fmt_i       ( w_int_fmt        ),
//   .vectorial_op_i  (  ),
//   .tag_i           ( w_aux_fpnew_in   ),
//   .in_valid_i      ( w_cvt_in_valid  ),
//   .in_ready_o      (                 ),
//   .flush_i         ( w_commit_flush  ),
//   .result_o        ( w_cast_result   ),
//   .status_o        ( w_cast_status   ),
//   .extension_bit_o (  ),
//   .tag_o           ( w_cast_aux       ),
//   .out_valid_o     ( w_cast_out_valid ),
//   .out_ready_i     ( 1'b1 ),
//   .busy_o          (  )
// );
//
// assign w_cast_out_fflags = {w_cast_status.NV,
//                             w_cast_status.DZ,
//                             w_cast_status.OF,
//                             w_cast_status.UF,
//                             w_cast_status.NX};
//
//
// logic                 w_fdiv_in_valid;
// logic                 w_fdiv_ready;
// logic                 w_fdiv_out_ready;
// assign w_fdiv_in_valid = i_valid & ~w_in_flush & w_fdiv_valid;
//
// localparam FpFmtConfig = riscv_fpu_pkg::FLEN_W == 32 ? 5'b10000 : 5'b11000;
//
// fpnew_divsqrt_multi
//   #(
//     .FpFmtConfig (FpFmtConfig      ),
//     .NumPipeRegs (32/2             ),
//     .PipeConfig  (fpnew_pkg::DISTRIBUTED),
//     .TagType     (aux_fpnew_t      ),
//     .AuxType     (logic            )
//     )
// fdiv
// (
//  .clk_i  (i_clk    ),
//  .rst_ni (i_reset_n),
//  // Input signals
//  .operands_i      (w_fdiv_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
//  .is_boxed_i      (w_fdiv_boxed    ),  // input logic [2:0]                 // 3 operands
//  .rnd_mode_i      (i_rnd_mode        ),  // input fpnew_pkg::roundmode_e
//  .dst_fmt_i       (i_pipe_ctrl.size == SIZE_W ? fpnew_pkg::FP32 : fpnew_pkg::FP64 ),
//  .op_i            (w_fpnew_op        ),  // input fpnew_pkg::operation_e
//  .tag_i           (w_aux_fpnew_in    ),  // input TagType
//  .aux_i           (                  ),  // input AuxType
//  // Input Handshake
//  .in_valid_i      (w_fdiv_in_valid ),  // input  logic
//  .in_ready_o      (w_fdiv_ready    ),  // output logic
//  .flush_i         (w_commit_flush  ),  // input  logic
//  // Output signals
//  .result_o        (w_fdiv_result   ),  // output logic [WIDTH-1:0]
//  .status_o        (w_fdiv_out_fflags),  // output fpnew_pkg::status_t
//  .extension_bit_o (                  ),  // output logic
//  .tag_o           (w_fdiv_aux      ),  // output TagType
//  .aux_o           (                  ),  // output AuxType
//  // Output handshake
//  .out_valid_o     (w_fdiv_out_valid),  // output logic
//  .out_ready_i     (w_fdiv_out_ready),  // input  logic
//  // Indication of valid data in flight
//  .busy_o          (                  )   // output logic
//  );
//
//
// generate if (riscv_fpu_pkg::FLEN_W == 64) begin : fma64
//   logic [2:0][63: 0]                      w_fma64_rs;
//   logic [2: 0]                            w_fma64_boxed;
//   logic [63: 0]                           w_fma64_result;
//   fpnew_pkg::status_t                     w_fma64_fflags;
//   logic [ 4: 0]                           w_fma64_out_fflags;
//   logic                                   w_fma64_out_valid;
//   logic                                   w_fma64_in_valid;
//   scariv_pkg::cmt_id_t                    w_fma64_cmt_id;
//   scariv_pkg::grp_id_t                    w_fma64_grp_id;
//   aux_fpnew_t                             w_fma64_aux;
//
//   logic                                   w_noncomp64_in_valid;
//   logic                                   w_noncomp64_out_valid;
//   logic [63: 0]                           w_noncomp64_result;
//   fpnew_pkg::status_t                     w_noncomp64_status;
//   fpnew_pkg::classmask_e                  w_noncomp64_class_mask;
//   logic [ 4: 0]                           w_noncomp64_out_fflags;
//   scariv_pkg::cmt_id_t                    w_noncomp64_cmt_id;
//   scariv_pkg::grp_id_t                    w_noncomp64_grp_id;
//   aux_fpnew_t                             w_noncomp64_aux;
//
//   assign w_fma64_rs[0] = (w_fpnew_op == fpnew_pkg::ADD) ? 'h0   : i_rs1;
//   assign w_fma64_rs[1] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs1 : i_rs2;
//   assign w_fma64_rs[2] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs2 : i_rs3;
//   assign w_fma64_boxed[2:0] = 3'b111;
//
//   assign w_fma64_in_valid     = i_valid & ~w_in_flush & w_fma_valid     & (i_pipe_ctrl.size == SIZE_DW);
//   assign w_noncomp64_in_valid = i_valid & ~w_in_flush & w_noncomp_valid & (i_pipe_ctrl.size == SIZE_DW);
//
//   fpnew_fma
//     #(
//       .FpFormat   (fpnew_pkg::FP64),
//       .NumPipeRegs(scariv_conf_pkg::FPNEW_LATENCY),
//       .PipeConfig (fpnew_pkg::DISTRIBUTED),
//       .TagType    (aux_fpnew_t),
//       .AuxType    (logic)
//       )
//   fpnew_64
//   (
//    .clk_i  (i_clk    ),
//    .rst_ni (i_reset_n),
//    // Input signals
//    .operands_i      (w_fma64_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
//    .is_boxed_i      (w_fma64_boxed    ),  // input logic [2:0]                 // 3 operands
//    .rnd_mode_i      (i_rnd_mode       ),  // input fpnew_pkg::roundmode_e
//    .op_i            (w_fpnew_op       ),  // input fpnew_pkg::operation_e
//    .op_mod_i        (w_fpnew_op_mod   ),  // input logic
//    .tag_i           (w_aux_fpnew_in    ),  // input TagType
//    .aux_i           (w_aux_fpnew_in   ),  // input AuxType
//    // Input Handshake
//    .in_valid_i      (w_fma64_in_valid ),  // input  logic
//    .in_ready_o      (w_fma64_ready    ),  // output logic
//    .flush_i         (w_commit_flush   ),  // input  logic
//    // Output signals
//    .result_o        (w_fma64_result   ),  // output logic [WIDTH-1:0]
//    .status_o        (w_fma64_fflags   ),  // output fpnew_pkg::status_t
//    .extension_bit_o (                 ),  // output logic
//    .tag_o           (w_fma64_aux      ),  // output TagType
//    .aux_o           (                 ),  // output AuxType
//    // Output handshake
//    .out_valid_o     (w_fma64_out_valid),  // output logic
//    .out_ready_i     (1'b1             ),  // input  logic
//    // Indication of valid data in flight
//    .busy_o          (                 )   // output logic
//    );
//
//   assign w_fma64_out_fflags = {w_fma64_fflags.NV,
//                                w_fma64_fflags.DZ,
//                                w_fma64_fflags.OF,
//                                w_fma64_fflags.UF,
//                                w_fma64_fflags.NX};
//
//
//   logic [ 1: 0][63: 0]                    w_noncomp64_rs;
//   logic [ 1: 0]                           w_noncomp64_boxed;
//   assign w_noncomp64_rs[0] = i_rs1;
//   assign w_noncomp64_rs[1] = i_rs2;
//   assign w_noncomp64_boxed = 2'b11;
//
//   fpnew_noncomp #(
//       .FpFormat   (fpnew_pkg::FP64),
//       .NumPipeRegs(scariv_conf_pkg::FPNEW_LATENCY),
//       .PipeConfig (fpnew_pkg::DISTRIBUTED),
//       .TagType    (aux_fpnew_t),
//       .AuxType    (logic)
//   ) fpnew_noncomp64 (
//     .clk_i  (i_clk    ),
//     .rst_ni (i_reset_n),
//     .operands_i      ( w_noncomp64_rs         ),
//     .is_boxed_i      ( w_noncomp64_boxed      ),
//     .rnd_mode_i      ( i_pipe_ctrl.op == OP_FEQ  ? fpnew_pkg::RDN :
//                        ((i_pipe_ctrl.op == OP_FLT) | (i_pipe_ctrl.op == OP_FMAX))  ? fpnew_pkg::RTZ :
//                        /* ((i_pipe_ctrl.op == OP_FLE) | (i_pipe_ctrl.op == OP_FMIN))  ? */ fpnew_pkg::RNE),
//     .op_i            ( w_fpnew_op             ),
//     .op_mod_i        ( w_fpnew_op_mod         ),
//     .tag_i           ( w_aux_fpnew_in          ),
//     .aux_i           (                        ), // Remember whether operation was vectorial
//     .in_valid_i      ( w_noncomp64_in_valid   ),
//     .in_ready_o      (                        ),
//     .flush_i         ( w_commit_flush         ),
//     .result_o        ( w_noncomp64_result     ),
//     .status_o        ( w_noncomp64_status     ),
//     .extension_bit_o (                        ),
//     .class_mask_o    ( w_noncomp64_class_mask ),
//     .is_class_o      (                        ),
//     .tag_o           ( w_noncomp64_aux        ),
//     .aux_o           (    ),
//     .out_valid_o     ( w_noncomp64_out_valid  ),
//     .out_ready_i     ( 1'b1                   ),
//     .busy_o          (                        )
//   );
//
//   assign w_noncomp64_out_fflags = {w_noncomp64_status.NV,
//                                    w_noncomp64_status.DZ,
//                                    w_noncomp64_status.OF,
//                                    w_noncomp64_status.UF,
//                                    w_noncomp64_status.NX};
//
//   always_ff @ (posedge i_clk, negedge i_reset_n) begin
//     if (!i_reset_n) begin
//       o_valid     <= 1'b0;
//       o_result    <= 'h0;
//       o_fflags    <= 'h0;
//       o_cmt_id    <= 'h0;
//       o_grp_id    <= 'h0;
//       o_rnid      <= 'h0;
//       o_frm_invalid <= 1'b0;
//       o_reg_type  <= scariv_pkg::FPR;
//     end else begin
//       o_valid  <= w_fma32_out_valid |
//                   w_noncomp32_out_valid |
//                   w_fma64_out_valid |
//                   w_noncomp64_out_valid |
//                   w_cast_out_valid |
//                   w_fdiv_out_valid;
//       if (w_fma32_out_valid) begin
//         o_result      <= {{32{1'b1}}, w_fma32_result};
//         o_fflags      <= w_fma32_out_fflags;
//         o_cmt_id      <= w_fma32_aux.cmt_id;
//         o_grp_id      <= w_fma32_aux.grp_id;
//         o_rnid        <= w_fma32_aux.rnid;
//         o_frm_invalid <= w_fma32_aux.frm_invalid;
//         o_reg_type    <= w_fma32_aux.reg_type;
//       end else if (w_noncomp32_out_valid) begin
//         if (w_noncomp32_aux.op == fpnew_pkg::CLASSIFY) begin
//           o_result <= w_noncomp32_class_mask;
//         end else begin
//           o_result <= {{32{(w_noncomp32_aux.op == fpnew_pkg::MINMAX)}}, w_noncomp32_result};
//         end
//         o_fflags      <= w_noncomp32_out_fflags;
//         o_cmt_id      <= w_noncomp32_aux.cmt_id;
//         o_grp_id      <= w_noncomp32_aux.grp_id;
//         o_rnid        <= w_noncomp32_aux.rnid;
//         o_frm_invalid <= w_noncomp32_aux.frm_invalid;
//         o_reg_type    <= w_noncomp32_aux.reg_type;
//       end else if (w_fma64_out_valid) begin // if (w_noncomp32_out_valid)
//         o_result      <= w_fma64_result;
//         o_fflags      <= w_fma64_out_fflags;
//         o_cmt_id      <= w_fma64_aux.cmt_id;
//         o_grp_id      <= w_fma64_aux.grp_id;
//         o_rnid        <= w_fma64_aux.rnid;
//         o_frm_invalid <= w_fma64_aux.frm_invalid;
//         o_reg_type    <= w_fma64_aux.reg_type;
//       end else if (w_noncomp64_out_valid) begin
//         if (w_noncomp64_aux.op == fpnew_pkg::CLASSIFY) begin
//           o_result <= w_noncomp64_class_mask;
//         end else begin
//           o_result <= w_noncomp64_result;
//         end
//         o_fflags      <= w_noncomp64_out_fflags;
//         o_cmt_id      <= w_noncomp64_aux.cmt_id;
//         o_grp_id      <= w_noncomp64_aux.grp_id;
//         o_rnid        <= w_noncomp64_aux.rnid;
//         o_frm_invalid <= w_noncomp64_aux.frm_invalid;
//         o_reg_type    <= w_noncomp64_aux.reg_type;
//       end else if (w_cast_out_valid) begin // if (w_noncomp64_out_valid)
//         o_result      <= w_cast_aux.output_is_fp32 ? {{32{1'b1}}, w_cast_result[31: 0]} : w_cast_result;
//         o_fflags      <= w_cast_out_fflags;
//         o_cmt_id      <= w_cast_aux.cmt_id;
//         o_grp_id      <= w_cast_aux.grp_id;
//         o_rnid        <= w_cast_aux.rnid;
//         o_frm_invalid <= w_cast_aux.frm_invalid;
//         o_reg_type    <= w_cast_aux.reg_type;
//       end else if (w_fdiv_out_valid) begin
//         o_result      <= {{32{1'b1}}, w_fdiv_result};
//         o_fflags      <= w_fdiv_out_fflags;
//         o_cmt_id      <= w_fdiv_aux.cmt_id;
//         o_grp_id      <= w_fdiv_aux.grp_id;
//         o_rnid        <= w_fdiv_aux.rnid;
//         o_frm_invalid <= w_fdiv_aux.frm_invalid;
//         o_reg_type    <= w_fdiv_aux.reg_type;
//       end else begin
//         o_result      <= 'h0;
//         o_fflags      <= 'h0;
//         o_cmt_id      <= 'h0;
//         o_grp_id      <= 'h0;
//         o_rnid        <= 'h0;
//         o_frm_invalid <= 1'b0;
//         o_reg_type    <= scariv_pkg::FPR;
//       end
//     end
//   end // always_comb
//
//   assign w_fdiv_out_ready = ~(w_fma32_out_valid     |
//                               w_noncomp32_out_valid |
//                               w_fma64_out_valid     |
//                               w_noncomp64_out_valid |
//                               w_cast_out_valid      );
//
//
// end else if (riscv_fpu_pkg::FLEN_W == 32) begin : block_32 // block: fma64
//   always_ff @ (posedge i_clk, negedge i_reset_n) begin
//     if (!i_reset_n) begin
//       o_valid     <= 1'b0;
//       o_result    <= 'h0;
//       o_fflags    <= 'h0;
//       o_cmt_id    <= 'h0;
//       o_grp_id    <= 'h0;
//       o_rnid      <= 'h0;
//       o_frm_invalid <= 1'b0;
//       o_reg_type  <= scariv_pkg::FPR;
//     end else begin
//       o_valid  <= w_fma32_out_valid |
//                   w_noncomp32_out_valid |
//                   w_cast_out_valid |
//                   w_fdiv_out_valid;
//       if (w_fma32_out_valid) begin
//         o_result      <= w_fma32_result;
//         o_fflags      <= w_fma32_out_fflags;
//         o_cmt_id      <= w_fma32_aux.cmt_id;
//         o_grp_id      <= w_fma32_aux.grp_id;
//         o_rnid        <= w_fma32_aux.rnid;
//         o_frm_invalid <= w_fma32_aux.frm_invalid;
//         o_reg_type    <= w_fma32_aux.reg_type;
//       end else if (w_noncomp32_out_valid) begin
//         if (w_noncomp32_aux.op == fpnew_pkg::CLASSIFY) begin
//           o_result <= w_noncomp32_class_mask;
//         end else begin
//           o_result <= w_noncomp32_result;
//         end
//         o_fflags      <= w_noncomp32_out_fflags;
//         o_cmt_id      <= w_noncomp32_aux.cmt_id;
//         o_grp_id      <= w_noncomp32_aux.grp_id;
//         o_rnid        <= w_noncomp32_aux.rnid;
//         o_frm_invalid <= w_noncomp32_aux.frm_invalid;
//         o_reg_type    <= w_noncomp32_aux.reg_type;
//       end else if (w_cast_out_valid) begin
//         o_result      <= w_cast_result;
//         o_fflags      <= w_cast_out_fflags;
//         o_cmt_id      <= w_cast_aux.cmt_id;
//         o_grp_id      <= w_cast_aux.grp_id;
//         o_rnid        <= w_cast_aux.rnid;
//         o_frm_invalid <= w_cast_aux.frm_invalid;
//         o_reg_type    <= w_cast_aux.reg_type;
//       end else if (w_fdiv_out_valid) begin
//         if (scariv_pkg::ALEN_W == 64) begin
//           o_result      <= {{32{1'b1}}, w_fdiv_result};
//         end else begin
//           o_result      <= w_fdiv_result;
//         end
//         o_fflags      <= w_fdiv_out_fflags;
//         o_cmt_id      <= w_fdiv_aux.cmt_id;
//         o_grp_id      <= w_fdiv_aux.grp_id;
//         o_rnid        <= w_fdiv_aux.rnid;
//         o_frm_invalid <= w_fdiv_aux.frm_invalid;
//         o_reg_type    <= w_fdiv_aux.reg_type;
//       end else begin
//         o_result      <= 'h0;
//         o_fflags      <= 'h0;
//         o_cmt_id      <= 'h0;
//         o_grp_id      <= 'h0;
//         o_rnid        <= 'h0;
//         o_frm_invalid <= 1'b0;
//         o_reg_type    <= scariv_pkg::FPR;
//       end // else: !if(w_fdiv_out_valid)
//     end
//   end // always_comb
//
//   assign w_fdiv_out_ready = ~(w_fma32_out_valid     |
//                               w_noncomp32_out_valid |
//                               w_cast_out_valid      );
//
// end // block: block_32
// endgenerate

endmodule // scariv_fpnew_wrapper
