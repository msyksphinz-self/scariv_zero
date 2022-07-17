module msrh_fpnew_wrapper
  import decoder_fpu_ctrl_pkg::*;
  import msrh_fpu_pkg::*;
#(
  parameter SCHED_ENTRY_SIZE = 8
  )
(
   input logic               i_clk,
   input logic               i_reset_n,

   input logic               i_valid,
   output logic              o_ready,
   input pipe_ctrl_t         i_pipe_ctrl,
   input logic [msrh_conf_pkg::RV_FPU_ENTRY_SIZE-1: 0] i_sched_index,
   input msrh_pkg::rnid_t                              i_rnid,
   input msrh_pkg::reg_t                               i_reg_type,
   input logic [ 2: 0]       i_rnd_mode,

   input msrh_pkg::alen_t    i_rs1,
   input msrh_pkg::alen_t    i_rs2,
   input msrh_pkg::alen_t    i_rs3,

   output logic              o_valid,
   output msrh_pkg::alen_t   o_result,
   output logic [ 4: 0]      o_fflags,
   output logic [msrh_conf_pkg::RV_FPU_ENTRY_SIZE-1: 0] o_sched_index,
   output msrh_pkg::rnid_t                              o_rnid,
   output msrh_pkg::reg_t                               o_reg_type
   );

logic     w_fma64_ready;
logic     w_fma32_ready;

assign o_ready = w_fma64_ready & w_fma32_ready;

typedef struct packed {
  fpnew_pkg::operation_e                        op;
  logic                                         op_mod;
  logic [msrh_conf_pkg::RV_FPU_ENTRY_SIZE-1: 0] sched_index;
  msrh_pkg::reg_t  reg_type;
  msrh_pkg::rnid_t rnid;
} aux_fpnew_t;

logic                                    w_fma32_in_valid;
logic                                    w_noncomp32_in_valid;

logic                                    w_fma_valid;
logic                                    w_noncomp_valid;
logic                                    w_fdiv_valid;

fpnew_pkg::operation_e                   w_fpnew_op;
logic                                    w_fpnew_op_mod;

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
logic                                    w_cvt_valid;
logic [ 4: 0]                            w_cast_out_fflags;
aux_fpnew_t                              w_cast_aux;

logic [ 1: 0][riscv_pkg::FLEN_W-1: 0]    w_fdiv_rs;
logic [ 1: 0]                            w_fdiv_boxed;
logic                                    w_fdiv_out_valid;
logic [riscv_pkg::FLEN_W-1: 0]           w_fdiv_result;
fpnew_pkg::status_t                      w_fdiv_status;
fpnew_pkg::classmask_e                   w_fdiv_class_mask;
logic [ 4: 0]                            w_fdiv_out_fflags;
aux_fpnew_t                              w_fdiv_aux;

aux_fpnew_t w_aux_fpnew_in;

assign w_aux_fpnew_in.op          = w_fpnew_op;
assign w_aux_fpnew_in.op_mod      = w_fpnew_op_mod;
assign w_aux_fpnew_in.reg_type    = i_reg_type;
assign w_aux_fpnew_in.rnid        = i_rnid;
assign w_aux_fpnew_in.sched_index = i_sched_index;

assign w_fma32_rs[0] = (w_fpnew_op == fpnew_pkg::ADD) ? 'h0          : i_rs1[31: 0];
assign w_fma32_rs[1] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs1[31: 0] : i_rs2[31: 0];
assign w_fma32_rs[2] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs2[31: 0] : i_rs3[31: 0];
assign w_fma32_boxed[2:0] = 3'b111;

assign w_noncomp32_rs[0] = i_rs1[31: 0];
assign w_noncomp32_rs[1] = i_rs2[31: 0];
generate if (riscv_pkg::FLEN_W == 64) begin
  assign w_noncomp32_boxed = {&i_rs2[63:32], &i_rs1[63:32]};
end else begin
  assign w_noncomp32_boxed = 2'b11;
end
endgenerate


generate if (msrh_pkg::ALEN_W == 64) begin
  assign w_fdiv_rs[0] = (i_pipe_ctrl.size == SIZE_W) ? {{32{1'b1}}, i_rs1[31: 0]} : i_rs1;
  assign w_fdiv_rs[1] = (i_pipe_ctrl.size == SIZE_W) ? {{32{1'b1}}, i_rs2[31: 0]} : i_rs2;
end else begin
  assign w_fdiv_rs[0] = i_rs1;
  assign w_fdiv_rs[1] = i_rs2;
end
endgenerate

assign w_fdiv_boxed = 2'b11;

always_comb begin
  case (i_pipe_ctrl.op)
    OP_FMADD     : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::FMADD   };
    OP_FMSUB     : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b1, fpnew_pkg::FMADD   };
    OP_FNMSUB    : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::FNMSUB  };
    OP_FNMADD    : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b1, fpnew_pkg::FNMSUB  };
    OP_FADD      : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::ADD     };
    OP_FSUB      : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b1, fpnew_pkg::ADD     };
    OP_FMUL      : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::MUL     };
    OP_FDIV      : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b1, 1'b0, fpnew_pkg::DIV     };
    OP_FSQRT     : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b1, 1'b0, fpnew_pkg::SQRT    };
    OP_FSGNJ_S   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJN_S  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJX_S  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FMIN      : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::MINMAX  };
    OP_FMAX      : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::MINMAX  };
    OP_FCVT_W_S  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_WU_S : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FEQ       : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FLT       : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FLE       : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FCLASS    : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, 1'b0, fpnew_pkg::CLASSIFY};
    OP_FCVT_S_W  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_S_WU : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    OP_FSGNJ_D   : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJN_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJX_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FCVT_S_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2F     };
    OP_FCVT_D_S  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2F     };
    OP_FCVT_W_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_WU_D : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FCVT_D_W  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_D_WU : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    OP_FCVT_L_D  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_LU_D : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FCVT_D_L  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_D_LU : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    OP_FCVT_L_S  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_LU_S : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::F2I     };
    OP_FCVT_S_L  : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_S_LU : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b1, fpnew_pkg::I2F     };
    default      : {w_fma_valid, w_noncomp_valid, w_fdiv_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, 1'b0, fpnew_pkg::FMADD   };
  endcase // case (i_op)

  case (i_pipe_ctrl.op)
    OP_FCVT_W_S  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_WU_S : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_W  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_WU : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_D  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_D_S  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP32};
    OP_FCVT_W_D  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_WU_D : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_D_W  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP32};
    OP_FCVT_D_WU : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT32, fpnew_pkg::FP64, fpnew_pkg::FP32};
    OP_FCVT_L_D  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_LU_D : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
    OP_FCVT_D_L  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FCVT_D_LU : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP64, fpnew_pkg::FP64};
    OP_FCVT_L_S  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_LU_S : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_L  : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    OP_FCVT_S_LU : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b1, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP32};
    default      : {w_cvt_valid, w_int_fmt, w_dst_fp_fmt, w_src_fp_fmt} = {1'b0, fpnew_pkg::INT64, fpnew_pkg::FP32, fpnew_pkg::FP64};
  endcase // case (i_pipe_ctrl.op)

end // always_comb

assign w_fma32_in_valid     = i_valid & w_fma_valid     & (i_pipe_ctrl.size == SIZE_W);
assign w_noncomp32_in_valid = i_valid & w_noncomp_valid & (i_pipe_ctrl.size == SIZE_W);

fpnew_fma
  #(
    .FpFormat   (fpnew_pkg::FP32),
    .NumPipeRegs(msrh_conf_pkg::FPNEW_LATENCY),
    .PipeConfig (fpnew_pkg::BEFORE),
    .TagType    (aux_fpnew_t),
    .AuxType    (logic)
    )
fma_32
(
 .clk_i  (i_clk    ),
 .rst_ni (i_reset_n),
 // Input signals
 .operands_i      (w_fma32_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
 .is_boxed_i      (w_fma32_boxed    ),  // input logic [2:0]                 // 3 operands
 .rnd_mode_i      (i_rnd_mode       ),  // input fpnew_pkg::roundmode_e
 .op_i            (w_fpnew_op       ),  // input fpnew_pkg::operation_e
 .op_mod_i        (w_fpnew_op_mod   ),  // input logic
 .tag_i           (w_aux_fpnew_in   ),  // input TagType
 .aux_i           (                 ),  // input AuxType
 // Input Handshake
 .in_valid_i      (w_fma32_in_valid ),  // input  logic
 .in_ready_o      (w_fma32_ready    ),  // output logic
 .flush_i         (1'b0             ),  // input  logic
 // Output signals
 .result_o        (w_fma32_result   ),  // output logic [WIDTH-1:0]
 .status_o        (w_fma32_fflags   ),  // output fpnew_pkg::status_t
 .extension_bit_o (                 ),  // output logic
 .tag_o           (w_fma32_aux      ),  // output TagType
 .aux_o           (                 ),  // output AuxType
 // Output handshake
 .out_valid_o     (w_fma32_out_valid),  // output logic
 .out_ready_i     (1'b1             ),  // input  logic
 // Indication of valid data in flight
 .busy_o          (                 )   // output logic
 );

assign w_fma32_out_fflags = {w_fma32_fflags.NV,
                            w_fma32_fflags.DZ,
                            w_fma32_fflags.OF,
                            w_fma32_fflags.UF,
                            w_fma32_fflags.NX};


fpnew_noncomp #(
    .FpFormat   (fpnew_pkg::FP32),
    .NumPipeRegs(msrh_conf_pkg::FPNEW_LATENCY),
    .PipeConfig (fpnew_pkg::BEFORE),
    .TagType    (aux_fpnew_t),
    .AuxType    (logic)
) fpnew_noncomp32 (
  .clk_i  (i_clk    ),
  .rst_ni (i_reset_n),
  .operands_i      ( w_noncomp32_rs         ),
  .is_boxed_i      ( w_noncomp32_boxed      ),
  .rnd_mode_i      ( i_pipe_ctrl.op == OP_FEQ  ? fpnew_pkg::RDN :
                     ((i_pipe_ctrl.op == OP_FLT) | (i_pipe_ctrl.op == OP_FMAX))  ? fpnew_pkg::RTZ :
                     /* ((i_pipe_ctrl.op == OP_FLE) | (i_pipe_ctrl.op == OP_FMIN))  ? */ fpnew_pkg::RNE),
  .op_i            ( w_fpnew_op             ),
  .op_mod_i        ( w_fpnew_op_mod         ),
  .tag_i           ( w_aux_fpnew_in          ),
  .aux_i           (                        ), // Remember whether operation was vectorial
  .in_valid_i      ( w_noncomp32_in_valid   ),
  .in_ready_o      (                        ),
  .flush_i         ( 1'b0                   ),
  .result_o        ( w_noncomp32_result     ),
  .status_o        ( w_noncomp32_status     ),
  .extension_bit_o (                        ),
  .class_mask_o    ( w_noncomp32_class_mask ),
  .is_class_o      (                        ),
  .tag_o           ( w_noncomp32_aux        ),
  .aux_o           (                        ),
  .out_valid_o     ( w_noncomp32_out_valid  ),
  .out_ready_i     ( 1'b1                   ),
  .busy_o          (                        )
);

assign w_noncomp32_out_fflags = {w_noncomp32_status.NV,
                                w_noncomp32_status.DZ,
                                w_noncomp32_status.OF,
                                w_noncomp32_status.UF,
                                w_noncomp32_status.NX};



logic w_cvt_in_valid;
logic [ 2: 0] [63: 0] w_multifmt_rs;
logic [ 4: 0] [ 2: 0] w_multifmt_boxed;
logic                 w_cast_out_valid;
logic [63: 0]         w_cast_result;
fpnew_pkg::status_t   w_cast_status;

assign w_cvt_in_valid = i_valid & w_cvt_valid;
assign w_multifmt_rs[0] = (i_pipe_ctrl.op == OP_FCVT_W_S || i_pipe_ctrl.op == OP_FCVT_WU_S) ? {{32{1'b1}}, i_rs1[31: 0]} : i_rs1;
assign w_multifmt_rs[1] = (i_pipe_ctrl.op == OP_FCVT_W_S || i_pipe_ctrl.op == OP_FCVT_WU_S) ? {{32{1'b1}}, i_rs2[31: 0]} : i_rs2;
assign w_multifmt_rs[2] = (i_pipe_ctrl.op == OP_FCVT_W_S || i_pipe_ctrl.op == OP_FCVT_WU_S) ? {{32{1'b1}}, i_rs3[31: 0]} : i_rs3;
assign w_multifmt_boxed[0] = 3'b111;
assign w_multifmt_boxed[1] = 3'b111;
assign w_multifmt_boxed[2] = 3'b111;
assign w_multifmt_boxed[3] = 3'b111;
assign w_multifmt_boxed[4] = 3'b111;


fpnew_opgroup_multifmt_slice /* #(
  .OpGroup       ( OpGroup          ),
  .Width         ( Width            ),
  .FpFmtConfig   ( FpFmtMask        ),
  .IntFmtConfig  ( IntFmtMask       ),
  .EnableVectors ( EnableVectors    ),
  .NumPipeRegs   ( REG              ),
  .PipeConfig    ( PipeConfig       ),
  .TagType       ( TagType          )
) */
  #(
    .NumPipeRegs(msrh_conf_pkg::FPNEW_LATENCY),
    .PipeConfig (fpnew_pkg::BEFORE),
    .TagType    (aux_fpnew_t)
    ) fpnew_cvt (
  .clk_i           ( i_clk     ),
  .rst_ni          ( i_reset_n ),
  .operands_i      ( w_multifmt_rs    ),
  .is_boxed_i      ( w_multifmt_boxed ),
  .rnd_mode_i      ( i_rnd_mode       ),
  .op_i            ( w_fpnew_op       ),
  .op_mod_i        ( w_fpnew_op_mod   ),
  .src_fmt_i       ( w_src_fp_fmt     ),
  .dst_fmt_i       ( w_dst_fp_fmt     ),
  .int_fmt_i       ( w_int_fmt        ),
  .vectorial_op_i  (  ),
  .tag_i           ( w_aux_fpnew_in   ),
  .in_valid_i      ( w_cvt_in_valid  ),
  .in_ready_o      (                 ),
  .flush_i         ( 1'b0            ),
  .result_o        ( w_cast_result   ),
  .status_o        ( w_cast_status   ),
  .extension_bit_o (  ),
  .tag_o           ( w_cast_aux       ),
  .out_valid_o     ( w_cast_out_valid ),
  .out_ready_i     ( 1'b1 ),
  .busy_o          (  )
);

assign w_cast_out_fflags = {w_cast_status.NV,
                            w_cast_status.DZ,
                            w_cast_status.OF,
                            w_cast_status.UF,
                            w_cast_status.NX};


logic                 w_fdiv_in_valid;
logic                 w_fdiv_ready;
assign w_fdiv_in_valid = i_valid & w_fdiv_valid;

localparam FpFmtConfig = riscv_pkg::FLEN_W == 32 ? 5'b10000 : 5'b11000;

fpnew_divsqrt_multi
  #(
    .FpFmtConfig (FpFmtConfig      ),
    .NumPipeRegs (32/2             ),
    .PipeConfig  (fpnew_pkg::BEFORE),
    .TagType     (aux_fpnew_t      ),
    .AuxType     (logic            )
    )
fdiv
(
 .clk_i  (i_clk    ),
 .rst_ni (i_reset_n),
 // Input signals
 .operands_i      (w_fdiv_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
 .is_boxed_i      (w_fdiv_boxed    ),  // input logic [2:0]                 // 3 operands
 .rnd_mode_i      (i_rnd_mode        ),  // input fpnew_pkg::roundmode_e
 .dst_fmt_i       (i_pipe_ctrl.size == SIZE_W ? fpnew_pkg::FP32 : fpnew_pkg::FP64 ),
 .op_i            (w_fpnew_op        ),  // input fpnew_pkg::operation_e
 .tag_i           (w_aux_fpnew_in    ),  // input TagType
 .aux_i           (                  ),  // input AuxType
 // Input Handshake
 .in_valid_i      (w_fdiv_in_valid ),  // input  logic
 .in_ready_o      (w_fdiv_ready    ),  // output logic
 .flush_i         (1'b0              ),  // input  logic
 // Output signals
 .result_o        (w_fdiv_result   ),  // output logic [WIDTH-1:0]
 .status_o        (w_fdiv_out_fflags),  // output fpnew_pkg::status_t
 .extension_bit_o (                  ),  // output logic
 .tag_o           (w_fdiv_aux      ),  // output TagType
 .aux_o           (                  ),  // output AuxType
 // Output handshake
 .out_valid_o     (w_fdiv_out_valid),  // output logic
 .out_ready_i     (1'b1              ),  // input  logic
 // Indication of valid data in flight
 .busy_o          (                  )   // output logic
 );


generate if (riscv_pkg::FLEN_W == 64) begin : fma64
  logic [2:0][63: 0]                      w_fma64_rs;
  logic [2: 0]                            w_fma64_boxed;
  logic [63: 0]                           w_fma64_result;
  fpnew_pkg::status_t                     w_fma64_fflags;
  logic [ 4: 0]                           w_fma64_out_fflags;
  logic                                   w_fma64_out_valid;
  logic                                   w_fma64_in_valid;
  aux_fpnew_t w_fma64_sched_index;
  aux_fpnew_t                                   w_fma64_aux;

  logic                                   w_noncomp64_in_valid;
  logic                                   w_noncomp64_out_valid;
  logic [63: 0]                           w_noncomp64_result;
  fpnew_pkg::status_t                     w_noncomp64_status;
  fpnew_pkg::classmask_e                  w_noncomp64_class_mask;
  logic [ 4: 0]                           w_noncomp64_out_fflags;
  aux_fpnew_t w_noncomp64_sched_index;
  aux_fpnew_t                                   w_noncomp64_aux;

  assign w_fma64_rs[0] = (w_fpnew_op == fpnew_pkg::ADD) ? 'h0   : i_rs1;
  assign w_fma64_rs[1] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs1 : i_rs2;
  assign w_fma64_rs[2] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs2 : i_rs3;
  assign w_fma64_boxed[2:0] = 3'b111;

  assign w_fma64_in_valid     = i_valid & w_fma_valid     & (i_pipe_ctrl.size == SIZE_DW);
  assign w_noncomp64_in_valid = i_valid & w_noncomp_valid & (i_pipe_ctrl.size == SIZE_DW);

  fpnew_fma
    #(
      .FpFormat   (fpnew_pkg::FP64),
      .NumPipeRegs(msrh_conf_pkg::FPNEW_LATENCY),
      .PipeConfig (fpnew_pkg::BEFORE),
      .TagType    (aux_fpnew_t),
      .AuxType    (logic)
      )
  fpnew_64
  (
   .clk_i  (i_clk    ),
   .rst_ni (i_reset_n),
   // Input signals
   .operands_i      (w_fma64_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
   .is_boxed_i      (w_fma64_boxed    ),  // input logic [2:0]                 // 3 operands
   .rnd_mode_i      (i_rnd_mode       ),  // input fpnew_pkg::roundmode_e
   .op_i            (w_fpnew_op       ),  // input fpnew_pkg::operation_e
   .op_mod_i        (w_fpnew_op_mod   ),  // input logic
   .tag_i           (w_aux_fpnew_in    ),  // input TagType
   .aux_i           (w_aux_fpnew_in   ),  // input AuxType
   // Input Handshake
   .in_valid_i      (w_fma64_in_valid ),  // input  logic
   .in_ready_o      (w_fma64_ready    ),  // output logic
   .flush_i         (1'b0             ),  // input  logic
   // Output signals
   .result_o        (w_fma64_result   ),  // output logic [WIDTH-1:0]
   .status_o        (w_fma64_fflags   ),  // output fpnew_pkg::status_t
   .extension_bit_o (                 ),  // output logic
   .tag_o           (w_fma64_aux      ),  // output TagType
   .aux_o           (                 ),  // output AuxType
   // Output handshake
   .out_valid_o     (w_fma64_out_valid),  // output logic
   .out_ready_i     (1'b1             ),  // input  logic
   // Indication of valid data in flight
   .busy_o          (                 )   // output logic
   );

  assign w_fma64_out_fflags = {w_fma64_fflags.NV,
                               w_fma64_fflags.DZ,
                               w_fma64_fflags.OF,
                               w_fma64_fflags.UF,
                               w_fma64_fflags.NX};


  logic [ 1: 0][63: 0]                    w_noncomp64_rs;
  logic [ 1: 0]                           w_noncomp64_boxed;
  assign w_noncomp64_rs[0] = i_rs1;
  assign w_noncomp64_rs[1] = i_rs2;
  assign w_noncomp64_boxed = 2'b11;

  fpnew_noncomp #(
      .FpFormat   (fpnew_pkg::FP64),
      .NumPipeRegs(msrh_conf_pkg::FPNEW_LATENCY),
      .PipeConfig (fpnew_pkg::BEFORE),
      .TagType    (aux_fpnew_t),
      .AuxType    (logic)
  ) fpnew_noncomp64 (
    .clk_i  (i_clk    ),
    .rst_ni (i_reset_n),
    .operands_i      ( w_noncomp64_rs         ),
    .is_boxed_i      ( w_noncomp64_boxed      ),
    .rnd_mode_i      ( i_pipe_ctrl.op == OP_FEQ  ? fpnew_pkg::RDN :
                       ((i_pipe_ctrl.op == OP_FLT) | (i_pipe_ctrl.op == OP_FMAX))  ? fpnew_pkg::RTZ :
                       /* ((i_pipe_ctrl.op == OP_FLE) | (i_pipe_ctrl.op == OP_FMIN))  ? */ fpnew_pkg::RNE),
    .op_i            ( w_fpnew_op             ),
    .op_mod_i        ( w_fpnew_op_mod         ),
    .tag_i           ( w_aux_fpnew_in          ),
    .aux_i           (                        ), // Remember whether operation was vectorial
    .in_valid_i      ( w_noncomp64_in_valid   ),
    .in_ready_o      (                        ),
    .flush_i         ( 1'b0                   ),
    .result_o        ( w_noncomp64_result     ),
    .status_o        ( w_noncomp64_status     ),
    .extension_bit_o (                        ),
    .class_mask_o    ( w_noncomp64_class_mask ),
    .is_class_o      (                        ),
    .tag_o           ( w_noncomp64_aux        ),
    .aux_o           (    ),
    .out_valid_o     ( w_noncomp64_out_valid  ),
    .out_ready_i     ( 1'b1                   ),
    .busy_o          (                        )
  );

  assign w_noncomp64_out_fflags = {w_noncomp64_status.NV,
                                   w_noncomp64_status.DZ,
                                   w_noncomp64_status.OF,
                                   w_noncomp64_status.UF,
                                   w_noncomp64_status.NX};


  assign o_valid  = w_fma32_out_valid |
                    w_noncomp32_out_valid |
                    w_fma64_out_valid |
                    w_noncomp64_out_valid |
                    w_cast_out_valid |
                    w_fdiv_out_valid;
  always_comb begin
    if (w_fma32_out_valid) begin
      o_result      = {{32{1'b1}}, w_fma32_result};
      o_fflags      = w_fma32_out_fflags;
      o_sched_index = w_fma32_aux.sched_index;
      o_rnid        = w_fma32_aux.rnid;
      o_reg_type    = w_fma32_aux.reg_type;
    end else if (w_noncomp32_out_valid) begin
      if (w_noncomp32_aux.op == fpnew_pkg::CLASSIFY) begin
        o_result = w_noncomp32_class_mask;
      end else begin
        o_result ={{32{(w_noncomp32_aux.op == fpnew_pkg::MINMAX)}}, w_noncomp32_result};
      end
      o_fflags      = w_noncomp32_out_fflags;
      o_sched_index = w_noncomp32_aux.sched_index;
      o_rnid        = w_noncomp32_aux.rnid;
      o_reg_type    = w_noncomp32_aux.reg_type;
    end else if (w_fma64_out_valid) begin // if (w_noncomp32_out_valid)
      o_result      = w_fma64_result;
      o_fflags      = w_fma64_out_fflags;
      o_sched_index = w_fma64_aux.sched_index;
      o_rnid        = w_fma64_aux.rnid;
      o_reg_type    = w_fma64_aux.reg_type;
    end else if (w_noncomp64_out_valid) begin
      if (w_noncomp64_aux.op == fpnew_pkg::CLASSIFY) begin
        o_result = w_noncomp64_class_mask;
      end else begin
        o_result = w_noncomp64_result;
      end
      o_fflags      = w_noncomp64_out_fflags;
      o_sched_index = w_noncomp64_aux.sched_index;
      o_rnid        = w_noncomp64_aux.rnid;
      o_reg_type    = w_noncomp64_aux.reg_type;
    end else if (w_cast_out_valid) begin // if (w_noncomp64_out_valid)
      o_result      = w_cast_result;
      o_fflags      = w_cast_out_fflags;
      o_sched_index = w_cast_aux.sched_index;
      o_rnid        = w_cast_aux.rnid;
      o_reg_type    = w_cast_aux.reg_type;
    end else if (w_fdiv_out_valid) begin
      o_result      = {{32{1'b1}}, w_fdiv_result};
      o_fflags      = w_fdiv_out_fflags;
      o_sched_index = w_fdiv_aux.sched_index;
      o_rnid        = w_fdiv_aux.rnid;
      o_reg_type    = w_fdiv_aux.reg_type;
    end else begin
      o_result      = 'h0;
      o_fflags      = 'h0;
      o_sched_index = 'h0;
      o_rnid        = 'h0;
      o_reg_type    = msrh_pkg::FPR;
    end
  end // always_comb

end else if (riscv_pkg::FLEN_W == 32) begin : block_32 // block: fma64
  assign o_valid  = w_fma32_out_valid |
                    w_noncomp32_out_valid |
                    w_cast_out_valid |
                    w_fdiv_out_valid;

  always_comb begin
    if (w_fma32_out_valid) begin
      o_result      = w_fma32_result;
      o_fflags      = w_fma32_out_fflags;
      o_sched_index = w_fma32_aux.sched_index;
      o_rnid        = w_fma32_aux.rnid;
      o_reg_type    = w_fma32_aux.reg_type;
    end else if (w_noncomp32_out_valid) begin
      if (w_noncomp32_aux.op == fpnew_pkg::CLASSIFY) begin
        o_result = w_noncomp32_class_mask;
      end else begin
        o_result = w_noncomp32_result;
      end
      o_fflags      = w_noncomp32_out_fflags;
      o_sched_index = w_noncomp32_aux.sched_index;
      o_rnid        = w_noncomp32_aux.rnid;
      o_reg_type    = w_noncomp32_aux.reg_type;
    end else if (w_cast_out_valid) begin
      o_result      = w_cast_result;
      o_fflags      = w_cast_out_fflags;
      o_sched_index = w_cast_aux.sched_index;
      o_rnid        = w_cast_aux.rnid;
      o_reg_type    = w_cast_aux.reg_type;
    end else if (w_fdiv_out_valid) begin
      if (msrh_pkg::ALEN_W == 64) begin
        o_result      = {{32{1'b1}}, w_fdiv_result};
      end else begin
        o_result      = w_fdiv_result;
      end
      o_fflags      = w_fdiv_out_fflags;
      o_sched_index = w_fdiv_aux.sched_index;
      o_rnid        = w_fdiv_aux.rnid;
      o_reg_type    = w_fdiv_aux.reg_type;
    end else begin
      o_result      = 'h0;
      o_fflags      = 'h0;
      o_sched_index = 'h0;
      o_rnid        = 'h0;
      o_reg_type    = msrh_pkg::FPR;
    end // else: !if(w_fdiv_out_valid)
  end // always_comb

end // block: block_32
endgenerate

endmodule // msrh_fpnew_wrapper
