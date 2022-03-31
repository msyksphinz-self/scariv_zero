module msrh_fpnew_wrapper
  import decoder_fpu_ctrl_pkg::*;
  import msrh_fpu_pkg::*;
  (
   input logic                           i_clk,
   input logic                           i_reset_n,

   input logic                           i_valid,
   output logic                          o_ready,
   input pipe_ctrl_t                     i_pipe_ctrl,

   input riscv_pkg::xlen_t  i_rs1,
   input riscv_pkg::xlen_t  i_rs2,
   input riscv_pkg::xlen_t  i_rs3,

   output logic                          o_valid,
   output riscv_pkg::xlen_t o_result,
   output logic [ 4: 0]                  o_fflags
   );


logic                                    w_fma32_in_valid;

logic                                    w_fma_valid;
logic                                    w_noncomp_valid;

logic [2:0][31:0]                        w_fma32_rs;
logic [2: 0]                             w_fma32_boxed;
logic [31: 0]                            w_fma32_result;
fpnew_pkg::status_t                      w_fma32_fflags;
logic                                    w_fma32_out_valid;
logic                                    w_noncomp32_out_valid;
logic [31: 0]                            w_noncomp32_result;
fpnew_pkg::operation_e                   w_fpnew_op;
logic                                    w_fpnew_op_mod;

assign w_fma32_rs[0] = (w_fpnew_op == fpnew_pkg::ADD) ? 'h0          : i_rs1[31: 0];
assign w_fma32_rs[1] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs1[31: 0] : i_rs2[31: 0];
assign w_fma32_rs[2] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs2[31: 0] : i_rs3[31: 0];
assign w_fma32_boxed[2:0] = 3'b111;

always_comb begin
  case (i_pipe_ctrl.op)
    OP_FMADD     : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::FMADD   };
    OP_FMSUB     : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b1, fpnew_pkg::FMADD   };
    OP_FNMSUB    : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::FNMSUB  };
    OP_FNMADD    : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b1, fpnew_pkg::FNMSUB  };
    OP_FADD      : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::ADD     };
    OP_FSUB      : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b1, fpnew_pkg::ADD     };
    OP_FMUL      : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::MUL     };
    OP_FDIV      : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::DIV     };
    OP_FSQRT     : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::SQRT    };
    OP_FSGNJ_S   : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJN_S  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJX_S  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FMIN      : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::MINMAX  };
    OP_FMAX      : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::MINMAX  };
    OP_FCVT_W_S  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_WU_S : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FEQ       : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FLT       : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FLE       : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::CMP     };
    OP_FCLASS    : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b1, 1'b0, fpnew_pkg::CLASSIFY};
    OP_FCVT_S_W  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_S_WU : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FSGNJ_D   : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJN_D  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FSGNJX_D  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::SGNJ    };
    OP_FCVT_S_D  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2F     };
    OP_FCVT_D_S  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2F     };
    OP_FCVT_W_D  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_WU_D : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_D_W  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::I2F     };
    OP_FCVT_D_WU : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::I2F     };
`ifdef RV64
    OP_FCVT_L_D  : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2I     };
    OP_FCVT_LU_D : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b1, 1'b0, 1'b0, fpnew_pkg::F2I     };
`endif // RV64
    default      : {w_fma_valid, w_noncomp_valid, w_fpnew_op_mod, w_fpnew_op} = {1'b0, 1'b0, 1'b0, fpnew_pkg::FMADD   };
  endcase // case (i_op)
end // always_comb


assign w_fma32_in_valid    = i_valid & w_fma_valid     & (i_pipe_ctrl.size == SIZE_W);
assign w_noncmp32_in_valid = i_valid & w_noncomp_valid & (i_pipe_ctrl.size == SIZE_W);

fpnew_fma
  #(
    .FpFormat   (fpnew_pkg::FP32),
    .NumPipeRegs(1),
    .PipeConfig (fpnew_pkg::BEFORE),
    .TagType    (logic),
    .AuxType    (logic)
    )
fpnew_32
(
 .clk_i  (i_clk    ),
 .rst_ni (i_reset_n),
 // Input signals
 .operands_i      (w_fma32_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
 .is_boxed_i      (w_fma32_boxed    ),  // input logic [2:0]                 // 3 operands
 .rnd_mode_i      (fpnew_pkg::RNE   ),  // input fpnew_pkg::roundmode_e
 .op_i            (w_fpnew_op       ),  // input fpnew_pkg::operation_e
 .op_mod_i        (w_fpnew_op_mod   ),  // input logic
 .tag_i           (1'b0             ),  // input TagType
 .aux_i           (1'b0             ),  // input AuxType
 // Input Handshake
 .in_valid_i      (w_fma32_in_valid ),  // input  logic
 .in_ready_o      (o_ready          ),  // output logic
 .flush_i         (1'b0             ),  // input  logic
 // Output signals
 .result_o        (w_fma32_result   ),  // output logic [WIDTH-1:0]
 .status_o        (w_fma32_fflags   ),  // output fpnew_pkg::status_t
 .extension_bit_o (                 ),  // output logic
 .tag_o           (                 ),  // output TagType
 .aux_o           (                 ),  // output AuxType
 // Output handshake
 .out_valid_o     (w_fma32_out_valid),  // output logic
 .out_ready_i     (1'b1             ),  // input  logic
 // Indication of valid data in flight
 .busy_o          (                 )   // output logic
 );

fpnew_noncomp #(
    .FpFormat   (fpnew_pkg::FP32),
    .NumPipeRegs(1),
    .PipeConfig (fpnew_pkg::BEFORE),
    .TagType    (logic),
    .AuxType    (logic)
) fpnew_noncomp64 (
  .clk_i  (i_clk    ),
  .rst_ni (i_reset_n),
  .operands_i      ( w_fma32_rs             ),
  .is_boxed_i      ( w_fma32_boxed          ),
  .rnd_mode_i      ( w_fpnew_op             ),
  .op_i            ( w_fpnew_op_mod         ),
  .op_mod_i        ( 1'b0                   ),
  .tag_i           ( 1'b0                   ),
  .aux_i           (                        ), // Remember whether operation was vectorial
  .in_valid_i      ( w_noncomp32_in_valid   ),
  .in_ready_o      (                        ),
  .flush_i         ( 1'b0                   ),
  .result_o        ( w_noncomp32_result     ),
  .status_o        ( w_noncomp32_status     ),
  .extension_bit_o (                        ),
  .class_mask_o    ( w_noncomp32_class_mask ),
  .is_class_o      (                        ),
  .tag_o           (                        ),
  .aux_o           (                        ),
  .out_valid_o     ( w_noncomp32_out_valid  ),
  .out_ready_i     ( 1'b1                   ),
  .busy_o          (                        )
);

generate if (riscv_pkg::XLEN_W==64) begin : fma64
  logic [2:0][63: 0]                      w_fma64_rs;
  logic [2: 0]                            w_fma64_boxed;
  logic [63: 0]                           w_fma64_result;
  fpnew_pkg::status_t                     w_fma64_fflags;
  logic                                   w_fma64_out_valid;
  logic                                   w_fma64_in_valid;
  logic                                   w_noncomp64_in_valid;
  logic                                   w_noncomp64_out_valid;
  logic [63: 0]                           w_noncomp64_result;
  fpnew_pkg::status_t                     w_noncomp64_status;
  fpnew_pkg::classmask_e                  w_noncomp64_class_mask;

  assign w_fma64_rs[0] = (w_fpnew_op == fpnew_pkg::ADD) ? 'h0          : i_rs1[63: 0];
  assign w_fma64_rs[1] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs1[63: 0] : i_rs2[63: 0];
  assign w_fma64_rs[2] = (w_fpnew_op == fpnew_pkg::ADD) ? i_rs2[63: 0] : i_rs3[63: 0];
  assign w_fma64_boxed[2:0] = 3'b111;

  assign w_fma64_in_valid     = i_valid & w_fma_valid     & (i_pipe_ctrl.size == SIZE_DW);
  assign w_noncomp64_in_valid = i_valid & w_noncomp_valid & (i_pipe_ctrl.size == SIZE_DW);

  fpnew_fma
    #(
      .FpFormat   (fpnew_pkg::FP64),
      .NumPipeRegs(1),
      .PipeConfig (fpnew_pkg::BEFORE),
      .TagType    (logic),
      .AuxType    (logic)
      )
  fpnew_64
  (
   .clk_i  (i_clk    ),
   .rst_ni (i_reset_n),
   // Input signals
   .operands_i      (w_fma64_rs       ),  // input logic [2:0][WIDTH-1:0]      // 3 operands
   .is_boxed_i      (w_fma64_boxed    ),  // input logic [2:0]                 // 3 operands
   .rnd_mode_i      (fpnew_pkg::RNE   ),  // input fpnew_pkg::roundmode_e
   .op_i            (w_fpnew_op       ),  // input fpnew_pkg::operation_e
   .op_mod_i        (w_fpnew_op_mod   ),  // input logic
   .tag_i           (1'b0             ),  // input TagType
   .aux_i           (1'b0             ),  // input AuxType
   // Input Handshake
   .in_valid_i      (w_fma64_in_valid ),  // input  logic
   .in_ready_o      (o_ready          ),  // output logic
   .flush_i         (1'b0             ),  // input  logic
   // Output signals
   .result_o        (w_fma64_result   ),  // output logic [WIDTH-1:0]
   .status_o        (w_fma64_fflags   ),  // output fpnew_pkg::status_t
   .extension_bit_o (                 ),  // output logic
   .tag_o           (                 ),  // output TagType
   .aux_o           (                 ),  // output AuxType
   // Output handshake
   .out_valid_o     (w_fma64_out_valid),  // output logic
   .out_ready_i     (1'b1             ),  // input  logic
   // Indication of valid data in flight
   .busy_o          (                 )   // output logic
   );

  fpnew_noncomp #(
      .FpFormat   (fpnew_pkg::FP64),
      .NumPipeRegs(1),
      .PipeConfig (fpnew_pkg::BEFORE),
      .TagType    (logic),
      .AuxType    (logic)
  ) fpnew_noncomp64 (
    .clk_i  (i_clk    ),
    .rst_ni (i_reset_n),
    .operands_i      ( w_fma64_rs             ),
    .is_boxed_i      ( w_fma64_boxed          ),
    .rnd_mode_i      ( w_fpnew_op             ),
    .op_i            ( w_fpnew_op_mod         ),
    .op_mod_i        ( 1'b0                   ),
    .tag_i           ( 1'b0                   ),
    .aux_i           (                        ), // Remember whether operation was vectorial
    .in_valid_i      ( w_noncomp64_in_valid   ),
    .in_ready_o      (                        ),
    .flush_i         ( 1'b0                   ),
    .result_o        ( w_noncomp64_result     ),
    .status_o        ( w_noncomp64_status     ),
    .extension_bit_o (                        ),
    .class_mask_o    ( w_noncomp64_class_mask ),
    .is_class_o      (                        ),
    .tag_o           (                        ),
    .aux_o           (                        ),
    .out_valid_o     ( w_noncomp64_out_valid  ),
    .out_ready_i     ( 1'b1                   ),
    .busy_o          (                        )
  );

  assign o_valid  = w_fma32_out_valid | w_noncomp32_out_valid | w_fma64_out_valid | w_noncomp64_out_valid;
  assign o_result = w_fma32_out_valid     ? {{32{w_fma32_result    [31]}}, w_fma32_result} :
                    w_noncomp32_out_valid ? {{32{w_noncomp32_result[31]}}, w_noncomp32_result} :
                    w_fma64_out_valid  ? w_fma64_result :
                    /* w_noncomp64_out_valid ? */ w_noncomp64_result;
  assign o_fflags = w_fma32_out_valid ? w_fma32_fflags : w_fma64_fflags;

end else if (riscv_pkg::XLEN_W==32) begin : block_32 // block: fma64
  assign o_valid  = w_fma32_out_valid | w_noncomp32_out_valid;
  assign o_result = w_fma32_out_valid ? w_fma32_result    : w_noncomp32_result;
  assign o_fflags = w_fma32_fflags;
end
endgenerate


endmodule // msrh_fpnew_wrapper
