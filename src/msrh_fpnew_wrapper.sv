module msrh_fpnew_wrapper
  (
   input logic                           i_clk,
   input logic                           i_reset_n,

   input logic                           i_valid,
   output logic                          o_ready,

   input logic [riscv_pkg::XLEN_W-1: 0]  i_rs1,
   input logic [riscv_pkg::XLEN_W-1: 0]  i_rs2,
   input logic [riscv_pkg::XLEN_W-1: 0]  i_rs3,

   output logic                          o_valid,
   output logic [riscv_pkg::XLEN_W-1: 0] o_result,
   output logic [ 4: 0]                  o_fflags
   );


logic [2:0][31:0]                       w_fma32_rs;
logic [2: 0]                            w_fma32_boxed;
logic [31: 0]                           w_fma32_result;
fpnew_pkg::status_t                     w_fma32_fflags;
logic                                   w_fma32_valid;
assign w_fma32_rs[0] = i_rs1[31: 0];
assign w_fma32_rs[1] = i_rs2[31: 0];
assign w_fma32_rs[2] = i_rs3[31: 0];
assign w_fma32_boxed[2:0] = 3'b000;

fpnew_fma
  #(
    .FpFormat   (fpnew_pkg::FP32),
    .NumPipeRegs(4),
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
 .op_i            (fpnew_pkg::FMADD ),  // input fpnew_pkg::operation_e
 .op_mod_i        (1'b0             ),  // input logic
 .tag_i           (1'b0             ),  // input TagType
 .aux_i           (1'b0             ),  // input AuxType
 // Input Handshake
 .in_valid_i      (i_valid          ),  // input  logic
 .in_ready_o      (o_ready          ),  // output logic
 .flush_i         (1'b0             ),  // input  logic
 // Output signals
 .result_o        (w_fma32_result   ),  // output logic [WIDTH-1:0]
 .status_o        (w_fma32_fflags   ),  // output fpnew_pkg::status_t
 .extension_bit_o (                 ),  // output logic
 .tag_o           (                 ),  // output TagType
 .aux_o           (                 ),  // output AuxType
 // Output handshake
 .out_valid_o     (w_fma32_valid    ),  // output logic
 .out_ready_i     (1'b1             ),  // input  logic
 // Indication of valid data in flight
 .busy_o          (                 )   // output logic
 );

generate if (riscv_pkg::XLEN_W==64) begin : fma64
  logic [2:0][63: 0]                      w_fma64_rs;
  logic [2: 0]                            w_fma64_boxed;
  logic [63: 0]                           w_fma64_result;
  fpnew_pkg::status_t                     w_fma64_fflags;
  logic                                   w_fma64_valid;
  assign w_fma64_rs[0] = i_rs1[63: 0];
  assign w_fma64_rs[1] = i_rs2[63: 0];
  assign w_fma64_rs[2] = i_rs3[63: 0];
  assign w_fma64_boxed[2:0] = 3'b000;

  fpnew_fma
    #(
      .FpFormat   (fpnew_pkg::FP64),
      .NumPipeRegs(4),
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
   .op_i            (fpnew_pkg::FMADD ),  // input fpnew_pkg::operation_e
   .op_mod_i        (1'b0             ),  // input logic
   .tag_i           (1'b0             ),  // input TagType
   .aux_i           (1'b0             ),  // input AuxType
   // Input Handshake
   .in_valid_i      (i_valid          ),  // input  logic
   .in_ready_o      (o_ready          ),  // output logic
   .flush_i         (1'b0             ),  // input  logic
   // Output signals
   .result_o        (w_fma64_result   ),  // output logic [WIDTH-1:0]
   .status_o        (w_fma64_fflags   ),  // output fpnew_pkg::status_t
   .extension_bit_o (                 ),  // output logic
   .tag_o           (                 ),  // output TagType
   .aux_o           (                 ),  // output AuxType
   // Output handshake
   .out_valid_o     (w_fma64_valid    ),  // output logic
   .out_ready_i     (1'b1             ),  // input  logic
   // Indication of valid data in flight
   .busy_o          (                 )   // output logic
   );

  assign o_valid  = w_fma32_valid | w_fma64_valid;
  assign o_result = w_fma32_valid ? {{32{w_fma32_result[31]}}, w_fma32_result} : w_fma64_result;
  assign o_fflags = w_fma32_valid ? w_fma32_fflags : w_fma64_fflags;

end else if (riscv_pkg::XLEN_W==32) begin : block_32 // block: fma64
  assign o_valid  = w_fma32_valid;
  assign o_result = w_fma32_result;
  assign o_fflags = w_fma32_fflags;
end
endgenerate


endmodule // msrh_fpnew_wrapper
