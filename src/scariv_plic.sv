// ------------------------------------------------------------------------
// NAME : SCARIV PLIC
// TYPE : module
// ------------------------------------------------------------------------
// PLIC (Platform Level Interrupt Controller)
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_plic #(
    parameter DATA_W    = 256,
    parameter TAG_W     = 4,
    parameter ADDR_W    = 12,
    parameter BASE_ADDR = 'h5400_0000,
    parameter SIZE      = 'h1000,

    parameter NUM_PRIORITIES = 4,
    parameter NUM_HARTS = 4,
    parameter NUM_SOURCES = 8
) (
   input logic i_clk,
   input logic i_reset_n,

   input  logic                   i_req_valid,
   input  scariv_lsu_pkg::mem_cmd_t i_req_cmd,
   input  logic [  ADDR_W-1:0]    i_req_addr,
   input  logic [   TAG_W-1:0]    i_req_tag,
   input  logic [  DATA_W-1:0]    i_req_data,
   input  logic [DATA_W/8-1:0]    i_req_byte_en,
   output logic                   o_req_ready,

   output logic              o_resp_valid,
   output logic [ TAG_W-1:0] o_resp_tag,
   output logic [DATA_W-1:0] o_resp_data,
   input  logic              i_resp_ready,

   input logic [NUM_SOURCES-1: 0] i_interrupts,

   plic_if.master plic_if
);

logic [NUM_SOURCES-1: 0]            w_reg_pending;
logic [$clog2(NUM_PRIORITIES)-1: 0] w_reg_priorities[NUM_SOURCES];
logic [NUM_SOURCES-1: 0]            w_reg_enables[NUM_HARTS];
logic [$clog2(NUM_PRIORITIES)-1: 0] w_reg_threshold[NUM_HARTS];
logic [NUM_SOURCES-1: 0]            w_plic_valid;

logic [NUM_HARTS-1: 0]              w_int_eligible;

logic [DATA_W-1: 0]                 w_req_data_mask;
generate for (genvar b_idx = 0; b_idx < DATA_W/8; b_idx++) begin
  assign w_req_data_mask[b_idx*8 +: 8] = i_req_byte_en[b_idx];
end
endgenerate

generate for (genvar g_idx = 0; g_idx < NUM_SOURCES; g_idx++) begin : gateway_loop
  plic_gateway
  u_gateway
    (
     .i_clk     (i_clk),
     .i_reset_n (i_reset_n),

     .i_interrupt     (i_interrupts  [g_idx]),
     .i_plic_ready    (!w_reg_pending[g_idx]),
     .i_plic_complete (),
     .o_plic_valid    (w_plic_valid  [g_idx])
     );

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      w_reg_pending[g_idx] <= 'h0;
    end else begin
      // if (/* i_claimed[g_idx] | */w_plic_valid) begin
      //   w_reg_pending[g_idx] <= !i_claimed[g_idx];
      // end
    end
  end

end // block: gateway_loop
endgenerate


generate for (genvar h_idx = 0; h_idx < NUM_HARTS; h_idx++) begin : harts_loop

  // By FanIn, selected interrupt
  logic                                    w_int_valid;
  logic [$clog2(NUM_SOURCES)-1: 0]         w_int_index;
  logic [$clog2(NUM_PRIORITIES)-1: 0]      w_int_priority;

  // Device FanIn
  plic_fanin
    #(
      .NUM_SOURCES(NUM_SOURCES),
      .NUM_PRIORITIES(NUM_PRIORITIES)
      )
  u_fanin
    (
     .i_interrupts(w_reg_enables[h_idx] & w_reg_pending),
     .i_priority  (w_reg_priorities),

     .o_int_valid    (w_int_valid),
     .o_int_index    (w_int_index),
     .o_int_priority (w_int_priority)
     );

  assign plic_if.int_valid[h_idx] = w_int_valid & w_int_priority > w_reg_threshold[h_idx];

end // block: harts_loop
endgenerate


scariv_plic_regs
  #(
    .DATA_W    (DATA_W    ),
    .TAG_W     (TAG_W     ),
    .ADDR_W    (ADDR_W    ),
    .BASE_ADDR (BASE_ADDR ),
    .SIZE      (SIZE      ),

    .NUM_PRIORITIES (NUM_PRIORITIES),
    .NUM_HARTS      (NUM_HARTS     ),
    .NUM_SOURCES    (NUM_SOURCES   )
    )
u_regs
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_req_valid   (i_req_valid  ),
   .i_req_cmd     (i_req_cmd    ),
   .i_req_addr    (i_req_addr   ),
   .i_req_tag     (i_req_tag    ),
   .i_req_data    (i_req_data   ),
   .i_req_byte_en (i_req_byte_en),
   .o_req_ready   (o_req_ready  ),

   .o_resp_valid (o_resp_valid),
   .o_resp_tag   (o_resp_tag  ),
   .o_resp_data  (o_resp_data ),
   .i_resp_ready (i_resp_ready),

   .o_reg_pending    (w_reg_pending   ),
   .o_reg_priorities (w_reg_priorities),
   .o_reg_enables    (w_reg_enables   ),
   .o_reg_threshold  (w_reg_threshold ),

   .i_pending_update_valid (/* i_claimed | */w_plic_valid),
   .i_pending_update_value (/* ~i_claimed */)
   );

endmodule // scariv_plic

module plic_gateway
  (
   input logic  i_clk,
   input logic  i_reset_n,

   input logic  i_interrupt,
   input logic  i_plic_ready,
   input logic  i_plic_complete,
   output logic o_plic_valid
   );

logic          r_inflight;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inflight <= 1'b0;
  end else begin
    if (r_inflight & i_plic_complete) begin
      r_inflight <= 1'b0;
    end else if (i_interrupt & i_plic_ready) begin
      r_inflight <= 1'b1;
    end
  end
end

assign o_plic_valid = !r_inflight & i_interrupt;

endmodule // plic_gateway

module plic_fanin
  #(
    parameter NUM_SOURCES = 8,
    parameter NUM_PRIORITIES = 4
    )
(
 input logic [NUM_SOURCES-1: 0]            i_interrupts,
 input logic [$clog2(NUM_PRIORITIES)-1: 0] i_priority[NUM_SOURCES],

 output logic                              o_int_valid,
 output logic                              o_int_index,
 output logic                              o_int_priority
 );

logic [$clog2(NUM_PRIORITIES): 0][NUM_SOURCES-1: 0] w_priority_valids;

generate for(genvar s_idx = 0; s_idx < NUM_SOURCES; s_idx++) begin: priority_valid_loop
  assign w_priority_valids[s_idx] = {i_interrupts[s_idx], i_priority[s_idx]};
end
endgenerate

logic [$clog2(NUM_PRIORITIES)-1: 0] w_priority_max_value;
logic                               w_priority_max_valid;
logic [$clog2(NUM_SOURCES)-1: 0]    w_priority_max_index;

recurse_module_with_index
  #(
    .WIDTH    (NUM_SOURCES),
    .DATA_SIZE($clog2(NUM_PRIORITIES) + 1),
    .FUNCTION (recurse_pkg::MAX)
    )
u_recurse_max
  (
   .in        (w_priority_valids),
   .out       ({w_priority_max_valid, w_priority_max_value}),
   .out_index (w_priority_max_index)
   );

assign o_int_valid = w_priority_max_valid;
assign o_int_index = w_priority_max_index;
assign o_int_priority = w_priority_max_value;


endmodule // plic_fanin

module recurse_module_with_index
  #(
    parameter WIDTH = 32,
    parameter DATA_SIZE = 8,
    parameter FUNCTION = recurse_pkg::MAX
    )
(
 input logic [WIDTH-1: 0][DATA_SIZE-1:0] in,
 output logic [DATA_SIZE-1: 0]           out,
 output logic [$clog2(WIDTH)-1: 0]       out_index
 );

generate if (WIDTH <= 1) begin : width_1
  assign out = in[0];
  assign out = 'h0;
end else begin
  localparam HALF = WIDTH/2;

  logic [DATA_SIZE-1: 0] lo_value;
  logic [DATA_SIZE-1: 0] hi_value;

  logic [$clog2(HALF)-1: 0]       lo_index;
  logic [$clog2(WIDTH-HALF)-1: 0] hi_index;

  recurse_module_with_index #(.WIDTH(HALF))       module_lo (.in(in[HALF-1:0])    , .out(lo_value), .out_index(lo_index));
  recurse_module_with_index #(.WIDTH(WIDTH-HALF)) module_hi (.in(in[WIDTH-1:HALF]), .out(hi_value), .out_index(hi_index));

  if (FUNCTION == recurse_pkg::MAX) begin : max_op
    assign out       = lo_value < hi_value ? hi_value        : lo_value;
    assign out_index = lo_value < hi_value ? hi_index + HALF : lo_index;
  end else begin
    assign out       = 'h0;
    assign out_index = 'h0;
  end

end // else: !if(WIDTH == 1)
endgenerate

endmodule // recurse_module
