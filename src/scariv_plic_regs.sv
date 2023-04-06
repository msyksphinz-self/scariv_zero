// ------------------------------------------------------------------------
// NAME : SCARIV PLIC Registers
// TYPE : module
// ------------------------------------------------------------------------
// PLIC (Platform Level Interrupt Controller)
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_plic_regs
  #(
    parameter DATA_W    = 256,
    parameter TAG_W     = 4,
    parameter ADDR_W    = 12,
    parameter BASE_ADDR = 'h5400_0000,
    parameter SIZE      = 'h1000,

    parameter NUM_PRIORITIES = 4,
    parameter NUM_HARTS = 4,
    parameter NUM_SOURCES = 8
    )
(
 input logic i_clk,
 input logic i_reset_n,

 input  logic                     i_req_valid,
 input  scariv_lsu_pkg::mem_cmd_t i_req_cmd,
 input  logic [  ADDR_W-1:0]      i_req_addr,
 input  logic [   TAG_W-1:0]      i_req_tag,
 input  logic [  DATA_W-1:0]      i_req_data,
 input  logic [DATA_W/8-1:0]      i_req_byte_en,
 output logic                     o_req_ready,

 output logic              o_resp_valid,
 output logic [ TAG_W-1:0] o_resp_tag,
 output logic [DATA_W-1:0] o_resp_data,
 input  logic              i_resp_ready,

 output logic [NUM_SOURCES-1: 0]            o_reg_pending,
 output logic [$clog2(NUM_PRIORITIES)-1: 0] o_reg_priorities[NUM_SOURCES],
 output logic [NUM_SOURCES-1: 0]            o_reg_enables[NUM_HARTS],
 output logic [$clog2(NUM_PRIORITIES)-1: 0] o_reg_threshold[NUM_HARTS],

 input logic [NUM_SOURCES-1: 0] i_pending_update_valid,
 input logic [NUM_SOURCES-1: 0] i_pending_update_value
 );

localparam SRC_PRIO_BASE_ADDR  = BASE_ADDR + 'h4;
localparam PENDING_BASE_ADDR   = BASE_ADDR + 'h1000;
localparam ENABLE_BASE_ADDR    = BASE_ADDR + 'h2000;
localparam THRESHOLD_BASE_ADDR = BASE_ADDR + 'h20_0000;

localparam PRIO_REG_BLOCK_NUM = $clog2(NUM_PRIORITIES) / 8; // number of 8-bit blocks

logic                                      w_priority_region;
logic                                      w_pending_region;
logic [$clog2(NUM_HARTS+1)-1: 0]           w_enables_region;
logic [$clog2(NUM_HARTS+1)-1: 0]           w_threshold_region;

logic [ADDR_W-1: 0]                        w_priority_addr ;
logic [ADDR_W-1: 0]                        w_pending_addr  ;
logic [ADDR_W-1: 0]                        w_enables_addr   ;
logic [ADDR_W-1: 0]                        w_threshold_addr;

assign w_priority_addr  = i_req_addr - SRC_PRIO_BASE_ADDR;
assign w_pending_addr   = i_req_addr - PENDING_BASE_ADDR;
assign w_enables_addr   = i_req_addr - ENABLE_BASE_ADDR;
assign w_threshold_addr = i_req_addr - THRESHOLD_BASE_ADDR;

logic                                      w_resp_valid_pre;
logic [ TAG_W-1:0]                         w_resp_tag_pre;
logic [DATA_W-1:0]                         w_resp_data_pre;

always_comb begin
  w_resp_valid_pre = i_req_valid & (i_req_cmd == scariv_lsu_pkg::M_XRD);
  w_resp_tag_pre   = i_req_tag;

  if (w_priority_region) begin
    w_resp_data_pre = o_reg_priorities[w_priority_addr[2 +: $clog2(NUM_SOURCES+1)]] << {i_req_addr[$clog2(DATA_W/8)-1: 0], 3'b000};
  end else if (w_pending_region) begin
    w_resp_data_pre = o_reg_pending[w_pending_addr[2 +: $clog2(NUM_SOURCES+1)] +: NUM_SOURCES] << {i_req_addr[$clog2(DATA_W/8)-1: 0], 3'b000};
  end else if (w_enables_region) begin
    w_resp_data_pre = o_reg_enables[w_enables_addr[7 +: $clog2(NUM_HARTS+1)]][w_enables_addr[2 +: $clog2(NUM_SOURCES+1)]] << {i_req_addr[$clog2(DATA_W/8)-1: 0], 3'b000};
  end else if (w_threshold_region) begin
    w_resp_data_pre = o_reg_threshold[w_threshold_addr[7 +: $clog2(NUM_HARTS+1)]][w_threshold_addr[2 +: $clog2(NUM_SOURCES+1)]] << {i_req_addr[$clog2(DATA_W/8)-1: 0], 3'b000};
  end else begin
    w_resp_data_pre = 'h0;
  end
end


assign o_req_ready = ~o_resp_valid | o_resp_valid & ~i_resp_ready;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_resp_valid <= 1'b0;
  end else begin
    if (~o_resp_valid | o_resp_valid & i_resp_ready) begin
      o_resp_valid <= w_resp_valid_pre;
      o_resp_data  <= w_resp_data_pre;
      o_resp_tag   <= w_resp_tag_pre;
    end
  end
end

// ---------------------
// Priorities Registers
// ---------------------
generate for (genvar s_idx = 0; s_idx < NUM_SOURCES; s_idx++) begin: r_pri_loop
  logic priority_wr_valid;
  assign priority_wr_valid = i_req_valid &
                             (i_req_cmd == scariv_lsu_pkg::M_XWR) &
                             w_priority_region &
                             (w_priority_addr[ 2 +: $clog2(NUM_SOURCES+1)] + 0 == s_idx);

  scariv_plic_reg_priority
  u_reg
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),
     .i_wr         (priority_wr_valid   ),
     .i_wr_byte_en (i_req_byte_en[ 3: 0]),
     .i_wr_data    (i_req_data   [31: 0]),

     .o_data (o_reg_priorities[s_idx])
     );

end // block: r_pri_loop
endgenerate

// ------------------
// Pending Registers
// ------------------
generate for (genvar s_idx = 0; s_idx < NUM_SOURCES / 8; s_idx+=8) begin: r_pend_loop
  logic pending_wr_valid;
  assign pending_wr_valid = i_req_valid &
                            (i_req_cmd == scariv_lsu_pkg::M_XWR) &
                            w_pending_region &
                            (w_pending_addr[ 3 +: $clog2(NUM_SOURCES)] + 0 == s_idx);

  scariv_plic_reg_pending
  u_reg
   (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),
     .i_wr         (pending_wr_valid    ),
     .i_wr_byte_en (i_req_byte_en[ 3: 0]),
     .i_wr_data    (i_req_data   [31: 0]),

     .o_data (o_reg_pending[s_idx*8 +: 8])
    );

end // block: r_pend_loop
endgenerate


generate for (genvar h_idx = 0; h_idx < NUM_HARTS; h_idx++) begin : r_enables_loop

  logic enables_wr_valid;
  assign enables_wr_valid = i_req_valid &
                            (i_req_cmd == scariv_lsu_pkg::M_XWR) &
                            w_enables_region &
                            (w_enables_addr[ 7 +: $clog2(NUM_HARTS+1)] + 0 == h_idx);

  scariv_plic_reg_enables
  u_reg
   (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),
     .i_wr         (enables_wr_valid    ),
     .i_wr_byte_en (i_req_byte_en[ 3: 0]),
     .i_wr_data    (i_req_data   [31: 0]),

     .o_data (o_reg_enables[h_idx])
    );

end // block: r_enables_loop
endgenerate


generate for (genvar h_idx = 0; h_idx < NUM_HARTS; h_idx++) begin : r_threshold_loop

  logic threshold_wr_valid;
  assign threshold_wr_valid = i_req_valid &
                             (i_req_cmd == scariv_lsu_pkg::M_XWR) &
                             w_threshold_region &
                             (w_threshold_addr[ 7 +: $clog2(NUM_HARTS+1)] + 0 == h_idx);

  scariv_plic_reg_threshold
  u_reg
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),
     .i_wr         (threshold_wr_valid   ),
     .i_wr_byte_en (i_req_byte_en[ 3: 0]),
     .i_wr_data    (i_req_data   [31: 0]),

     .o_data (o_reg_threshold[h_idx])
     );

end // block: r_source_loop
endgenerate

// Memory Map
always_comb begin
  w_priority_region  = 1'b0;
  w_pending_region   = 1'b0;
  w_enables_region    = 'h0;
  w_threshold_region = 'h0;

  if (i_req_valid) begin
      if (i_req_addr == BASE_ADDR + 'h0) begin
        // ignore
      end else if (i_req_addr >= SRC_PRIO_BASE_ADDR && i_req_addr < SRC_PRIO_BASE_ADDR + (NUM_SOURCES * 4)) begin
        w_priority_region = 1'b1;
        // Source Priority
      end else if (i_req_addr >= PENDING_BASE_ADDR && i_req_addr < PENDING_BASE_ADDR + (NUM_SOURCES + 32) / 32 * 4) begin
        // Pending Bits
        w_pending_region = 1'b1;
      end else if (i_req_addr >= ENABLE_BASE_ADDR && i_req_addr < ENABLE_BASE_ADDR + NUM_HARTS * 4) begin
        // Enable Bits
        w_enables_region = 'h1 << w_enables_addr[7 +: $clog2(NUM_HARTS + 1)];
      end else if (i_req_addr >= THRESHOLD_BASE_ADDR && i_req_addr < THRESHOLD_BASE_ADDR + NUM_HARTS * 4) begin
        // Threshold
        w_threshold_region = 'h1 << w_threshold_addr[12 +: $clog2(NUM_HARTS + 1)];
      end
  end // if (i_req_valid & i_req_cmd == scariv_lsu_pkg::XWR)
end // always_comb



endmodule // scariv_plic_regs
