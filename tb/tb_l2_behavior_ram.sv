module tb_l2_behavior_ram
  #(
    parameter DATA_W    = 256,
    parameter TAG_W     = 4,
    parameter ADDR_W    = 12,
    parameter BASE_ADDR = 'h8000_0000,
    parameter SIZE      = 4096,
    parameter RD_LAT    = 10
    )
(
   input logic                i_clk,
   input logic                i_reset_n,

  // L2 request from ICache
   input logic                i_req_valid,
   input msrh_lsu_pkg::mem_cmd_t   i_req_cmd,
   input logic [ADDR_W-1:0]   i_req_addr,
   input logic [TAG_W-1:0]    i_req_tag,
   input logic [DATA_W-1:0]   i_req_data,
   input logic [DATA_W/8-1:0] i_req_byte_en,
   output logic               o_req_ready,

   output logic               o_resp_valid,
   output logic [TAG_W-1:0]   o_resp_tag,
   output logic [DATA_W-1:0]  o_resp_data,
   input logic                i_resp_ready
   );

localparam SIZE_W = $clog2(SIZE);

logic [DATA_W-1:0]         ram[SIZE];
logic                      req_fire;
logic [ADDR_W-1:0]         actual_addr;
logic [ADDR_W-1:0]         actual_line_pos;
logic [DATA_W-1:0]         rd_data[RD_LAT];
logic [TAG_W-1:0]          rd_tag[RD_LAT];
logic [RD_LAT-1:0]         rd_valid;

assign o_req_ready = 1'b1;
assign req_fire = i_req_valid & o_req_ready;
/* verilator lint_off WIDTH */
assign actual_addr = i_req_addr - BASE_ADDR;
assign actual_line_pos = actual_addr >> $clog2(DATA_W/8);



always_ff @ (posedge i_clk) begin
  if (req_fire && i_req_cmd == msrh_lsu_pkg::M_XWR) begin
    for (int byte_idx = 0; byte_idx < DATA_W/8; byte_idx++) begin
      if (i_req_byte_en[byte_idx]) begin
        ram[actual_line_pos[SIZE_W-1:0]][byte_idx*8+:8] <= i_req_data[byte_idx*8+:8];
      end
    end
  end
end


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < RD_LAT; i++) begin
      rd_valid[i] <= 1'b0;
    end
  end else begin
    if (req_fire && i_req_cmd == msrh_lsu_pkg::M_XRD) begin
      rd_data[0] <= ram[actual_line_pos[SIZE_W-1:0]];
      rd_tag[0]   <= i_req_tag;
      rd_valid[0] <= 1'b1;
    end else begin
      rd_valid[0] <= 1'b0;
    end

    if (!(o_resp_valid & !i_resp_ready)) begin
      for (int i = 1; i < RD_LAT; i++) begin
        rd_valid[i] <= rd_valid[i-1];
        rd_tag  [i] <= rd_tag  [i-1];
        rd_data [i] <= rd_data [i-1];
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_resp_valid = rd_valid[RD_LAT-1];
assign o_resp_tag   = rd_tag  [RD_LAT-1];
assign o_resp_data  = rd_data [RD_LAT-1];

// always_ff @ (posedge i_clk, negedge i_reset_n) begin
//   if (!i_reset_n) begin
//   end else begin
//     if (req_fire) begin
//       /* verilator lint_off WIDTH */
//       if (actual_line_pos >= SIZE || i_req_addr < BASE_ADDR) begin
//         $display("ERROR: address %10x is out of region of L2 RAM", i_req_addr);
//         $stop;
//       end
//     end
//   end
// end

endmodule // tb_l2_behavior_ram
