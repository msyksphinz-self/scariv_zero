module inst_buffer
  #(
    parameter DISPATCH_SIZE = 5
    )
(
 input logic                                i_clk,
 input logic                                i_reset_n,

 input logic                                i_inst_vld,

 output logic                               o_inst_rdy,
 input logic [mrh_pkg::ICACHE_DATA_W-1: 0]  i_inst_in,
 input logic [mrh_pkg::ICACHE_DATA_B_W-1:0] i_inst_byte_en,

 output logic                               o_inst_buf_valid,
 output mrh_pkg::inst_buf_t                 o_inst_buf[DISPATCH_SIZE],
 input logic                                i_inst_buf_ready
 );

logic [ 1: 0]                               inst_buffer_vld_q;
logic [mrh_pkg::ICACHE_DATA_W-1: 0]         inst_buffer_q[2];
logic [mrh_pkg::ICACHE_DATA_B_W-1: 0]       inst_buffer_byte_en_q[2];
logic [mrh_pkg::ICACHE_DATA_B_W-1: 0]       inst_buffer_en_pick_up;
logic [$clog2(mrh_pkg::ICACHE_DATA_B_W)-1:0] inst_buffer_en_ff_idx;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    inst_buffer_vld_q <= 2'b00;
  end else begin
    if (i_inst_vld & o_inst_rdy) begin
      if (!inst_buffer_vld_q[0]) begin
        inst_buffer_q[0]         <= i_inst_in;
        inst_buffer_vld_q[0]     <= 1'b1;
        inst_buffer_byte_en_q[0] <= i_inst_byte_en;
      end else begin
        inst_buffer_q[1]         <= i_inst_in;
        inst_buffer_vld_q[1]     <= 1'b1;
        inst_buffer_byte_en_q[1] <= i_inst_byte_en;
      end
    end // if (i_inst_vld & o_inst_rdy)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_inst_rdy = !(&inst_buffer_vld_q);

bit_ff_lsb #(.WIDTH(mrh_pkg::ICACHE_DATA_B_W)) u_byte_en_ff (.in(inst_buffer_byte_en_q[0]), .valid(), .out(inst_buffer_en_ff_idx));

endmodule // inst_buffer
