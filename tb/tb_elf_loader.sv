import "DPI-C" function int debug_tick
(
 output bit debug_req_valid,
 input bit  debug_req_ready,
 output int debug_req_bits_addr,
 output int debug_req_bits_data
);

module tb_elf_loader
(
 input logic         i_clk,
 input logic         i_reset_n,

 output logic        o_req_vld,
 output logic [31:0] o_req_bits_addr,
 output logic [31:0] o_req_bits_data,
 input logic         i_req_rdy
);

logic                __debug_req_vld;
logic [31: 0]        __debug_req_bits_addr;
logic [31: 0]        __debug_req_bits_data;

logic                req_vld_reg;
logic [31:0]         req_bits_addr_reg;
logic [31:0]         req_bits_data_reg;

always_ff @(posedge clock) begin
  req_vld_reg     <= __debug_req_vld;
  req_bits_addr_reg <= __debug_req_bits_addr;
  req_bits_data_reg <= __debug_req_bits_data;
end

assign req_vld       = req_vld_reg;
assign req_bits_addr = req_bits_addr_reg;
assign req_bits_data = req_bits_data_reg;

int debug_tick_val;

always_ff @(negedge clock, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    debug_tick_val = debug_tick(
      __debug_req_vld,
      req_rdy,
      __debug_req_bits_addr,
      __debug_req_bits_data
      );
  end
end

endmodule // tb_elf_loader
