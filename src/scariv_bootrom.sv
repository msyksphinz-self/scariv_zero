// ------------------------------------------------------------------------
// NAME : scariv_bootrom
// TYPE : module
// ------------------------------------------------------------------------
// BootROM
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------


module scariv_bootrom #(
    parameter DATA_W    = 256,
    parameter TAG_W     = 4,
    parameter ADDR_W    = 12,
    parameter BASE_ADDR = 'h1000,
    parameter SIZE      = 4096,
    parameter RD_LAT    = 10
) (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request
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
    input  logic              i_resp_ready
);

localparam WORDS = SIZE / (DATA_W / 8);

logic [DATA_W-1: 0]           r_rom[WORDS];

assign o_req_ready = 1'b1;

logic [RD_LAT-1: 0]           r_resp_valid;
logic [DATA_W-1: 0]           r_resp_data[RD_LAT];
logic [TAG_W-1 : 0]           r_resp_tag [RD_LAT];

logic [ADDR_W-1: 0]           w_req_addr_wo_offset;
assign w_req_addr_wo_offset = i_req_addr - BASE_ADDR;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_resp_valid[0] <= 'h0;
    r_resp_data [0] <= 'h0;
    r_resp_tag  [0] <= 'h0;
  end else begin
    r_resp_valid[0] <= i_req_valid;
    r_resp_data [0] <= r_rom[w_req_addr_wo_offset[$clog2(DATA_W / 8) +: $clog2(WORDS)]];
    r_resp_tag  [0] <= i_req_tag;
  end
end

generate for (genvar p_idx = 1; p_idx < RD_LAT; p_idx ++) begin : rd_loop
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_resp_valid[p_idx] <= 'h0;
      r_resp_tag  [p_idx] <= 'h0;
      r_resp_data [p_idx] <= 'h0;
    end else begin
      r_resp_valid[p_idx] <= r_resp_valid[p_idx-1];
      r_resp_tag  [p_idx] <= r_resp_tag  [p_idx-1];
      r_resp_data [p_idx] <= r_resp_data [p_idx-1];
    end
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end // block: rd_loop
endgenerate

assign o_resp_valid = r_resp_valid[RD_LAT-1];
assign o_resp_tag   = r_resp_tag  [RD_LAT-1];
assign o_resp_data  = r_resp_data [RD_LAT-1];

initial begin
  if (scariv_conf_pkg::ICACHE_DATA_W == 64) begin
    $readmemh ("../../../dts/bootrom_w8.hex", r_rom);
  end else if (scariv_conf_pkg::ICACHE_DATA_W == 128) begin
    $readmemh ("../../../dts/bootrom_w16.hex", r_rom);
  end else if (scariv_conf_pkg::ICACHE_DATA_W == 256) begin
    $readmemh ("../../../dts/bootrom_w32.hex", r_rom);
  end else if (scariv_conf_pkg::ICACHE_DATA_W == 512) begin
    $readmemh ("../../../dts/bootrom_w64.hex", r_rom);
  end
end

endmodule // scariv_bootrom
