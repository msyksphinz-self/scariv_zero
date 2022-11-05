module tb_flash #(
    parameter FILE = "",
    parameter DATA_W = 256,
    parameter TAG_W = 4,
    parameter ADDR_W = 12,
    parameter BASE_ADDR = 'h1000,
    parameter SIZE = 4096,
    parameter RD_LAT = 10
) (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request
    input  logic                   i_req_valid,
    input  msrh_lsu_pkg::mem_cmd_t i_req_cmd,
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

logic [DATA_W-1: 0]           r_ram[WORDS];

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
    r_resp_valid[0] <= i_req_valid & (i_req_cmd == msrh_lsu_pkg::M_XRD);
    r_resp_data [0] <= r_ram[w_req_addr_wo_offset[$clog2(DATA_W / 8) +: $clog2(WORDS)]];
    r_resp_tag  [0] <= i_req_tag;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (i_req_valid && (i_req_cmd == msrh_lsu_pkg::M_XWR)) begin
      r_ram[w_req_addr_wo_offset[$clog2(DATA_W / 8) +: $clog2(WORDS)]] <= i_req_data;
    end
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
  if (FILE == "image") begin
    if (msrh_conf_pkg::ICACHE_DATA_W == 128) begin
      $readmemh ("../../../tests/linux/image_w16.hex", r_ram);
    end else if (msrh_conf_pkg::ICACHE_DATA_W == 256) begin
      $readmemh ("../../../tests/linux/image_w32.hex", r_ram);
    end else if (msrh_conf_pkg::ICACHE_DATA_W == 512) begin
      $readmemh ("../../../tests/linux/image_w64.hex", r_ram);
    end
  end else if (FILE == "initrd") begin
    if (msrh_conf_pkg::ICACHE_DATA_W == 128) begin
      $readmemh ("../../../tests/linux/spike_rootfs_w16.hex", r_ram);
    end else if (msrh_conf_pkg::ICACHE_DATA_W == 256) begin
      $readmemh ("../../../tests/linux/spike_rootfs_w32.hex", r_ram);
    end else if (msrh_conf_pkg::ICACHE_DATA_W == 512) begin
      $readmemh ("../../../tests/linux/spike_rootfs_w64.hex", r_ram);
    end
  end
end

endmodule // tb_flash
