module msrh_bootrom #(
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

logic [DATA_W-1: 0]           r_rom[SIZE / (DATA_W / 8)];


initial begin
  $readmemh ("../../../dts/bootrom.hex", r_rom);
end

endmodule // msrh_bootrom
