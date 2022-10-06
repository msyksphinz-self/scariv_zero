module msrh_serialdevice #(
    parameter DATA_W    = 256,
    parameter TAG_W     = 4,
    parameter ADDR_W    = 12,
    parameter BASE_ADDR = 'h5400_0000,
    parameter SIZE      = 'h1000,
    parameter RD_LAT    = 10
) (
    input logic i_clk,
    input logic i_reset_n,

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

assign o_req_ready = 1'b1;
assign o_resp_valid = 1'b0;

integer                       device_fp;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (i_req_valid & o_req_ready &
        (i_req_addr == BASE_ADDR) &
        (i_req_cmd == msrh_lsu_pkg::M_XWR)) begin
      $fwrite (device_fp, "%c", i_req_data[ 7: 0]);
    end
  end
end

initial begin
  device_fp = $fopen("serial.out", "w");
end

endmodule // msrh_serialdevice
