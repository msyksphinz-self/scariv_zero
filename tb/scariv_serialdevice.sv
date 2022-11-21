module scariv_serialdevice #(
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

assign o_req_ready = 1'b1;
assign o_resp_valid = 1'b0;

integer                       device_fp;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (i_req_valid & o_req_ready &
        (i_req_addr == BASE_ADDR) &
        (i_req_cmd == scariv_lsu_pkg::M_XWR)) begin
      if (i_req_data[ 7: 0] >= 'h20 ||
          i_req_data[ 7: 0] == 'h0a || // LF
          i_req_data[ 7: 0] == 'h0d    // CR
          ) begin
        $fwrite (device_fp, "%c", i_req_data[ 7: 0]);
        $fflush (device_fp);
      end
    end
  end
end

logic               r_read_valid_init;
logic [DATA_W-1: 0] r_read_data_init;
logic [TAG_W-1: 0]  r_read_tag_init;

logic               r_read_valid[10];
logic [DATA_W-1: 0] r_read_data [10];
logic [TAG_W-1: 0]  r_read_tag  [10];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_read_valid_init <= 1'b0;
    r_read_data_init  <= 'h0;
    r_read_tag_init   <= 'h0;
  end else begin
    if (i_req_valid & o_req_ready &
        (i_req_cmd == scariv_lsu_pkg::M_XRD)) begin
      r_read_valid_init <= 1'b1;
      r_read_tag_init   <= i_req_tag;
      case (i_req_addr)
        BASE_ADDR + 5 : begin
          r_read_data_init  <= 'h20 << ((5 % (DATA_W/8)) * 8);
        end
        default : begin
          r_read_data_init  <= 'h00;
        end
      endcase // case (i_req_addr)
    end else begin
      r_read_valid_init <= 1'b0;
      r_read_data_init  <= 'h0;
      r_read_tag_init   <= 'h0;
    end
  end // else: !if(!i_reset_n)
end


generate for (genvar i = 0; i < 10; i++) begin : device_resp_loop
  if (i == 0) begin
    always_ff @ (posedge i_clk) begin
      r_read_valid[i] <= r_read_valid_init;
      r_read_data [i] <= r_read_data_init;
      r_read_tag  [i] <= r_read_tag_init;
    end
  end else begin
    always_ff @ (posedge i_clk) begin
      r_read_valid[i] <= r_read_valid[i-1];
      r_read_data [i] <= r_read_data [i-1];
      r_read_tag  [i] <= r_read_tag  [i-1];
    end
  end // else: !if(i == 0)
end
endgenerate

assign o_resp_valid = r_read_valid[9];
assign o_resp_data  = r_read_data [9];
assign o_resp_tag   = r_read_tag  [9];

initial begin
  device_fp = $fopen("serial.out", "w");
end

endmodule // scariv_serialdevice
