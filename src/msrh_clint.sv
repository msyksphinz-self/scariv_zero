// ------------------------------------------------------------------------
// NAME : MSRH CLINT
// TYPE : module
// ------------------------------------------------------------------------
// CLINT (Core Local Interruptor)
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_clint #(
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
   input  logic              i_resp_ready,

   clint_if.master clint_if
);

logic w_req_fire;

logic r_msip;
logic [ 7: 0] r_mtimecmp[riscv_pkg::XLEN_W/8];
logic [ 7: 0] r_mtime[riscv_pkg::XLEN_W/8];

logic [riscv_pkg::XLEN_W-1: 0] w_mtime_flatten;
logic [riscv_pkg::XLEN_W-1: 0] w_mtime_next;
logic [riscv_pkg::XLEN_W-1: 0] w_mtimecmp_flatten;

assign o_req_ready = !(o_resp_valid & !i_resp_ready);

assign w_req_fire = i_req_valid & o_req_ready;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_msip <= 1'b0;
  end else begin
    if (w_req_fire &
        (i_req_cmd == msrh_lsu_pkg::M_XWR) &
        (i_req_addr == BASE_ADDR)) begin
      r_msip <= i_req_data[0];
    end
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int b_idx = 0; b_idx < riscv_pkg::XLEN_W/8; b_idx++) begin
      r_mtimecmp[b_idx] <= 8'h0;
    end
  end else begin
    if (w_req_fire &
        (i_req_cmd == msrh_lsu_pkg::M_XWR) &
        (i_req_addr == BASE_ADDR + 'h4000)) begin
      for (int b_idx = 0; b_idx < riscv_pkg::XLEN_W/8; b_idx++) begin
        r_mtimecmp[b_idx] <= i_req_data[b_idx * 8 +: 8];
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int b_idx = 0; b_idx < riscv_pkg::XLEN_W/8; b_idx++) begin
      r_mtime[b_idx] <= 8'h0;
    end
  end else begin
    if (w_req_fire &
        (i_req_cmd == msrh_lsu_pkg::M_XWR) &
        (i_req_addr == BASE_ADDR + 'hbff8)) begin
      for (int b_idx = 0; b_idx < riscv_pkg::XLEN_W/8; b_idx++) begin
        r_mtime[b_idx] <= i_req_data[b_idx * 8 +: 8];
      end
    end else begin
      for (int b_idx = 0; b_idx < riscv_pkg::XLEN_W/8; b_idx++) begin
        r_mtime[b_idx] <= w_mtime_next[b_idx * 8 +: 8];
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


logic w_resp_valid_next;
riscv_pkg::xlen_t w_resp_data_next;
logic [TAG_W-1:0] w_resp_tag_next;


always_comb begin
  if (w_req_fire &
      (i_req_cmd == msrh_lsu_pkg::M_XRD)) begin
    case (i_req_addr)
      BASE_ADDR + 'h0000 : begin
        w_resp_valid_next = 1'b1;
        w_resp_tag_next   = i_req_tag;
        w_resp_data_next  = {{(riscv_pkg::XLEN_W-1){1'b0}}, r_msip};
      end
      BASE_ADDR + 'h4000 : begin
        w_resp_valid_next = 1'b1;
        w_resp_tag_next   = i_req_tag;
        w_resp_data_next  = w_mtimecmp_flatten;
      end
      BASE_ADDR + 'hbff8 : begin
        w_resp_valid_next = 1'b1;
        w_resp_tag_next   = i_req_tag;
        w_resp_data_next  = w_mtime_flatten;
      end
      default : begin
        w_resp_valid_next = 1'b0;
        w_resp_tag_next   = i_req_tag;
        w_resp_data_next  = 'h0;
      end
    endcase // case (i_req_addr)
  end else begin // if (w_req_fire &...
    w_resp_valid_next = 1'b0;
  end // if (w_req_fire &...
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_resp_valid <= 1'b0;
  end else begin
    if (o_resp_valid & i_resp_ready) begin
      o_resp_valid <= 1'b0;
    end else if (!(o_resp_valid & !i_resp_ready)) begin
      o_resp_valid <= w_resp_valid_next;
      o_resp_data  <= w_resp_data_next << {i_req_addr[$clog2(DATA_W/8)-1:0], 3'b000};
      o_resp_tag   <= w_resp_tag_next;
    end
  end
end

logic [ 5: 0] r_interleave;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_interleave <= 6'h0;
  end else begin
    r_interleave <= r_interleave + 'h1;
  end
end


assign w_mtime_next = w_mtime_flatten + &r_interleave;
generate for(genvar b_idx = 0; b_idx < riscv_pkg::XLEN_W/8; b_idx++) begin : byte_loop
  assign w_mtime_flatten   [b_idx * 8 +: 8] = r_mtime[b_idx];
  assign w_mtimecmp_flatten[b_idx * 8 +: 8] = r_mtimecmp[b_idx];
end
endgenerate

assign clint_if.ipi_valid = r_msip;
assign clint_if.time_irq_valid = w_mtime_flatten >= w_mtimecmp_flatten;

endmodule // msrh_st_buffer
