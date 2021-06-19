module tb_l2_behavior_ram #(
    parameter DATA_W    = 256,
    parameter TAG_W     = 4,
    parameter ADDR_W    = 12,
    parameter BASE_ADDR = 'h8000_0000,
    parameter SIZE      = 4096,
    parameter RD_LAT    = 10
) (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request
    input  logic                                  i_req_valid,
    input  msrh_lsu_pkg::mem_cmd_t                i_req_cmd,
    input  logic                   [  ADDR_W-1:0] i_req_addr,
    input  logic                   [   TAG_W-1:0] i_req_tag,
    input  logic                   [  DATA_W-1:0] i_req_data,
    input  logic                   [DATA_W/8-1:0] i_req_byte_en,
    output logic                                  o_req_ready,

    output logic              o_resp_valid,
    output logic [ TAG_W-1:0] o_resp_tag,
    output logic [DATA_W-1:0] o_resp_data,
    input  logic              i_resp_ready,

    // Snoop Interface
    output logic                          o_snoop_req_valid,
    output logic [riscv_pkg::PADDR_W-1:0] o_snoop_req_paddr,

    input logic                                     i_snoop_resp_valid,
    input logic [ msrh_conf_pkg::DCACHE_DATA_W-1:0] i_snoop_resp_data,
    input logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1:0] i_snoop_resp_be
);

  // localparam SIZE_W = $clog2(SIZE);

    typedef enum logic [0:0] {
        ST_INIT = 0,
        ST_GIVEN = 1
    } line_status_t;

    logic                [DATA_W-1:0] ram             [int unsigned];
    line_status_t                     status          [int unsigned];
    logic                             req_fire;
    logic                [ADDR_W-1:0] actual_addr;
    logic                [ADDR_W-1:0] actual_line_pos;
    logic                [DATA_W-1:0] rd_data         [RD_LAT];
    logic                [ TAG_W-1:0] rd_tag          [RD_LAT];
    logic                [RD_LAT-1:0] rd_valid;

    logic [riscv_pkg::PADDR_W-1:0] r_req_paddr_pos;
    logic                [ TAG_W-1:0] r_req_tag;

typedef enum logic [0:0] {
   IDLE = 0,
   SNOOP = 1
} state_t;

state_t r_state;

assign o_req_ready = (r_state == IDLE);
assign req_fire = i_req_valid & o_req_ready;
/* verilator lint_off WIDTH */
assign actual_addr = i_req_addr /* - BASE_ADDR */;
assign actual_line_pos = actual_addr >> $clog2(DATA_W / 8);

// initial begin
//   for (int i = 0; i < SIZE; i++) begin
//     status[i] = ST_INIT;
//   end
// end


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= IDLE;
    o_snoop_req_valid <= 1'b0;
    o_snoop_req_paddr <= 'h0;
    r_req_paddr_pos <= 'h0;
    r_req_tag <= 'h0;
  end else begin
    case(r_state)
      IDLE: begin
        if (req_fire && i_req_cmd == msrh_lsu_pkg::M_XWR) begin
          if ((status.exists(actual_line_pos) ? status[actual_line_pos] : ST_INIT) == ST_GIVEN) begin
            status[actual_line_pos] = ST_INIT;
          end
          for (int byte_idx = 0; byte_idx < DATA_W / 8; byte_idx++) begin
            if (i_req_byte_en[byte_idx]) begin
              ram[actual_line_pos][byte_idx*8+:8] = i_req_data[byte_idx*8+:8];
            end
          end
        end else if (req_fire && i_req_cmd == msrh_lsu_pkg::M_XRD) begin
          if (status[actual_line_pos] == ST_INIT) begin
            if (i_req_tag[TAG_W-1 -: 2] == msrh_lsu_pkg::L2_UPPER_TAG_RD_L1D) begin
              status[actual_line_pos] = ST_GIVEN;
            end
            rd_data[0] <= ram.exists(actual_line_pos) ? ram[actual_line_pos] : 'h0;
            rd_tag[0] <= i_req_tag;
            rd_valid[0] <= 1'b1;
          end else begin
            r_state <= SNOOP;
            o_snoop_req_valid <= 1'b1;
            o_snoop_req_paddr <= i_req_addr;
            r_req_paddr_pos <= actual_line_pos;
            r_req_tag <= i_req_tag;
          end
        end else begin
          rd_valid[0] <= 1'b0;
        end // else: !if(req_fire && i_req_cmd == msrh_lsu_pkg::M_XRD)
      end // case: IDLE
      SNOOP : begin
        o_snoop_req_valid <= 1'b0;
        o_snoop_req_paddr <= 'h0;
        if (i_snoop_resp_valid) begin
          r_state <= IDLE;
          status[r_req_paddr_pos] = ST_GIVEN;
          for (int byte_idx = 0; byte_idx < DATA_W / 8; byte_idx++) begin
            if (i_snoop_resp_be[byte_idx]) begin
              ram[r_req_paddr_pos][byte_idx*8+:8] = i_snoop_resp_data[byte_idx*8+:8];
            end
          end
          rd_data[0] <= i_snoop_resp_data;
          rd_tag[0] <= r_req_tag;
          rd_valid[0] <= 1'b1;
        end else begin
          rd_valid[0] <= 1'b0;
        end // else: !if(i_snoop_resp_valid)
      end // case: SNOOP
    endcase // case (r_state)

    if (!(o_resp_valid & !i_resp_ready)) begin
      for (int i = 1; i < RD_LAT; i++) begin
        rd_valid[i] <= rd_valid[i-1];
        rd_tag[i] <= rd_tag[i-1];
        rd_data[i] <= rd_data[i-1];
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_resp_valid = rd_valid[RD_LAT-1];
assign o_resp_tag = rd_tag[RD_LAT-1];
assign o_resp_data = rd_data[RD_LAT-1];

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

// `ifdef SIMULATION
// generate for (genvar idx=0; idx < SIZE; idx++) begin : ram_loop
//   line_status_t debug_line_status = status[idx];
//   wire [DATA_W-1: 0] debug_ram = ram[idx];
// end
// endgenerate
// `endif // SIMULATION

endmodule  // tb_l2_behavior_ram
