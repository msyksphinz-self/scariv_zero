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
    input  scariv_lsu_pkg::mem_cmd_t                i_req_cmd,
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
    input logic [ scariv_conf_pkg::DCACHE_DATA_W-1:0] i_snoop_resp_data,
    input logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1:0] i_snoop_resp_be
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

typedef struct packed {
  logic [ TAG_W-1:0] tag  ;
  logic [DATA_W-1:0] data ;
  logic [ 3: 0]      sim_timer;
} rd_data_t;

rd_data_t rd_queue[$];
rd_data_t rd_queue_init;
rd_data_t rd_queue_ram;

logic [riscv_pkg::PADDR_W-1:0] r_req_paddr_pos;
logic                [ TAG_W-1:0] r_req_tag;

always_comb begin
  rd_queue_init.data      = ram.exists(actual_line_pos) ? ram[actual_line_pos] : 'h0;
  rd_queue_init.tag       = i_req_tag;
  rd_queue_init.sim_timer = 10;
end

generate for (genvar byte_idx = 0; byte_idx < DATA_W / 8; byte_idx++) begin
  always_comb begin
    rd_queue_ram.data[byte_idx*8+:8] = i_snoop_resp_be[byte_idx] ? i_snoop_resp_data[byte_idx*8+:8] :
                                       ram[r_req_paddr_pos][byte_idx*8+:8];
  end
end endgenerate
assign rd_queue_ram.tag       = r_req_tag;
assign rd_queue_ram.sim_timer = 10;

typedef enum logic [0:0] {
   IDLE = 0,
   SNOOP = 1
} state_t;

state_t r_state;

assign o_req_ready = (r_state == IDLE) |
                     i_req_valid & (i_req_cmd == scariv_lsu_pkg::M_XWR);
assign req_fire = i_req_valid & o_req_ready;
/* verilator lint_off WIDTH */
assign actual_addr = i_req_addr /* - BASE_ADDR */;
assign actual_line_pos = actual_addr >> $clog2(DATA_W / 8);

line_status_t  actual_line_status;
always_comb begin
  actual_line_status = status[actual_line_pos];
end

`ifdef SIMULATION
localparam DEBUG_LINE_SIZE = 128;
line_status_t [DEBUG_LINE_SIZE-1: 0] sim_line_status_set;
generate for (genvar i = 0; i < DEBUG_LINE_SIZE; i++) begin
  always_comb begin
    sim_line_status_set[i] = status[(actual_line_pos & ~(DEBUG_LINE_SIZE-1)) + i];
  end
end endgenerate
`endif // SIMULATION

// PMA Memory Map
logic                       w_map_hit;
scariv_lsu_pkg::map_attr_t  w_map_attributes;
pma_map
  u_pma_map
(
 .i_pa      (actual_addr),
 .o_map_hit (w_map_hit),
 .o_map_attr(w_map_attributes)
 );


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= IDLE;
    o_snoop_req_valid <= 1'b0;
    o_snoop_req_paddr <= 'h0;
    r_req_paddr_pos <= 'h0;
    r_req_tag <= 'h0;
  end else begin
    if (req_fire && i_req_cmd == scariv_lsu_pkg::M_XWR) begin
      if ((status.exists(actual_line_pos) ? status[actual_line_pos] : ST_INIT) == ST_GIVEN) begin
        status[actual_line_pos] = ST_INIT;
      end
      // $display("%t write(%x): line update %08x status[%08x] = %d", $time, i_req_tag, actual_line_pos, actual_line_pos, status[actual_line_pos]);
      for (int byte_idx = 0; byte_idx < DATA_W / 8; byte_idx++) begin
        if (i_req_byte_en[byte_idx]) begin
          ram[actual_line_pos][byte_idx*8+:8] = i_req_data[byte_idx*8+:8];
        end
      end
    end

    // Read request
    case(r_state)
      IDLE: begin
        if (req_fire && i_req_cmd == scariv_lsu_pkg::M_XRD) begin
          // $display("%t read (%x): data read %08x, status[%08x]=%d", $time, i_req_tag, actual_addr, actual_line_pos, status[actual_line_pos]);
          if ((status.exists(actual_line_pos) ? status[actual_line_pos] : ST_INIT) == ST_INIT) begin
            if (w_map_hit & w_map_attributes.c &
                (i_req_tag[TAG_W-1 -: 2] == scariv_lsu_pkg::L2_UPPER_TAG_RD_L1D)) begin
              status[actual_line_pos] = ST_GIVEN;
            end
            rd_queue.push_back(rd_queue_init);
          end else begin
            r_state <= SNOOP;
            o_snoop_req_valid <= 1'b1;
            o_snoop_req_paddr <= i_req_addr;
            r_req_paddr_pos <= actual_line_pos;
            r_req_tag <= i_req_tag;
          end // else: !if((status.exists(actual_line_pos) ? status[actual_line_pos] : ST_INIT) == ST_INIT)
        end // if (req_fire && i_req_cmd == scariv_lsu_pkg::M_XRD)
      end // case: IDLE
      SNOOP : begin
        o_snoop_req_valid <= 1'b0;
        o_snoop_req_paddr <= 'h0;
        if (i_snoop_resp_valid) begin
          r_state <= IDLE;
          if (r_req_tag[TAG_W-1 -: 2] != scariv_lsu_pkg::L2_UPPER_TAG_RD_L1D) begin
            status[r_req_paddr_pos] = ST_INIT;
          end
          for (int byte_idx = 0; byte_idx < DATA_W / 8; byte_idx++) begin
            if (i_snoop_resp_be[byte_idx]) begin
              ram[r_req_paddr_pos][byte_idx*8+:8] = i_snoop_resp_data[byte_idx*8+:8];
            end
          end
          rd_queue.push_back(rd_queue_ram);
        end // else: !if(i_snoop_resp_valid)
      end // case: SNOOP
    endcase // case (r_state)

    for (int i = 0; i < rd_queue.size(); i++) begin
      if (rd_queue[i].sim_timer > 0) begin
        rd_queue[i].sim_timer = rd_queue[i].sim_timer - 1;
      end
    end
    if (rd_queue.size() > 0) begin
      if ((rd_queue[0].sim_timer == 0) & i_resp_ready) begin
        rd_queue.pop_front();
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

always_comb begin
  o_resp_valid = rd_queue.size() > 0 ? rd_queue[0].sim_timer == 'h0 : 1'b0;
  o_resp_tag   = rd_queue.size() > 0 ? rd_queue[0].tag              : 'h0;
  o_resp_data  = rd_queue.size() > 0 ? rd_queue[0].data             : 'h0;
end

// assign sim_rd_data_front.sim_timer = rd_queue[0].sim_timer;
// assign sim_rd_data_front.tag       = rd_queue[0].tag;
// assign sim_rd_data_front.data      = rd_queue[0].data;

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
