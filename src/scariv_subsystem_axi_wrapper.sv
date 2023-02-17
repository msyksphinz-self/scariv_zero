module scariv_subsystem_axi_wrapper
  (
   input logic   i_clk,
   input logic   i_reset_n,

   output logic                               axi_if_aw_valid,
   input  logic                               axi_if_aw_ready,
   output logic                               axi_if_aw_last,
   output scariv_pkg::paddr_t                 axi_if_aw_addr,
   logic [1:0]                                axi_if_aw_burst,
   logic [7:0]                                axi_if_aw_len,
   logic [2:0]                                axi_if_aw_size,
   logic                                      axi_if_aw_lock,
   logic [2:0]                                axi_if_aw_prot,
   logic [3:0]                                axi_if_aw_cache,
   logic [3:0]                                axi_if_aw_qos,
   logic [3:0]                                axi_if_aw_region,
   logic [scariv_lsu_pkg::L2_CMD_TAG_W+2-1:0] axi_if_aw_id,

   output logic                     axi_if_w_valid,
   input  logic                     axi_if_w_ready,
   output logic                     axi_if_w_last,
   output scariv_pkg::ic_data_t     axi_if_w_data,
   output scariv_pkg::ic_strb_t     axi_if_w_strb,

   input  logic                                      axi_if_b_valid,
   output logic                                      axi_if_b_ready,
   input  logic [1:0]                                axi_if_b_resp,
   input  logic [scariv_lsu_pkg::L2_CMD_TAG_W+2-1:0] axi_if_b_id,

   output logic                                        axi_if_ar_valid,
   input  logic                                        axi_if_ar_ready,
   output logic                                        axi_if_ar_last,
   output scariv_pkg::paddr_t                          axi_if_ar_addr,
   output logic [1:0]                                  axi_if_ar_burst,
   output logic [7:0]                                  axi_if_ar_len,
   output logic [2:0]                                  axi_if_ar_size,
   output logic                                        axi_if_ar_lock,
   output logic [2:0]                                  axi_if_ar_prot,
   output logic [3:0]                                  axi_if_ar_cache,
   output logic [3:0]                                  axi_if_ar_qos,
   output logic [3:0]                                  axi_if_ar_region,
   output logic [scariv_lsu_pkg::L2_CMD_TAG_W+2-1:0]   axi_if_ar_id,

   input logic                                      axi_if_r_valid,
   output logic                                     axi_if_r_ready,
   input logic                                      axi_if_r_last,
   input logic [1:0]                                axi_if_r_resp,
   input scariv_pkg::ic_data_t                      axi_if_r_data,
   input logic [scariv_lsu_pkg::L2_CMD_TAG_W+2-1:0] axi_if_r_id,

   // External Interrupts
   input logic [ 7: 0] i_interrupts
);



l2_req_if  #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W+2)) w_l2_req ();
l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W+2)) w_l2_resp();

snoop_if w_snoop_if ();

typedef enum logic {
  IDLE = 0,
  WR_WAIT = 1
} state_t;

state_t r_state;
scariv_lsu_pkg::l2_req_t r_l2_payload;
logic [scariv_lsu_pkg::L2_CMD_TAG_W+2-1:0] r_l2_tag;

logic w_wr_valid;
logic w_rd_valid;
assign w_wr_valid = (r_state == WR_WAIT) & (r_l2_payload.cmd == scariv_lsu_pkg::M_XWR);
assign w_rd_valid = w_l2_req.valid & (w_l2_req.payload.cmd == scariv_lsu_pkg::M_XRD);

logic w_aw_fire;
logic w_w_fire;
logic r_aw_fire_hold;
logic r_w_fire_hold;
assign w_aw_fire = axi_if_aw_valid & axi_if_aw_ready;
assign w_w_fire  = axi_if_w_valid  & axi_if_w_ready;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= IDLE;
    r_aw_fire_hold <= 1'b0;
    r_w_fire_hold  <= 1'b0;
  end else begin
    case (r_state)
      IDLE : begin
        if (w_l2_req.valid &
            (w_l2_req.payload.cmd == scariv_lsu_pkg::M_XWR)) begin
          r_state <= WR_WAIT;
          r_l2_payload <= w_l2_req.payload;
          r_l2_tag     <= w_l2_req.tag;
        end
      end
      WR_WAIT : begin
        r_aw_fire_hold <= r_aw_fire_hold | w_aw_fire;
        r_w_fire_hold  <= r_w_fire_hold  | w_w_fire;
        if (r_aw_fire_hold & r_w_fire_hold) begin
          r_state <= IDLE;
          r_aw_fire_hold <= 1'b0;
          r_w_fire_hold  <= 1'b0;
        end
      end
    endcase // case (r_state)
  end
end // always_ff @ (posedge i_clk, i_reset_n)


// -------------------
// L2 Interconnection
// -------------------
assign axi_if_aw_valid  = w_wr_valid & ~r_aw_fire_hold;
assign axi_if_aw_addr   = {r_l2_payload.addr[riscv_pkg::PADDR_W-1:$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)],
                           {$clog2(scariv_conf_pkg::ICACHE_DATA_W/8){1'b0}}};
assign axi_if_aw_id     = r_l2_tag;
assign axi_if_aw_last   = 1'b1;
assign axi_if_aw_burst  = 2'b0;
assign axi_if_aw_len    = 8'h0;
assign axi_if_aw_size   = 3'b100;
assign axi_if_aw_lock   = 1'b0;
assign axi_if_aw_prot   = 1'b0;
assign axi_if_aw_cache  = 1'b0;
assign axi_if_aw_qos    = 1'b0;
assign axi_if_aw_region = 1'b0;

assign axi_if_w_valid = w_wr_valid & ~r_w_fire_hold;
assign axi_if_w_last  = 1'b1;
assign axi_if_w_data  = r_l2_payload.data    << {r_l2_payload.addr[riscv_pkg::PADDR_W-1:$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)], 3'b000};
assign axi_if_w_strb  = r_l2_payload.byte_en <<  r_l2_payload.addr[riscv_pkg::PADDR_W-1:$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)];

assign axi_if_b_ready = 1'b1;

assign axi_if_ar_valid  = w_rd_valid;
assign axi_if_ar_last   = 1'b1;
assign axi_if_ar_addr   = w_l2_req.payload.addr;
assign axi_if_ar_burst  = 2'b00;
assign axi_if_ar_len    = 8'h0;
assign axi_if_ar_size   = 3'b100;
assign axi_if_ar_lock   = 1'b0;
assign axi_if_ar_prot   = 1'b0;
assign axi_if_ar_cache  = 1'b0;
assign axi_if_ar_qos    = 1'b0;
assign axi_if_ar_region = 1'b0;
assign axi_if_ar_id     = w_l2_req.tag;

assign axi_if_r_ready         = 1'b1;
assign w_l2_resp.valid        = axi_if_r_valid;
assign w_l2_resp.tag          = axi_if_r_id;
assign w_l2_resp.payload.data = axi_if_r_data;

assign w_l2_req.ready = (r_state == IDLE) & (w_rd_valid ? axi_if_ar_ready : 1'b1);

// // ----------------
// // Snoop Interface
// // ----------------
// assign w_snoop_if.req_valid         = i_snoop_req_valid;
// assign w_snoop_if.req_payload.paddr = i_snoop_req_paddr;
//
// assign o_snoop_resp_valid = w_snoop_if.resp_valid;
// assign o_snoop_resp_data  = w_snoop_if.resp_payload.data;
// assign o_snoop_resp_be    = w_snoop_if.resp_payload.be;

scariv_subsystem
u_scariv_subsystem
(
 .i_clk     (i_clk),
 .i_reset_n (i_reset_n),

 .l2_req  (w_l2_req ),
 .l2_resp (w_l2_resp),

 .i_interrupts (i_interrupts),

 .snoop_if (w_snoop_if)

 );

endmodule // scariv_subsystem_axi
