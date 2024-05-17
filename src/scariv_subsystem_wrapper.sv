// ------------------------------------------------------------------------
// NAME : scariv_subsystem_wrapper
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Subsystem AXI Wrapper
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_subsystem_wrapper
  (
    input  logic                                                        i_clk,
    input  logic                                                        i_reset_n,

    input scariv_pkg::vaddr_t                                           i_const_init_vaddr,

    // L2 request
    output logic                                                          o_l2_req_valid,
    output scariv_lsu_pkg::mem_cmd_t                                      o_l2_req_cmd,
    output logic                   [              riscv_pkg::PADDR_W-1:0] o_l2_req_addr,
    output logic                   [  scariv_lsu_pkg::DCACHE_COLOR_W-1:0] o_l2_req_color,
    output logic                   [  scariv_lsu_pkg::L2_CMD_TAG_W+2-1:0] o_l2_req_tag,
    output logic                   [  scariv_conf_pkg::DCACHE_DATA_W-1:0] o_l2_req_data,
    output logic                   [scariv_conf_pkg::DCACHE_DATA_W/8-1:0] o_l2_req_byte_en,
    input  logic                                                          i_l2_req_ready,

    input  logic                                      i_l2_resp_valid,
    input  logic [scariv_lsu_pkg::L2_CMD_TAG_W+2-1:0] i_l2_resp_tag,
    input  logic [scariv_conf_pkg::DCACHE_DATA_W-1:0] i_l2_resp_data,
    output logic                                      o_l2_resp_ready,

    input logic [ 7: 0] i_interrupts,

    // Snoop Interface
    input logic                      i_snoop_req_valid,
    input scariv_pkg::paddr_t        i_snoop_req_paddr,
    input scariv_lsu_pkg::dc_color_t i_snoop_req_color,

    output logic                                       o_snoop_resp_valid,
    output logic [ scariv_conf_pkg::DCACHE_DATA_W-1:0] o_snoop_resp_data,
    output logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1:0] o_snoop_resp_be
   );

l2_req_if  #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W+2)) w_l2_req ();
l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W+2)) w_l2_resp();

snoop_if w_snoop_if ();


// -------------------
// L2 Interconnection
// -------------------
assign o_l2_req_valid          = w_l2_req.valid;
assign o_l2_req_cmd            = w_l2_req.payload.cmd;
assign o_l2_req_addr           = w_l2_req.payload.addr;
assign o_l2_req_color          = w_l2_req.payload.color;
assign o_l2_req_tag            = w_l2_req.tag        ;
assign o_l2_req_data           = w_l2_req.payload.data;
assign o_l2_req_byte_en        = w_l2_req.payload.byte_en;
assign w_l2_req.ready          = i_l2_req_ready;

assign w_l2_resp.valid        = i_l2_resp_valid;
assign w_l2_resp.tag          = i_l2_resp_tag;
assign w_l2_resp.payload.data = i_l2_resp_data;
assign o_l2_resp_ready        = w_l2_resp.ready;


// ----------------
// Snoop Interface
// ----------------
assign w_snoop_if.req_valid         = i_snoop_req_valid;
assign w_snoop_if.req_payload.paddr = i_snoop_req_paddr;
assign w_snoop_if.req_payload.color = i_snoop_req_color;

assign o_snoop_resp_valid = w_snoop_if.resp_valid;
assign o_snoop_resp_data  = w_snoop_if.resp_payload.data;
assign o_snoop_resp_be    = w_snoop_if.resp_payload.be;

scariv_subsystem
u_scariv_subsystem
(
 .i_clk     (i_clk),
 .i_reset_n (i_reset_n),

 .i_const_init_vaddr (i_const_init_vaddr),

 .l2_req  (w_l2_req ),
 .l2_resp (w_l2_resp),

 .i_interrupts (i_interrupts),

 .snoop_if (w_snoop_if)

 );


endmodule // scariv_subsystem_wrapper
