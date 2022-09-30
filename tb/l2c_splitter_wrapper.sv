module l2c_splitter_wrapper
  (
   /* Input */
   input logic                                      i_req_valid,
   input msrh_lsu_pkg::mem_cmd_t                    i_req_cmd,
   input msrh_pkg::paddr_t                          i_req_addr,
   input logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_req_tag,
   input msrh_pkg::ic_data_t                        i_req_data,
   input msrh_pkg::ic_strb_t                        i_req_byte_en,
   output logic                                     o_req_ready,

   output logic                                    o_resp_valid,
   output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]   o_resp_tag,
   output msrh_pkg::ic_data_t                      o_resp_data,
   input logic                                     i_resp_ready,

   /* Peripheral Interface */
   output logic                                      o_peripheral_req_valid,
   output msrh_lsu_pkg::mem_cmd_t                    o_peripheral_req_cmd,
   output logic [riscv_pkg::PADDR_W-1:0]             o_peripheral_req_addr,
   output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     o_peripheral_req_tag,
   output logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   o_peripheral_req_data,
   output logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] o_peripheral_req_byte_en,
   input  logic                                      i_peripheral_req_ready,

   input  logic                                      i_peripheral_resp_valid,
   input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_peripheral_resp_tag,
   input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_peripheral_resp_data,
   output logic                                      o_peripheral_resp_ready,

   /* L2 Interface */
   output logic                                      o_l2_req_valid,
   output msrh_lsu_pkg::mem_cmd_t                    o_l2_req_cmd,
   output logic [riscv_pkg::PADDR_W-1:0]             o_l2_req_addr,
   output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     o_l2_req_tag,
   output logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   o_l2_req_data,
   output logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] o_l2_req_byte_en,
   input  logic                                      i_l2_req_ready,

   input  logic                                      i_l2_resp_valid,
   input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_l2_resp_tag,
   input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_l2_resp_data,
   output logic                                      o_l2_resp_ready
   );

l2_resp_if resp_if[2]();
l2_resp_if resp_if_selected();

logic                                                w_req_is_peripheral;
assign w_req_is_peripheral = {i_req_addr[riscv_pkg::PADDR_W-1: 12], 12'h000}  == 'h4000;

// ===========================
// Request from single Master
// ===========================
assign o_peripheral_req_valid   = i_req_valid & w_req_is_peripheral;
assign o_peripheral_req_cmd     = i_req_cmd    ;
assign o_peripheral_req_addr    = i_req_addr   ;
assign o_peripheral_req_tag     = i_req_tag    ;
assign o_peripheral_req_data    = i_req_data   ;
assign o_peripheral_req_byte_en = i_req_byte_en;

assign o_l2_req_valid   = i_req_valid & ~w_req_is_peripheral;
assign o_l2_req_cmd     = i_req_cmd    ;
assign o_l2_req_addr    = i_req_addr   ;
assign o_l2_req_tag     = i_req_tag    ;
assign o_l2_req_data    = i_req_data   ;
assign o_l2_req_byte_en = i_req_byte_en;

// =============================
// Response from several Slaves
// =============================

// Peripheral interconnection
assign resp_if[0].valid        = i_peripheral_resp_valid;
assign resp_if[0].payload.tag  = i_peripheral_resp_tag;
assign resp_if[0].payload.data = i_peripheral_resp_data;
assign o_peripheral_resp_ready = resp_if[0].ready;

// L2 interconnection
assign resp_if[1].valid        = i_l2_resp_valid;
assign resp_if[1].payload.tag  = i_l2_resp_tag;
assign resp_if[1].payload.data = i_l2_resp_data;
assign o_l2_resp_ready         = resp_if[1].ready;

l2_if_resp_arbiter #(.ARB_NUM(2)) u_l2_if_arbiter (.l2_resp_slave_if(resp_if), .l2_resp_master_if(resp_if_selected));

assign o_resp_valid = resp_if_selected.valid;
assign o_resp_tag   = resp_if_selected.payload.tag;
assign o_resp_data  = resp_if_selected.payload.data;
assign resp_if_selected.ready = i_resp_ready;

endmodule // l2c_splitter_wrapper
