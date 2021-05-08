module l2c_arbiter_wrapper
  (
/* from ELF Loader */
input  logic                                      i_elf_req_valid,
input  msrh_lsu_pkg::mem_cmd_t                    i_elf_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]             i_elf_req_addr,
input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_elf_req_tag,
input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_elf_req_data,
input  logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] i_elf_req_byte_en,
output logic                                      o_elf_req_ready,

/* from Frontend IC */
input  logic                                      i_ic_req_valid,
input  msrh_lsu_pkg::mem_cmd_t                    i_ic_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]             i_ic_req_addr,
input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_ic_req_tag,
input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_ic_req_data,
input  logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] i_ic_req_byte_en,
output logic                                      o_ic_req_ready,

output logic                                     o_ic_resp_valid,
output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    o_ic_resp_tag,
output logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]  o_ic_resp_data,
input  logic                                     i_ic_resp_ready  ,

/* L1D Interface */
input  logic                                      i_l1d_req_valid,
input  msrh_lsu_pkg::mem_cmd_t                    i_l1d_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]             i_l1d_req_addr,
input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_l1d_req_tag,
input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_l1d_req_data,
input  logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] i_l1d_req_byte_en,
output logic                                      o_l1d_req_ready,

output logic                                     o_l1d_resp_valid,
output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    o_l1d_resp_tag,
output logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]  o_l1d_resp_data,
input  logic                                     i_l1d_resp_ready,

/* PTW Interface */
input  logic                                      i_ptw_req_valid,
input  msrh_lsu_pkg::mem_cmd_t                    i_ptw_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]             i_ptw_req_addr,
input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_ptw_req_tag,
input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_ptw_req_data,
input  logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] i_ptw_req_byte_en,
output logic                                      o_ptw_req_ready,

output logic                                     o_ptw_resp_valid,
output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    o_ptw_resp_tag,
output logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]  o_ptw_resp_data,
input  logic                                     i_ptw_resp_ready,

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


l2_req_if req_if[4]();
l2_req_if req_if_selected();


// elf_if interconnection
assign req_if[0].valid           = i_elf_req_valid;
assign req_if[0].payload.cmd     = i_elf_req_cmd;
assign req_if[0].payload.addr    = i_elf_req_addr;
assign req_if[0].payload.tag     = i_elf_req_tag;
assign req_if[0].payload.data    = i_elf_req_data;
assign req_if[0].payload.byte_en = i_elf_req_byte_en;
assign o_elf_req_ready = req_if[0].ready;

assign o_ic_resp_valid = i_l2_resp_valid;
assign o_ic_resp_tag   = i_l2_resp_tag;
assign o_ic_resp_data  = i_l2_resp_data;
// assign o_l2_resp_ =

// ic_if interconnection
assign req_if[1].valid           = i_ic_req_valid;
assign req_if[1].payload.cmd     = i_ic_req_cmd;
assign req_if[1].payload.addr    = i_ic_req_addr;
assign req_if[1].payload.tag     = i_ic_req_tag;
assign req_if[1].payload.data    = i_ic_req_data;
assign req_if[1].payload.byte_en = i_ic_req_byte_en;
assign o_ic_req_ready = req_if[1].ready;

assign o_ic_resp_valid = i_l2_resp_valid;
assign o_ic_resp_tag   = i_l2_resp_tag;
assign o_ic_resp_data  = i_l2_resp_data;

// l1d_if interconnection
assign req_if[2].valid           = i_l1d_req_valid;
assign req_if[2].payload.cmd     = i_l1d_req_cmd;
assign req_if[2].payload.addr    = i_l1d_req_addr;
assign req_if[2].payload.tag     = i_l1d_req_tag;
assign req_if[2].payload.data    = i_l1d_req_data;
assign req_if[2].payload.byte_en = i_l1d_req_byte_en;
assign o_l1d_req_ready = req_if[2].ready;

assign o_l1d_resp_valid = i_l2_resp_valid;
assign o_l1d_resp_tag   = i_l2_resp_tag;
assign o_l1d_resp_data  = i_l2_resp_data;

// ptw_if interconnection
assign req_if[3].valid           = i_ptw_req_valid;
assign req_if[3].payload.cmd     = i_ptw_req_cmd;
assign req_if[3].payload.addr    = i_ptw_req_addr;
assign req_if[3].payload.tag     = i_ptw_req_tag;
assign req_if[3].payload.data    = i_ptw_req_data;
assign req_if[3].payload.byte_en = i_ptw_req_byte_en;
assign o_ptw_req_ready = req_if[3].ready;

assign o_ptw_resp_valid = i_l2_resp_valid;
assign o_ptw_resp_tag   = i_l2_resp_tag;
assign o_ptw_resp_data  = i_l2_resp_data;

l2_if_arbiter #(.ARB_NUM(4)) u_l2_if_arbiter (.l2_slave_if(req_if), .l2_master_if(req_if_selected));

// output interconnection
assign o_l2_req_valid   = req_if_selected.valid;
assign o_l2_req_cmd     = req_if_selected.payload.cmd;
assign o_l2_req_addr    = req_if_selected.payload.addr;
assign o_l2_req_tag     = req_if_selected.payload.tag;
assign o_l2_req_data    = req_if_selected.payload.data;
assign o_l2_req_byte_en = req_if_selected.payload.byte_en;
assign req_if_selected.ready = i_l2_req_ready;

assign o_l2_resp_ready = 1'b1;

endmodule // l2c_arbiter_wrapper
