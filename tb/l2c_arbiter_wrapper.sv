module l2c_arbiter_wrapper
  (
/* from ELF Loader */
input  logic                                        i_elf_req_valid,
input  scariv_lsu_pkg::mem_cmd_t                    i_elf_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]               i_elf_req_addr,
input  logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]     i_elf_req_tag,
input  logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   i_elf_req_data,
input  logic [scariv_conf_pkg::ICACHE_DATA_W/8-1:0] i_elf_req_byte_en,
output logic                                        o_elf_req_ready,

/* from Frontend IC */
input  logic                                        i_ss_req_valid,
input  scariv_lsu_pkg::mem_cmd_t                    i_ss_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]               i_ss_req_addr,
input  logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]     i_ss_req_tag,
input  logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   i_ss_req_data,
input  logic [scariv_conf_pkg::ICACHE_DATA_W/8-1:0] i_ss_req_byte_en,
output logic                                        o_ss_req_ready,

output logic                                       o_ss_resp_valid,
output logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    o_ss_resp_tag,
output logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]  o_ss_resp_data,
input  logic                                       i_ss_resp_ready  ,

/* L2 Interface */
output logic                                        o_l2_req_valid,
output scariv_lsu_pkg::mem_cmd_t                    o_l2_req_cmd,
output logic [riscv_pkg::PADDR_W-1:0]               o_l2_req_addr,
output logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]     o_l2_req_tag,
output logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   o_l2_req_data,
output logic [scariv_conf_pkg::ICACHE_DATA_W/8-1:0] o_l2_req_byte_en,
input  logic                                        i_l2_req_ready,

input  logic                                        i_l2_resp_valid,
input  logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]     i_l2_resp_tag,
input  logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   i_l2_resp_data,
output logic                                        o_l2_resp_ready
   );


l2_req_if req_if[2]();
l2_req_if req_if_selected();


// elf_if interconnection
assign req_if[0].valid           = i_elf_req_valid;
assign req_if[0].payload.cmd     = i_elf_req_cmd;
assign req_if[0].payload.addr    = i_elf_req_addr;
assign req_if[0].payload.tag     = i_elf_req_tag;
assign req_if[0].payload.data    = i_elf_req_data;
assign req_if[0].payload.byte_en = i_elf_req_byte_en;
assign o_elf_req_ready = req_if[0].ready;

// ic_if interconnection
assign req_if[1].valid           = i_ss_req_valid;
assign req_if[1].payload.cmd     = i_ss_req_cmd;
assign req_if[1].payload.addr    = i_ss_req_addr;
assign req_if[1].payload.tag     = i_ss_req_tag;
assign req_if[1].payload.data    = i_ss_req_data;
assign req_if[1].payload.byte_en = i_ss_req_byte_en;
assign o_ss_req_ready = req_if[1].ready;

assign o_ss_resp_valid = i_l2_resp_valid;
assign o_ss_resp_tag   = i_l2_resp_tag;
assign o_ss_resp_data  = i_l2_resp_data;

l2_if_arbiter #(.ARB_NUM(2)) u_l2_if_arbiter (.l2_req_slave_if(req_if), .l2_req_master_if(req_if_selected));

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
