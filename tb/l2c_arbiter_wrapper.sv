module l2c_arbiter_wrapper
  (
/* from ELF Loader */
input  logic                                      i_elf_req_valid,
input  msrh_lsu_pkg::mem_cmd_t                    i_elf_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]             i_elf_req_addr,
input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_elf_req_tag,
input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_elf_req_data,
input  logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] i_elf_req_byte_en,
output logic                                     o_elf_req_ready,

/* from Frontend IC */
input  logic                                      i_ic_req_valid,
input  msrh_lsu_pkg::mem_cmd_t                    i_ic_req_cmd,
input  logic [riscv_pkg::PADDR_W-1:0]             i_ic_req_addr,
input  logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]     i_ic_req_tag,
input  logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   i_ic_req_data,
input  logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] i_ic_req_byte_en,
output logic                                      i_ic_req_ready,

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
   ),



endmodule // l2c_arbiter_wrapper
