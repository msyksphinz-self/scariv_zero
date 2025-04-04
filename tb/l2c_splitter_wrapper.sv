module l2c_splitter_wrapper
  #(parameter TAG_W = scariv_lsu_pkg::L2_CMD_TAG_W)
(
   /* Input */
   input logic                                        i_req_valid,
   input scariv_lsu_pkg::mem_cmd_t                    i_req_cmd,
   input scariv_pkg::paddr_t                          i_req_addr,
   input logic [TAG_W-1:0]     i_req_tag,
   input scariv_lsu_pkg::dc_data_t                    i_req_data,
   input scariv_lsu_pkg::dc_strb_t                    i_req_byte_en,
   output logic                                       o_req_ready,

   output logic                                      o_resp_valid,
   output logic [TAG_W-1:0]   o_resp_tag,
   output scariv_lsu_pkg::dc_data_t                  o_resp_data,
   input logic                                       i_resp_ready,

   /* BootROM Interface */
   output logic                                        o_bootrom_req_valid,
   output scariv_lsu_pkg::mem_cmd_t                    o_bootrom_req_cmd,
   output scariv_pkg::paddr_t                          o_bootrom_req_addr,
   output logic [TAG_W-1:0]                            o_bootrom_req_tag,
   output scariv_lsu_pkg::dc_data_t                    o_bootrom_req_data,
   output scariv_lsu_pkg::dc_strb_t                    o_bootrom_req_byte_en,
   input  logic                                        i_bootrom_req_ready,

   input  logic                                        i_bootrom_resp_valid,
   input  logic [TAG_W-1:0]                            i_bootrom_resp_tag,
   input  scariv_lsu_pkg::dc_data_t                    i_bootrom_resp_data,
   output logic                                        o_bootrom_resp_ready,

   /* Serial Device */
   output logic                                        o_serial_req_valid,
   output scariv_lsu_pkg::mem_cmd_t                    o_serial_req_cmd,
   output scariv_pkg::paddr_t                          o_serial_req_addr,
   output logic [TAG_W-1:0]                            o_serial_req_tag,
   output scariv_lsu_pkg::dc_data_t                    o_serial_req_data,
   output scariv_lsu_pkg::dc_strb_t                    o_serial_req_byte_en,
   input  logic                                        i_serial_req_ready,

   input  logic                                        i_serial_resp_valid,
   input  logic [TAG_W-1:0]                            i_serial_resp_tag,
   input  scariv_lsu_pkg::dc_data_t                    i_serial_resp_data,
   output logic                                        o_serial_resp_ready,

   /* Kernel Flash */
   output logic                                        o_kernel_req_valid,
   output scariv_lsu_pkg::mem_cmd_t                    o_kernel_req_cmd,
   output scariv_pkg::paddr_t                          o_kernel_req_addr,
   output logic [TAG_W-1:0]                            o_kernel_req_tag,
   output scariv_lsu_pkg::dc_data_t                    o_kernel_req_data,
   output scariv_lsu_pkg::dc_strb_t                    o_kernel_req_byte_en,
   input  logic                                        i_kernel_req_ready,

   input  logic                                        i_kernel_resp_valid,
   input  logic [TAG_W-1:0]                            i_kernel_resp_tag,
   input  scariv_lsu_pkg::dc_data_t                    i_kernel_resp_data,
   output logic                                        o_kernel_resp_ready,

   /* Initrd Flash */
   output logic                                        o_initrd_req_valid,
   output scariv_lsu_pkg::mem_cmd_t                    o_initrd_req_cmd,
   output scariv_pkg::paddr_t                          o_initrd_req_addr,
   output logic [TAG_W-1:0]                            o_initrd_req_tag,
   output scariv_lsu_pkg::dc_data_t                    o_initrd_req_data,
   output scariv_lsu_pkg::dc_strb_t                    o_initrd_req_byte_en,
   input  logic                                        i_initrd_req_ready,

   input  logic                                        i_initrd_resp_valid,
   input  logic [TAG_W-1:0]                            i_initrd_resp_tag,
   input  scariv_lsu_pkg::dc_data_t                    i_initrd_resp_data,
   output logic                                        o_initrd_resp_ready,

   /* L2 Interface */
   output logic                                        o_l2_req_valid,
   output scariv_lsu_pkg::mem_cmd_t                    o_l2_req_cmd,
   output scariv_pkg::paddr_t                          o_l2_req_addr,
   output logic [TAG_W-1:0]                            o_l2_req_tag,
   output scariv_lsu_pkg::dc_data_t                    o_l2_req_data,
   output scariv_lsu_pkg::dc_strb_t                    o_l2_req_byte_en,
   input  logic                                        i_l2_req_ready,

   input  logic                                        i_l2_resp_valid,
   input  logic [TAG_W-1:0]     i_l2_resp_tag,
   input  scariv_lsu_pkg::dc_data_t    i_l2_resp_data,
   output logic                                        o_l2_resp_ready
   );

l2_resp_if #(.TAG_W(TAG_W)) w_resp_if[5]();
l2_resp_if #(.TAG_W(TAG_W)) w_resp_if_selected();

logic                                                w_req_is_bootrom;
logic                                                w_req_is_serial;
logic                                                w_req_is_kernel;
logic                                                w_req_is_initrd;
logic                                                w_req_is_another;
`ifndef LITEX
assign w_req_is_bootrom = {i_req_addr[riscv_pkg::PADDR_W-1: 12], 12'h000}  == 'h0000_1000;
`else // LITEX
assign w_req_is_bootrom = 1'b0;
`endif // LITEX
assign w_req_is_serial  = {i_req_addr[riscv_pkg::PADDR_W-1: 12], 12'h000}  == 'h5400_0000;
assign w_req_is_kernel  = (i_req_addr[riscv_pkg::PADDR_W-1:  0] >= 'h8020_0000) &&
                          (i_req_addr[riscv_pkg::PADDR_W-1:  0] <  'h8220_0000);
assign w_req_is_initrd  = (i_req_addr[riscv_pkg::PADDR_W-1:  0] >= 'hffc8_4a00) &&
                          (i_req_addr[riscv_pkg::PADDR_W-1:  0] <  'hffff_f000);
assign w_req_is_another = !w_req_is_bootrom & !w_req_is_serial & !w_req_is_kernel & !w_req_is_initrd;


// ===========================
// Request from single Master
// ===========================
assign o_bootrom_req_valid   = i_req_valid & w_req_is_bootrom;
assign o_bootrom_req_cmd     = i_req_cmd    ;
assign o_bootrom_req_addr    = i_req_addr   ;
assign o_bootrom_req_tag     = i_req_tag    ;
assign o_bootrom_req_data    = i_req_data   ;
assign o_bootrom_req_byte_en = i_req_byte_en;

assign o_serial_req_valid   = i_req_valid & w_req_is_serial;
assign o_serial_req_cmd     = i_req_cmd    ;
assign o_serial_req_addr    = i_req_addr   ;
assign o_serial_req_tag     = i_req_tag    ;
assign o_serial_req_data    = i_req_data   ;
assign o_serial_req_byte_en = i_req_byte_en;

assign o_kernel_req_valid   = i_req_valid & w_req_is_kernel;
assign o_kernel_req_cmd     = i_req_cmd    ;
assign o_kernel_req_addr    = i_req_addr   ;
assign o_kernel_req_tag     = i_req_tag    ;
assign o_kernel_req_data    = i_req_data   ;
assign o_kernel_req_byte_en = i_req_byte_en;

assign o_initrd_req_valid   = i_req_valid & w_req_is_initrd;
assign o_initrd_req_cmd     = i_req_cmd    ;
assign o_initrd_req_addr    = i_req_addr   ;
assign o_initrd_req_tag     = i_req_tag    ;
assign o_initrd_req_data    = i_req_data   ;
assign o_initrd_req_byte_en = i_req_byte_en;

assign o_l2_req_valid   = i_req_valid & w_req_is_another;
assign o_l2_req_cmd     = i_req_cmd    ;
assign o_l2_req_addr    = i_req_addr   ;
assign o_l2_req_tag     = i_req_tag    ;
assign o_l2_req_data    = i_req_data   ;
assign o_l2_req_byte_en = i_req_byte_en;

assign o_req_ready = w_req_is_bootrom & i_bootrom_req_ready |
                     w_req_is_serial  & i_serial_req_ready  |
                     w_req_is_kernel  & i_kernel_req_ready  |
                     w_req_is_initrd  & i_initrd_req_ready  |
                     w_req_is_another & i_l2_req_ready;

// =============================
// Response from several Slaves
// =============================

// Bootrom interconnection
assign w_resp_if[0].valid        = i_bootrom_resp_valid;
assign w_resp_if[0].tag          = i_bootrom_resp_tag;
assign w_resp_if[0].payload.data = i_bootrom_resp_data;
assign o_bootrom_resp_ready    = w_resp_if[0].ready;

// Serialdevice interconnection
assign w_resp_if[1].valid        = i_serial_resp_valid;
assign w_resp_if[1].tag          = i_serial_resp_tag;
assign w_resp_if[1].payload.data = i_serial_resp_data;
assign o_serial_resp_ready     = w_resp_if[1].ready;

// Kernel interconnection
assign w_resp_if[2].valid        = i_kernel_resp_valid;
assign w_resp_if[2].tag          = i_kernel_resp_tag;
assign w_resp_if[2].payload.data = i_kernel_resp_data;
assign o_kernel_resp_ready     = w_resp_if[2].ready;

// initrd interconnection
assign w_resp_if[3].valid        = i_initrd_resp_valid;
assign w_resp_if[3].tag          = i_initrd_resp_tag;
assign w_resp_if[3].payload.data = i_initrd_resp_data;
assign o_initrd_resp_ready     = w_resp_if[3].ready;

// L2 interconnection
assign w_resp_if[4].valid        = i_l2_resp_valid;
assign w_resp_if[4].tag          = i_l2_resp_tag;
assign w_resp_if[4].payload.data = i_l2_resp_data;
assign o_l2_resp_ready         = w_resp_if[4].ready;

l2_if_resp_arbiter
  #(.ARB_NUM(5)
    )
u_l2_if_arbiter
  (
   .l2_resp_slave_if(w_resp_if),
   .l2_resp_master_if(w_resp_if_selected)
);

assign o_resp_valid = w_resp_if_selected.valid;
assign o_resp_tag   = w_resp_if_selected.tag        ;
assign o_resp_data  = w_resp_if_selected.payload.data;
assign w_resp_if_selected.ready = i_resp_ready;

endmodule // l2c_splitter_wrapper
