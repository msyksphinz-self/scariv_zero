// ------------------------------------------------------------------------
// NAME : SCARIV PLIC
// TYPE : module
// ------------------------------------------------------------------------
// PLIC (Platform Level Interrupt Controller)
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_plic #(
    parameter DATA_W    = 256,
    parameter TAG_W     = 4,
    parameter ADDR_W    = 12,
    parameter BASE_ADDR = 'h5400_0000,
    parameter SIZE      = 'h1000,
    parameter RD_LAT    = 10
) (
   input logic i_clk,
   input logic i_reset_n,

   input  logic                     i_req_valid,
   input  scariv_lsu_pkg::mem_cmd_t i_req_cmd,
   input  logic [  ADDR_W-1:0]      i_req_addr,
   input  logic [   TAG_W-1:0]      i_req_tag,
   input  logic [  DATA_W-1:0]      i_req_data,
   input  logic [DATA_W/8-1:0]      i_req_byte_en,
   output logic                     o_req_ready,

   output logic              o_resp_valid,
   output logic [ TAG_W-1:0] o_resp_tag,
   output logic [DATA_W-1:0] o_resp_data,
   input  logic              i_resp_ready,

   plic_if.master plic_if
);

typedef enum logic [ 1: 0] {
  INIT = 0,
  READ = 1
} plic_state_t;

plic_state_t r_state;
logic w_plic_req_fire;
logic w_plic_resp_fire;
logic [   TAG_W-1:0] r_req_tag;
logic [DATA_W-1: 0]  r_plic_prdata;

logic                 w_plic_penable;
logic                 w_plic_pwrite;
logic [DATA_W/8-1: 0] w_plic_pstrb;
logic [DATA_W-1: 0]   w_plic_prdata;
logic [DATA_W-1: 0]   r_plic_prdata;
logic                 w_plic_pready;


assign w_plic_req_fire = i_req_valid & o_req_ready;

assign o_req_ready = r_state == INIT;

assign o_resp_valid = r_state == READ_RESP;
assign o_resp_tag   = r_req_tag;
assign o_resp_data  = r_plic_prdata;

assign w_plic_resp_fire = w_resp_plic_if.valid & w_resp_plic_if.ready;

assign w_plic_penable = i_req_cmd == scariv_lsu_pkg::M_XWR;
assign w_plic_pwrite  = i_req_cmd == scariv_lsu_pkg::M_XWR;
assign w_plic_pstrb   = i_req_byte_en;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= INIT;
  end else begin
    case (r_state)
      INIT : begin
        if (w_plic_req_fire &
            (i_req_cmd == scariv_lsu_pkg::M_XRD)) begin
          r_state <= READ;
          r_req_tag <= i_req_tag;
        end
      end
      READ_WAIT : begin
        if (w_plic_pready) begin
          r_state <= READ_RESP;
          r_plic_prdata <= w_plic_prdata;
        end
      end
      READ_RESP : begin
        if (w_plic_resp_fire) begin
          r_state <= INIT;
        end
      end
    endcase // case (r_state)
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

apb4_plic_top
  #(
    // AHB Parameters
    .PADDR_SIZE(riscv_pkg::PADDR_W),
    .PDATA_SIZE(scariv_conf_pkg::ICACHE_DATA_W),
    // PLIC Parameters
    .SOURCES           (64),   //Number of interrupt sources
    .TARGETS           ( 4),   //Number of interrupt targets
    .PRIORITIES        ( 8),   //Number of Priority levels
    .MAX_PENDING_COUNT ( 8),   //Max. number of 'pending' events
    .HAS_THRESHOLD     ( 1),   //Is 'threshold' implemented?
    .HAS_CONFIG_REG    ( 1)    //Is the 'configuration' register implemented?
    )
u_plic
  (
   .PCLK    (i_clk),
   .PRESETn (i_reset_n),

   //AHB Slave Interface
   .PSEL    (w_plic_req_fire),
   .PENABLE (w_plic_penable),
   .PADDR   (i_req_addr),
   .PWRITE  (w_plic_pwrite),
   .PSTRB   (w_plic_pstrb),
   .PWDATA  (i_req_data),

   .PRDATA  (w_plic_prdata),
   .PREADY  (w_plic_pready),
   .PSLVERR (),

   .src (i_interrupts),       // Interrupt sources
   .irq (w_plic_if.int_valid)        // Interrupt Requests
   );


endmodule // scariv_plic
