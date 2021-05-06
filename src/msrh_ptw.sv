module msrh_ptw
  import msrh_lsu_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   // Page Table Walk I/O
   tlb_ptw_if.slave ptw_if[1 + msrh_conf_pkg::LSU_INST_NUM],

   // L2 request from L1D
   l2_req_if.master ptw_req,
   l2_resp_if.slave ptw_resp
   );

localparam PTW_PORT_NUM = 1 + msrh_conf_pkg::LSU_INST_NUM;

typedef enum logic [ 1: 0] {
  IDLE = 0,
  REQUEST = 1,
  WAIT = 2
} state_t;

state_t r_state;
logic [$clog2(PG_LEVELS)-1: 0] r_count;

logic [PTW_PORT_NUM-1: 0] w_ptw_valid;
logic [PTW_PORT_NUM-1: 0] w_ptw_accept;
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_satp  [PTW_PORT_NUM];
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_status[PTW_PORT_NUM];
ptw_req_t   w_ptw_req [PTW_PORT_NUM];

ptw_req_t   w_ptw_accepted_req;
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_accepted_satp;
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_accepted_status;

logic                          r_ptw_addr[PPN_W-1: 0];

generate for (genvar p_idx = 0; p_idx < PTW_PORT_NUM; p_idx++) begin : ptw_loop
  assign w_ptw_valid [p_idx] = ptw_if[p_idx].valid;
  assign w_ptw_req   [p_idx] = ptw_if[p_idx].req;
  assign w_ptw_satp  [p_idx] = ptw_if[p_idx].satp;
  assign w_ptw_status[p_idx] = ptw_if[p_idx].statusx;
end
endgenerate

simple_arbiter #(.WIDTH(PTW_PORT_NUM)) u_simple_arbiter (.i_valid(ptw_valid), .o_accept(w_ptw_accept));
bit_oh_or #(.T(ptw_req_t),                     .WORDS(PTW_PORT_NUM)) bit_accepted_ptw_req    (.i_oh(w_ptw_accept), .i_data(w_ptw_req   ), .o_selected(w_ptw_accepted_req   ));
bit_oh_or #(.T(logic[riscv_pkg::XLEN_W-1: 0]), .WORDS(PTW_PORT_NUM)) bit_accepted_ptw_satp   (.i_oh(w_ptw_accept), .i_data(w_ptw_satp  ), .o_selected(w_ptw_accepted_satp  ));
bit_oh_or #(.T(logic[riscv_pkg::XLEN_W-1: 0]), .WORDS(PTW_PORT_NUM)) bit_accepted_ptw_status (.i_oh(w_ptw_accept), .i_data(w_ptw_status), .o_selected(w_ptw_accepted_status));


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= IDLE;
    r_count <= 'h0;
  end else begin
    case (r_state)
      IDLE : begin
        if (w_ptw_accepted_req.valid) begin
          r_state <= REQUEST;
          r_count <= PG_LEVELS - 1;
          r_ptw_addr <= w_ptw_accepted_status[PPN_W-1: 0] +
                        w_ptw_accepted_req.vaddr[PG_IDX_W + (PG_LEVES-1)*VPN_FIELD_W +: VPN_FIELD_W];
        end
      end
      REQUEST : begin
        if (ptw_req.valid & ptw_req.ready) begin
          r_state <= WAIT;
        end
      end
      WAIT : begin
        if (ptw_resp.valid & ptw_resp.ready) begin
          if (r_count == 'h0) begin
            r_state <= IDLE;
          end else begin
            r_state <= WAIT;
          end
        end
      end
    endcase // case (r_state)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign ptw_req.valid           = (r_state == REQUEST);
assign ptw_req.payload.cmd     = M_XRD;
assign ptw_req.payload.addr    = {r_ptw_addr, {PG_IDX_W{1'b0}}};
assign ptw_req.payload.tag     = 'h0;
assign ptw_req.payload.data    = 'h0;
assign ptw_req.payload.byte_en = 'h0;
assign ptw_resp.ready = 1'b1;

endmodule // msrh_ptw
