module msrh_ptw
  import msrh_lsu_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   // Page Table Walk I/O
   tlb_ptw_if.slave ptw_if[1 + msrh_conf_pkg::LSU_INST_NUM],

   // Interface to check LSU L1D
   lsu_access_if.master lsu_access,

   // L2 request from L1D
   l2_req_if.master ptw_req,
   l2_resp_if.slave ptw_resp
   );

localparam PTW_PORT_NUM = 1 + msrh_conf_pkg::LSU_INST_NUM;

typedef enum logic [ 2: 0] {
  IDLE = 0,
  CHECK_L1D = 1,
  RESP_L1D  = 2,
  L2_REQUEST = 3,
  WAIT_L1D_LRQ = 4,
  L2_RESP_WAIT = 5
} state_t;

state_t r_state;
logic [$clog2(riscv_pkg::PG_LEVELS)-1: 0] r_count;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] r_wait_conflicted_lrq_oh;

logic [PTW_PORT_NUM-1: 0]             w_ptw_valid;
logic [PTW_PORT_NUM-1: 0]             w_ptw_accept;
logic [PTW_PORT_NUM-1: 0]             r_ptw_accept;
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_satp  [PTW_PORT_NUM];
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_status[PTW_PORT_NUM];
ptw_req_t   w_ptw_req [PTW_PORT_NUM];

ptw_req_t   w_ptw_accepted_req;
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_accepted_satp;
logic [riscv_pkg::XLEN_W-1: 0] w_ptw_accepted_status;
logic [msrh_lsu_pkg::VPN_W-1: 0] r_ptw_vpn;
logic [riscv_pkg::PADDR_W-1: 0] r_ptw_addr;

logic                          lsu_access_is_leaf;
logic                          lsu_access_bad_pte;
msrh_lsu_pkg::pte_t            lsu_access_pte;

generate for (genvar p_idx = 0; p_idx < PTW_PORT_NUM; p_idx++) begin : ptw_req_loop
  assign w_ptw_valid [p_idx] = ptw_if[p_idx].req.valid;
  assign w_ptw_req   [p_idx] = ptw_if[p_idx].req;
  assign w_ptw_satp  [p_idx] = ptw_if[p_idx].satp;
  assign w_ptw_status[p_idx] = ptw_if[p_idx].status;
end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ptw_accept <= 'h0;
  end else begin
    r_ptw_accept <= r_state == IDLE ? w_ptw_accept : r_ptw_accept;
  end
end

generate for (genvar p_idx = 0; p_idx < PTW_PORT_NUM; p_idx++) begin : ptw_resp_loop
  always_comb begin
    ptw_if[p_idx].resp = 'h0;
    ptw_if[p_idx].req_ready = (r_state == IDLE) & w_ptw_accept[p_idx];
    if (r_ptw_accept[p_idx] | w_ptw_accept[p_idx]) begin
      ptw_if[p_idx].resp.valid       = (((r_state == RESP_L1D) & (lsu_access.status == msrh_lsu_pkg::STATUS_HIT)) |
                                        ((r_state == L2_RESP_WAIT) & ptw_resp.valid & ptw_resp.ready)) &
                                       (lsu_access_is_leaf | lsu_access_bad_pte | (r_count == 'h0)) &
                                       r_ptw_accept[p_idx];
      ptw_if[p_idx].resp.ae          = 1'b0; // if instruction region fault
      ptw_if[p_idx].resp.pte         = lsu_access_pte;   // r_pte;
      ptw_if[p_idx].resp.level       = r_count;
      ptw_if[p_idx].resp.homogeneous = 'h0;   // homogeneous || pageGranularityPMPs;
    end
  end // always_comb
end // block: ptw_resp_loop
endgenerate


simple_arbiter #(.WIDTH(PTW_PORT_NUM)) u_simple_arbiter (.i_valid(w_ptw_valid), .o_accept(w_ptw_accept));
bit_oh_or #(.T(ptw_req_t),                     .WORDS(PTW_PORT_NUM)) bit_accepted_ptw_req    (.i_oh(w_ptw_accept), .i_data(w_ptw_req   ), .o_selected(w_ptw_accepted_req   ));
bit_oh_or #(.T(logic[riscv_pkg::XLEN_W-1: 0]), .WORDS(PTW_PORT_NUM)) bit_accepted_ptw_satp   (.i_oh(w_ptw_accept), .i_data(w_ptw_satp  ), .o_selected(w_ptw_accepted_satp  ));
bit_oh_or #(.T(logic[riscv_pkg::XLEN_W-1: 0]), .WORDS(PTW_PORT_NUM)) bit_accepted_ptw_status (.i_oh(w_ptw_accept), .i_data(w_ptw_status), .o_selected(w_ptw_accepted_status));

assign lsu_access_pte = (r_state == L2_RESP_WAIT) ? msrh_lsu_pkg::pte_t'(ptw_resp.payload.data[riscv_pkg::XLEN_W-1:0]) :
                        msrh_lsu_pkg::pte_t'(lsu_access.data[riscv_pkg::XLEN_W-1:0]);

assign lsu_access_is_leaf = lsu_access_pte.v &
                            (lsu_access_pte.r | lsu_access_pte.w | lsu_access_pte.x);

assign lsu_access_bad_pte = ~lsu_access_pte.v |
                            (~lsu_access_pte.r & lsu_access_pte.w);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= IDLE;
    r_count <= 'h0;
  end else begin
    case (r_state)
      IDLE : begin
        if (w_ptw_accepted_req.valid) begin
          r_state <= CHECK_L1D;
          /* verilator lint_off WIDTH */
          r_count <= riscv_pkg::PG_LEVELS - 'h1;
          r_ptw_vpn <= w_ptw_accepted_req.addr;
          r_ptw_addr <= {w_ptw_accepted_satp[riscv_pkg::PPN_W-1: 0], {PG_IDX_W{1'b0}}} +
                        {{(riscv_pkg::PADDR_W-VPN_FIELD_W-$clog2(riscv_pkg::XLEN_W / 8)){1'b0}},
                         w_ptw_accepted_req.addr[(riscv_pkg::PG_LEVELS-1)*VPN_FIELD_W +: VPN_FIELD_W],
                         {$clog2(riscv_pkg::XLEN_W / 8){1'b0}}};
        end
      end
      CHECK_L1D : begin
        r_state <= RESP_L1D;
      end
      RESP_L1D : begin
        if (lsu_access.resp_valid) begin
          case (lsu_access.status)
            msrh_lsu_pkg::STATUS_HIT : begin
              if (lsu_access_is_leaf || r_count == 'h0) begin
                r_state  <= IDLE;
              end else begin
                r_count  <= r_count - 1;
                r_state  <= CHECK_L1D;
                /* verilator lint_off WIDTH */
                r_ptw_addr <= {lsu_access_pte.ppn, {PG_IDX_W{1'b0}}} +
                              {{(riscv_pkg::PADDR_W-VPN_FIELD_W-$clog2(riscv_pkg::XLEN_W / 8)){1'b0}},
                               r_ptw_vpn[(r_count-'h1)*VPN_FIELD_W +: VPN_FIELD_W],
                               {$clog2(riscv_pkg::XLEN_W / 8){1'b0}}};

              end
            end
            msrh_lsu_pkg::STATUS_MISS : begin
              r_state <= L2_REQUEST;
            end
            msrh_lsu_pkg::STATUS_L1D_CONFLICT : begin
              // L1D port conflict : retry
              r_state <= CHECK_L1D;
            end
            msrh_lsu_pkg::STATUS_LRQ_CONFLICT : begin
              r_state <= WAIT_L1D_LRQ;
              r_wait_conflicted_lrq_oh <= lsu_access.lrq_conflicted_idx_oh;
            end
            default : begin
              $fatal(0, "This state must not to be come");
            end
          endcase // case (lsu_access.status)
        end else begin // if (lsu_access.resp_valid)
          $fatal(0, "lsu_access.resp should be return in one cycle");
        end // else: !if(lsu_access.resp_valid)
      end
      WAIT_L1D_LRQ : begin
        if (lsu_access.conflict_resolve_vld &&
            lsu_access.conflict_resolve_idx_oh == r_wait_conflicted_lrq_oh) begin
          r_state <= CHECK_L1D;
        end
      end
      L2_REQUEST : begin
        if (ptw_req.valid & ptw_req.ready) begin
          r_state <= L2_RESP_WAIT;
        end
      end
      L2_RESP_WAIT : begin
        if (ptw_resp.valid & ptw_resp.ready) begin
          if (lsu_access_is_leaf || r_count == 'h0) begin
            r_state <= IDLE;
          end else if (lsu_access_bad_pte) begin
            r_state <= IDLE;
          end else begin
            r_state <= L2_RESP_WAIT;
          end
        end
      end
      default : begin
        $fatal(0, "This state must not be come\n");
      end
    endcase // case (r_state)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

// L1D check Interface
assign lsu_access.req_valid = (r_state == CHECK_L1D);
assign lsu_access.paddr = r_ptw_addr;
assign lsu_access.size  = riscv_pkg::XLEN_W == 64 ? decoder_lsu_ctrl::SIZE_DW :
                          decoder_lsu_ctrl::SIZE_W;

// PTW to L2 Interface
assign ptw_req.valid           = (r_state == L2_REQUEST);
assign ptw_req.payload.cmd     = M_XRD;
assign ptw_req.payload.addr    = r_ptw_addr;
assign ptw_req.payload.tag     = 'h0;
assign ptw_req.payload.data    = 'h0;
assign ptw_req.payload.byte_en = 'h0;
assign ptw_resp.ready = 1'b1;

endmodule // msrh_ptw
