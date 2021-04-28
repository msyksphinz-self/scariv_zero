module tlb
 #(
    parameter USING_VM = 1'b1
 )
(
 input logic  i_clk,
 input logic  i_reset_n,

 input        sfence_t i_sfence,

 input        msrh_lsu_pkg::tlb_req_t i_tlb_req,
 output logic o_tlb_ready,
 output       msrh_lsu_pkg::tlb_resp_t o_tlb_resp,

              // Page Table Walk I/O
              msrh_lsu_pkg::tlbptw_if ptw_if,
 output logic o_tlb_update
);

localparam PG_LEVELS = 3;
localparam VPN_W = riscv_pkg::VADDR_W - PG_LEVELS;
localparam PG_IDX_W = 12;
localparam PG_LEVEL_W = 10 - $clog2(riscv_pkg::XLEN_W / 32);
localparam SECTOR_NUM = 4;

typedef struct packed {
  logic [PPN_W-1: 0] ppn;
  logic              u ;
  logic              g ;
  logic              ae;
  logic              sw;
  logic              sx;
  logic              sr;
  logic              pw;
  logic              px;
  logic              pr;
  logic              pal;
  logic              paa;
  logic              eff;
  logic              c;
  logic              fragmented_superpage;
} tlb_entry_data_t;

typedef struct packed {
  logic              valid;
  logic [1: 0]       level;
  logic [VPN_W-1: 0] tag;
  tlb_entry_data_t   data;
} tlb_entry_t;

typedef enum logic [1:0] {
  ST_READY           = 0,
  ST_REQUEST         = 1,
  ST_WAIT            = 2,
  ST_WAIT_INVALIDATE = 3
} tlb_state_t;

tlb_state_t r_state;

tlb_entry_t w_sectored_entries[TLB_ENTRIES];
tlb_entry_t w_superpage_entries;
tlb_entry_t w_special_entry;
logic [riscv_pkg::VADDR_W-1: PG_IDX_W] w_vpn;
logic                                  w_priv_s;
logic                                  w_priv_uses_vm;
logic                                  w_vm_enabled;
logic [7: 0]                           w_hit_vector;

logic [TLB_ENTRIES-1: 0]               w_is_hit;

generate for (genvar t_idx = 0; t_idx < TLB_ENTRIES; t_idx++) begin : tlb_loop
  logic w_is_hit;
  logic [PG_LEVEL-1: 0] w_tag_match;
  logic                   sector_idx;
  logic                   sector_tag_match;

  assign sector_idx = w_vpn[$clog2(SECTOR_NUM)-1: 0];
  assign sector_tag_match = w_entries[t_idx].tag[VPN_W-1: $clog2(SECTOR_NUM)] ==
                            w_vpn[VPN_W-1: $clog2(SECTOR_NUM)];

  for (genvar lvl_idx = 0; lvl_idx < PG_LEVEL; lvl_idx++) begin : lvl_loop
    localparam base = VPN_W - (lvl_idx + 1) * PG_LEVEL_W;
    localparam ignore = (level < lvl_idx) || (SUPERPAGEONLY && lvl_idx == PG_LEVELS-1);
    assign w_tag_match[lvl_idx] = ignore || tag[base +: PG_LEVEL_W] == w_vpn[base :+ PG_LEVEL_W];
  end
  assign w_is_hit = (SUPER_PAGE && msrh_confg::USING_VM) ? |w_tag_match :
                    w_entries[t_idx].valid[sector_idx] & sector_tag_match;


end
endgenerate

assign w_vpn = i_tlb_req.vaddr[riscv_pkg::VADDR_W-1: PG_IDX_W];

assign o_tlb_ready = (r_state === ST_READY);

generate if (msrh_conf_pkg::USING_VM) begin : use_vm
  case (r_state)
    ST_READY : begin
      if (i_tlb_req.valid & o_tlb_ready & w_tlb_miss) begin
        r_state <= ST_REQUEST;
      end
    end
    ST_REQUEST : begin
      if (i_kill) begin
        r_state <= ST_READY;
      end else if (ptw_if.ready) begin
        if (i_sfence.valid) begin
          r_state <=  ST_WAIT_INVALIDATE;
        end else begin
          r_state <= ST_WAIT;
        end
      end else if (sfence) begin
        r_state <= ST_READY;
      end
    end
    ST_WAIT : begin
      if (i_sfence.valid) begin
        r_state <= ST_WAIT_INVALIDATE;
      end
    end
    ST_INVALIDATE : begin
      if (ptw_if.resp.valid) begin
        r_state <= ST_READY;
      end
    end
  endcase // case (r_state)
end
endgenerate

// ------------------
// Response of TLB
// ------------------

assign o_tlb_resp.pf.ld        = (w_bad_va && cmd_read) || (pf_ld_array & hits).orR;
assign o_tlb_resp.pf.st        = (w_bad_va && cmd_write_perms) || (pf_st_array & hits).orR;
assign o_tlb_resp.pf.inst      = w_bad_va || (pf_inst_array & hits).orR;
assign o_tlb_resp.ae.ld        = ae_ld_array & |hits;
assign o_tlb_resp.ae.st        = ae_st_array & |hits;
assign o_tlb_resp.ae.inst      = ~px_array   & |hits;
assign o_tlb_resp.ma.ld        = ma_ld_array & |hits;
assign o_tlb_resp.ma.st        = ma_st_array & |hits;
assign o_tlb_resp.ma.inst      = 1'b0 // this is up to the pipeline to figure out
assign o_tlb_resp.cacheable    = (c_array & hits).orR;
assign o_tlb_resp.must_alloc   = (must_alloc_array & hits).orR;
assign o_tlb_resp.prefetchable = (prefetchable_array & hits).orR && edge.manager.managers.forall(m => !m.supportsAcquireB || m.supportsHint).B;
assign o_tlb_resp.miss         = do_refill || tlb_miss || multipleHits;
assign o_tlb_resp.paddr        = {ppn, i_tlb_req.vaddr[PG_IDXW-1: 0]};

assign o_tlb_update = 1'b0;

endmodule
