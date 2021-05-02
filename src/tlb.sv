module tlb
  import msrh_lsu_pkg::*;
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

 input msrh_pkg::prv_t                i_status_priv,
 input logic [riscv_pkg::XLEN_W-1: 0] i_csr_satp,

 // Page Table Walk I/O
 tlb_ptw_if.master ptw_if,
 output logic o_tlb_update
);

localparam TLB_ENTRIES = 8;
localparam TLB_SUPERPAGE_ENTRIES = 4;

typedef struct packed {
  logic [riscv_pkg::PPN_W-1: 0] ppn;
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
tlb_entry_t w_superpage_entries[TLB_SUPERPAGE_ENTRIES];
tlb_entry_t w_special_entry;
logic [riscv_pkg::VADDR_W-1: PG_IDX_W] w_vpn;
logic                                  w_priv_s;
logic                                  w_vm_enabled;
logic                                  w_bad_va;
logic                                  w_misaligned;

logic [TLB_ENTRIES-1: 0]               w_is_hit;

generate for (genvar t_idx = 0; t_idx < TLB_ENTRIES; t_idx++) begin : tlb_loop
  logic w_is_hit;
  logic [PG_LEVEL-1: 0] w_tag_match;
  logic                 sector_idx;
  logic                 sector_tag_match;

  assign sector_idx = w_vpn[$clog2(SECTOR_NUM)-1: 0];
  assign sector_tag_match = w_entries[t_idx].tag[VPN_W-1: $clog2(SECTOR_NUM)] ==
                            w_vpn[VPN_W-1: $clog2(SECTOR_NUM)];

  for (genvar lvl_idx = 0; lvl_idx < PG_LEVEL; lvl_idx++) begin : lvl_loop
    localparam base = VPN_W - (lvl_idx + 1) * PG_LEVEL_W;
    localparam ignore = (level < lvl_idx) || (SUPERPAGEONLY && lvl_idx == PG_LEVELS-1);
    assign w_tag_match[lvl_idx] = ignore || tag[base +: PG_LEVEL_W] == w_vpn[base +: PG_LEVEL_W];
  end
  assign w_is_hit = (SUPER_PAGE && msrh_conf_pkg::USING_VM) ? |w_tag_match :
                    w_entries[t_idx].valid[sector_idx] & sector_tag_match;
end
endgenerate

assign w_vpn = i_tlb_req.vaddr[riscv_pkg::VADDR_W-1: PG_IDX_W];

assign o_tlb_ready = (r_state === ST_READY);
assign w_priv_uses_vm = i_status_priv <= msrh_pkg::PRV_U;
assign w_vm_enabled = msrh_conf_pkg::USING_VM &
                      (i_csr_satp[riscv_pkg::XLEN_W-1 -: 2] != 'h0) &
                      w_priv_uses_vm &
                      !i_tlb_req.passthrough;

generate if (msrh_conf_pkg::USING_VM) begin : use_vm
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_state <= ST_READY;
    end else begin
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
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end
endgenerate


assign w_bad_va     = 1'b0;
assign w_misaligned = i_tlb_req.vaddr & ((1 << i_tlb_req.size) - 1);

logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_ptw_ae_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_priv_rw_ok;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_priv_x_ok;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_r_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_w_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_x_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_pr_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_pw_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_px_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_eff_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_c_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_paa_array
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_pal_array;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_paa_array_if_cached;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_pal_array_if_cached;
logic [1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES-1: 0] w_prefetchable_array;

generate for (genvar e_idx = 0; e_idx < 1 + TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES; e_idx++) begin : elem_loop
  if (e_idx < TLB_ENTRIES) begin : normal_entries
    assign w_ptw_ae_array[e_idx] = sectoroed_entries[e_idx].ae;
    assign w_priv_rw_ok  [e_idx] = !priv_s || io.ptw.status.sum ? sectoroed_entries[e_idx].u : 'h0 |
                                   priv_s ? ~sectoroed_entries[e_idx].u : 'h0;
    assign w_priv_x_ok   [e_idx] = priv_s ? ~sectoroed_entries[e_idx].u : sectoroed_entries[e_idx].u;
    assign w_r_array     [e_idx] = priv_rw_ok & (sectoroed_entries[e_idx].sr) | (io.ptw.status.mxr ? sectoroed_entries[e_idx].sx, 'h0);
assign w_w_array     [e_idx] = {1'b1, priv_rw_ok & sectoroed_entries[e_idx].sw)))
assign w_x_array     [e_idx] = {1'b1, priv_x_ok  & sectoroed_entries[e_idx].sx)))
assign w_pr_array    [e_idx] = {nPhysicalEntries{prot_r  },  normal_sectoroed_entries[e_idx].pr)) & ~ptw_ae_array)
assign w_pw_array    [e_idx] = {nPhysicalEntries{prot_w  },  normal_sectoroed_entries[e_idx].pw)) & ~ptw_ae_array)
assign w_px_array    [e_idx] = {nPhysicalEntries{prot_x  },  normal_sectoroed_entries[e_idx].px)) & ~ptw_ae_array)
assign w_eff_array   [e_idx] = {nPhysicalEntries{prot_eff},  normal_sectoroed_entries[e_idx].eff)))
assign w_c_array     [e_idx] = {nPhysicalEntries{cacheable}, normal_sectoroed_entries[e_idx].c)))
assign w_paa_array   [e_idx] = {nPhysicalEntries{prot_aa },  normal_sectoroed_entries[e_idx].paa)))
assign w_pal_array   [e_idx] = {nPhysicalEntries{prot_al },  normal_sectoroed_entries[e_idx].pal)))
assign w_paa_array_if_cached = paa_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_pal_array_if_cached = pal_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_prefetchable_array  = {(cacheable && homogeneous) << (nPhysicalEntries-1), normal_sectoroed_entries[e_idx].c)))
  end else if (e_idx < TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES) begin : superpage_entries
assign w_ptw_ae_array = {1'b0, entries.map(_.ae)))
assign w_priv_rw_ok   = !priv_s || io.ptw.status.sum ? entries.map(_.u), 0.U) | Mux(priv_s, ~entries.map(_.u) : 'h0;
assign w_priv_x_ok    = priv_s ? ~entries.map(_.u) : entries.map(_.u));
assign w_r_array      = {1'b1, priv_rw_ok & (entries.map(_.sr) | Mux(io.ptw.status.mxr, entries.map(_.sx), 0.U))))
assign w_w_array      = {1'b1, priv_rw_ok & entries.map(_.sw)))
assign w_x_array      = {1'b1, priv_x_ok  & entries.map(_.sx)))
assign w_pr_array     = {nPhysicalEntries{prot_r  },  normal_entries.map(_.pr)) & ~ptw_ae_array)
assign w_pw_array     = {nPhysicalEntries{prot_w  },  normal_entries.map(_.pw)) & ~ptw_ae_array)
assign w_px_array     = {nPhysicalEntries{prot_x  },  normal_entries.map(_.px)) & ~ptw_ae_array)
assign w_eff_array    = {nPhysicalEntries{prot_eff},  normal_entries.map(_.eff)))
assign w_c_array      = {nPhysicalEntries{cacheable}, normal_entries.map(_.c)))
assign w_paa_array    = {nPhysicalEntries{prot_aa },  normal_entries.map(_.paa)))
assign w_pal_array    = {nPhysicalEntries{prot_al },  normal_entries.map(_.pal)))
assign w_paa_array_if_cached = paa_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_pal_array_if_cached = pal_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_prefetchable_array  = {(cacheable && homogeneous) << (nPhysicalEntries-1), normal_entries.map(_.c)))
  end else if (e_idx < TLB_SUPERPAGE_ENTRIES + TLB_ENTRIES + 1) begin : superpage_entries
assign w_ptw_ae_array = {1'b0, entries.map(_.ae)))
assign w_priv_rw_ok   = !priv_s || io.ptw.status.sum ? entries.map(_.u), 0.U) | Mux(priv_s, ~entries.map(_.u) : 'h0;
assign w_priv_x_ok    = priv_s ? ~entries.map(_.u) : entries.map(_.u));
assign w_r_array      = {1'b1, priv_rw_ok & (entries.map(_.sr) | Mux(io.ptw.status.mxr, entries.map(_.sx), 0.U))))
assign w_w_array      = {1'b1, priv_rw_ok & entries.map(_.sw)))
assign w_x_array      = {1'b1, priv_x_ok  & entries.map(_.sx)))
assign w_pr_array     = {nPhysicalEntries{prot_r  },  normal_entries.map(_.pr)) & ~ptw_ae_array)
assign w_pw_array     = {nPhysicalEntries{prot_w  },  normal_entries.map(_.pw)) & ~ptw_ae_array)
assign w_px_array     = {nPhysicalEntries{prot_x  },  normal_entries.map(_.px)) & ~ptw_ae_array)
assign w_eff_array    = {nPhysicalEntries{prot_eff},  normal_entries.map(_.eff)))
assign w_c_array      = {nPhysicalEntries{cacheable}, normal_entries.map(_.c)))
assign w_paa_array    = {nPhysicalEntries{prot_aa },  normal_entries.map(_.paa)))
assign w_pal_array    = {nPhysicalEntries{prot_al },  normal_entries.map(_.pal)))
assign w_paa_array_if_cached = paa_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_pal_array_if_cached = pal_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_prefetchable_array  = {(cacheable && homogeneous) << (nPhysicalEntries-1), normal_entries.map(_.c)))
  end
end
endgenerate

assign w_ptw_ae_array = {1'b0, entries.map(_.ae)))
assign w_priv_rw_ok   = !priv_s || io.ptw.status.sum ? entries.map(_.u), 0.U) | Mux(priv_s, ~entries.map(_.u) : 'h0;
assign w_priv_x_ok    = priv_s ? ~entries.map(_.u) : entries.map(_.u));
assign w_r_array      = {1'b1, priv_rw_ok & (entries.map(_.sr) | Mux(io.ptw.status.mxr, entries.map(_.sx), 0.U))))
assign w_w_array      = {1'b1, priv_rw_ok & entries.map(_.sw)))
assign w_x_array      = {1'b1, priv_x_ok  & entries.map(_.sx)))
assign w_pr_array     = {nPhysicalEntries{prot_r  },  normal_entries.map(_.pr)) & ~ptw_ae_array)
assign w_pw_array     = {nPhysicalEntries{prot_w  },  normal_entries.map(_.pw)) & ~ptw_ae_array)
assign w_px_array     = {nPhysicalEntries{prot_x  },  normal_entries.map(_.px)) & ~ptw_ae_array)
assign w_eff_array    = {nPhysicalEntries{prot_eff},  normal_entries.map(_.eff)))
assign w_c_array      = {nPhysicalEntries{cacheable}, normal_entries.map(_.c)))
assign w_paa_array    = {nPhysicalEntries{prot_aa },  normal_entries.map(_.paa)))
assign w_pal_array    = {nPhysicalEntries{prot_al },  normal_entries.map(_.pal)))
assign w_paa_array_if_cached = paa_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_pal_array_if_cached = pal_array | Mux(usingAtomicsInCache.B, c_array, 0.U))
assign w_prefetchable_array  = {(cacheable && homogeneous) << (nPhysicalEntries-1), normal_entries.map(_.c)))


localparam USE_ATOMIC = 1'b1;

logic w_cmd_lrsc          ;
logic w_cmd_amo_logical   ;
logic w_cmd_amo_arithmetic;
logic w_cmd_read          ;
logic w_cmd_write         ;
logic w_cmd_write_perms   ;

assign w_cmd_lrsc           = USE_ATOMIC && (i_tlb_req.cmd == M_XLR || i_tlb_req.cmd == M_XSC);
assign w_cmd_amo_logical    = USE_ATOMIC && is_amo_logical(i_tlb_req.cmd);
assign w_cmd_amo_arithmetic = USE_ATOMIC && is_amo_arithmetic(i_tlb_req.cmd);
assign w_cmd_read           = is_read(i_tlb_req.cmd);
assign w_cmd_write          = is_write(i_tlb_req.cmd);
assign w_cmd_write_perms    = cmd_write || (i_tlb_req.cmd === M_FLUSH_ALL); // not a write, but needs write permissions


// ------------------
// Response of TLB
// ------------------
assign o_tlb_resp.pf.ld        = (w_bad_va && w_cmd_read) || (|(pf_ld_array & w_is_hit));
assign o_tlb_resp.pf.st        = (w_bad_va && W_cmd_write_perms) || (|(pf_st_array & w_is_hit));
assign o_tlb_resp.pf.inst      = w_bad_va || (|(pf_inst_array & w_is_hit));
assign o_tlb_resp.ae.ld        = ae_ld_array & w_vm_enabled ? |w_is_hit : 1'b1;
assign o_tlb_resp.ae.st        = ae_st_array & w_vm_enabled ? |w_is_hit : 1'b1;
assign o_tlb_resp.ae.inst      = ~px_array   & w_vm_enabled ? |w_is_hit : 1'b1;
assign o_tlb_resp.ma.ld        = ma_ld_array & w_vm_enabled ? |w_is_hit : 1'b1;
assign o_tlb_resp.ma.st        = ma_st_array & w_vm_enabled ? |w_is_hit : 1'b1;
assign o_tlb_resp.ma.inst      = 1'b0;   // this is up to the pipeline to figure out
assign o_tlb_resp.cacheable    = |(c_array & w_is_hit);
assign o_tlb_resp.must_alloc   = |(must_alloc_array & w_is_hit);
// && edge.manager.managers.forall(m => !m.supportsAcquireB || m.supportsHint).B;
assign o_tlb_resp.prefetchable = |(prefetchable_array & w_is_hit);
assign o_tlb_resp.miss         = do_refill || w_tlb_miss || multipleW_is_hit;
assign o_tlb_resp.paddr        = {ppn, i_tlb_req.vaddr[PG_IDXW-1: 0]};

assign o_tlb_update = 1'b0;

endmodule
