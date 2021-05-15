module tlb
  import msrh_lsu_pkg::*;
#(
  parameter USING_VM = 1'b1
  )
(
 input logic  i_clk,
 input logic  i_reset_n,

 input        sfence_t i_sfence,

 input logic  i_kill,

 input        msrh_lsu_pkg::tlb_req_t i_tlb_req,
 output logic o_tlb_ready,
 output       msrh_lsu_pkg::tlb_resp_t o_tlb_resp,

 input msrh_pkg::priv_t               i_status_prv,
 input logic [riscv_pkg::XLEN_W-1: 0] i_csr_status,
 input logic [riscv_pkg::XLEN_W-1: 0] i_csr_satp,

 // Page Table Walk I/O
 tlb_ptw_if.master ptw_if,
 output logic o_tlb_update
);

localparam TLB_NORMAL_ENTRIES_NUM = 8;
localparam TLB_SUPERPAGE_ENTRIES_NUM = 4;
localparam USE_ATOMICS_INCACHE = 1'b1;
localparam USE_ATOMIC = 1'b1;
localparam TLB_ALL_ENTRIES_NUM = TLB_NORMAL_ENTRIES_NUM + TLB_SUPERPAGE_ENTRIES_NUM + 1;
localparam PG_LEVEL = 3;  // Sv39

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
  logic [SECTOR_NUM-1:0]                 valid;
  logic [1: 0]                           level;
  logic [riscv_pkg::VADDR_W-1: PG_IDX_W] tag;
  tlb_entry_data_t [SECTOR_NUM-1:0]      data;
} tlb_entry_t;

typedef enum logic [1:0] {
  ST_READY           = 0,
  ST_REQUEST         = 1,
  ST_WAIT            = 2,
  ST_WAIT_INVALIDATE = 3
} tlb_state_t;

tlb_state_t r_state;

tlb_entry_t w_sectored_entries[TLB_NORMAL_ENTRIES_NUM];
tlb_entry_t w_superpage_entries[TLB_SUPERPAGE_ENTRIES_NUM];
tlb_entry_t w_special_entry;
tlb_entry_t w_all_entries[TLB_ALL_ENTRIES_NUM]; // This is a alias of all entries

logic [riscv_pkg::VADDR_W-1: PG_IDX_W] w_vpn;
logic                                  w_priv_s;
logic                                  w_priv_uses_vm;
logic                                  w_vm_enabled;
logic                                  w_bad_va;
logic                                  w_misaligned;

logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_is_hit;

logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_ptw_ae_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_priv_rw_ok;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_priv_x_ok;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_r_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_w_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_x_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_pr_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_pw_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_px_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_eff_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_c_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_paa_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_pal_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_paa_array_if_cached;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_pal_array_if_cached;
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_prefetchable_array;

logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_hits_vec;
// assign  = widthMap(w => VecInit(all_entries.map(vm_enabled(w) && _.hit(vpn(w)))))
logic [TLB_ALL_ENTRIES_NUM-1: 0]       w_real_hits;

logic                                  w_tlb_hit;
logic                                  w_tlb_miss;

logic [riscv_pkg::VADDR_W-1: PG_IDX_W] r_refill_tag;

generate for (genvar e_idx = 0; e_idx < TLB_ALL_ENTRIES_NUM; e_idx++) begin : all_entries
  if (e_idx < TLB_NORMAL_ENTRIES_NUM) begin : normal_entries
    assign w_all_entries[e_idx]        = w_sectored_entries[e_idx];
  end else if (e_idx < TLB_SUPERPAGE_ENTRIES_NUM + TLB_NORMAL_ENTRIES_NUM) begin : superpage_entries
    assign w_all_entries[e_idx] = w_superpage_entries[e_idx - TLB_NORMAL_ENTRIES_NUM];
  end else if (e_idx < TLB_SUPERPAGE_ENTRIES_NUM + TLB_NORMAL_ENTRIES_NUM + 1) begin : superpage_entries
    assign w_all_entries[e_idx] = w_special_entry;
  end
end
endgenerate


logic [riscv_pkg::PPN_W-1:0] w_entry_ppn[TLB_ALL_ENTRIES_NUM];
logic [riscv_pkg::PPN_W-1:0] w_selected_ppn;
logic [riscv_pkg::PPN_W-1:0] w_ppn;
generate for (genvar t_idx = 0; t_idx < TLB_ALL_ENTRIES_NUM; t_idx++) begin : tlb_loop
  logic [PG_LEVEL-1: 0] w_tag_match;
  logic [$clog2(SECTOR_NUM)-1: 0] sector_idx;
  logic                 sector_tag_match;

  localparam SUPER_PAGE      = (t_idx >= TLB_NORMAL_ENTRIES_NUM);
  localparam SUPER_PAGE_ONLY = (t_idx >= TLB_NORMAL_ENTRIES_NUM) && (t_idx < TLB_NORMAL_ENTRIES_NUM + TLB_SUPERPAGE_ENTRIES_NUM);

  assign sector_idx = w_vpn[PG_IDX_W +: $clog2(SECTOR_NUM)] ;
  assign sector_tag_match = (w_all_entries[t_idx].tag == w_vpn);

  for (genvar lvl_idx = 0; lvl_idx < PG_LEVEL; lvl_idx++) begin : lvl_loop
    localparam base = VPN_W - (lvl_idx + 1) * PG_LEVEL_W;
    logic w_ignore;
    /* verilator lint_off UNSIGNED */
    assign w_ignore = (w_all_entries[t_idx].level < lvl_idx) || (SUPER_PAGE_ONLY && lvl_idx == PG_LEVELS-1);
    assign w_tag_match[lvl_idx] = w_ignore | (w_all_entries[t_idx].tag[base + PG_IDX_W +: PG_LEVEL_W] == w_vpn[base + PG_IDX_W +: PG_LEVEL_W]);
  end
  assign w_is_hit[t_idx] = w_all_entries[t_idx].valid[sector_idx] & ((SUPER_PAGE && msrh_conf_pkg::USING_VM) ? |w_tag_match :
                                                                     sector_tag_match);
  assign w_hits_vec[t_idx]  = w_vm_enabled & w_is_hit[t_idx];
  assign w_real_hits[t_idx] = w_hits_vec[t_idx];

  assign w_entry_ppn[t_idx] = w_all_entries[t_idx].data[sector_idx].ppn;
end
endgenerate

bit_oh_or #(.T(logic[riscv_pkg::PPN_W-1:0]), .WORDS(TLB_ALL_ENTRIES_NUM)) bit_ppn (.i_data(w_entry_ppn), .i_oh(w_hits_vec), .o_selected(w_selected_ppn));

assign w_vpn = i_tlb_req.vaddr[riscv_pkg::VADDR_W-1: PG_IDX_W];
assign w_ppn = !w_vm_enabled ? {{(riscv_pkg::PPN_W+PG_IDX_W-riscv_pkg::VADDR_W){1'b0}}, w_vpn} : w_selected_ppn;

assign o_tlb_ready = (r_state === ST_READY);
assign w_priv_uses_vm = i_status_prv <= msrh_pkg::PRV_U;
assign w_vm_enabled = msrh_conf_pkg::USING_VM &
                      (i_csr_satp[riscv_pkg::XLEN_W-1 -: 2] != 'h0) &
                      w_priv_uses_vm &
                      !i_tlb_req.passthrough;

assign w_tlb_hit  = |w_real_hits;
assign w_tlb_miss = w_vm_enabled & !w_bad_va & !w_tlb_hit;

generate if (msrh_conf_pkg::USING_VM) begin : use_vm
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_state <= ST_READY;
    end else begin
      case (r_state)
        ST_READY : begin
          if (i_tlb_req.valid & o_tlb_ready & w_tlb_miss) begin
            r_state <= ST_REQUEST;
            r_refill_tag <= w_vpn;
          end
        end
        ST_REQUEST : begin
          if (i_kill) begin
            r_state <= ST_READY;
          end else if (ptw_if.req_ready) begin
            if (i_sfence.valid) begin
              r_state <=  ST_WAIT_INVALIDATE;
            end else begin
              r_state <= ST_WAIT;
            end
          end else if (i_sfence.valid) begin
            r_state <= ST_READY;
          end
        end
        ST_WAIT : begin
          if (i_sfence.valid) begin
            r_state <= ST_WAIT_INVALIDATE;
          end
        end
        ST_WAIT_INVALIDATE : begin
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
assign w_misaligned = ((i_tlb_req.vaddr & ((1 << i_tlb_req.size) - 1)) != 'h0);

generate for (genvar e_idx = 0; e_idx < TLB_ALL_ENTRIES_NUM; e_idx++) begin : elem_loop
  if (e_idx < TLB_NORMAL_ENTRIES_NUM) begin : normal_entries
    logic [$clog2(SECTOR_NUM)-1: 0] sector_idx;
    assign sector_idx = w_vpn[PG_IDX_W +: $clog2(SECTOR_NUM)] ;

    assign w_ptw_ae_array[e_idx] = w_sectored_entries[e_idx].data[sector_idx].ae;
    assign w_priv_rw_ok  [e_idx] = !w_priv_s || ptw_if.status[18] ? w_sectored_entries[e_idx].data[sector_idx].u : 'h0 |
                                   w_priv_s ? ~w_sectored_entries[e_idx].data[sector_idx].u : 'h0;
    assign w_priv_x_ok   [e_idx] = w_priv_s ? ~w_sectored_entries[e_idx].data[sector_idx].u : w_sectored_entries[e_idx].data[sector_idx].u;
    assign w_r_array     [e_idx] = w_priv_rw_ok[e_idx] & (w_sectored_entries[e_idx].data[sector_idx].sr | (ptw_if.status[19] ? w_sectored_entries[e_idx].data[sector_idx].sx : 1'b0));
    assign w_w_array     [e_idx] = w_priv_rw_ok[e_idx] & w_sectored_entries[e_idx].data[sector_idx].sw;
    assign w_x_array     [e_idx] = w_priv_x_ok [e_idx] & w_sectored_entries[e_idx].data[sector_idx].sx;
    assign w_pr_array    [e_idx] = w_sectored_entries[e_idx].data[sector_idx].pr & ~w_ptw_ae_array[e_idx];
    assign w_pw_array    [e_idx] = w_sectored_entries[e_idx].data[sector_idx].pw & ~w_ptw_ae_array[e_idx];
    assign w_px_array    [e_idx] = w_sectored_entries[e_idx].data[sector_idx].px & ~w_ptw_ae_array[e_idx];
    assign w_eff_array   [e_idx] = w_sectored_entries[e_idx].data[sector_idx].eff;
    assign w_c_array     [e_idx] = w_sectored_entries[e_idx].data[sector_idx].c;
    assign w_paa_array   [e_idx] = w_sectored_entries[e_idx].data[sector_idx].paa;
    assign w_pal_array   [e_idx] = w_sectored_entries[e_idx].data[sector_idx].pal;
    assign w_paa_array_if_cached[e_idx] = w_paa_array[e_idx] | USE_ATOMICS_INCACHE ? w_c_array[e_idx] : 1'b0;
    assign w_pal_array_if_cached[e_idx] = w_pal_array[e_idx] | USE_ATOMICS_INCACHE ? w_c_array[e_idx] : 1'b0;
    assign w_prefetchable_array [e_idx] = w_sectored_entries[e_idx].data[sector_idx].c;
  end else if (e_idx < TLB_SUPERPAGE_ENTRIES_NUM + TLB_NORMAL_ENTRIES_NUM) begin : superpage_entries
  end else if (e_idx < TLB_SUPERPAGE_ENTRIES_NUM + TLB_NORMAL_ENTRIES_NUM + 1) begin : superpage_entries
  end
end
endgenerate

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
assign w_cmd_write_perms    = w_cmd_write || (i_tlb_req.cmd === M_FLUSH_ALL); // not a write, but needs write permissions

logic [TLB_ALL_ENTRIES_NUM-1: 0] w_lrsc_allowed;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_ae_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_ae_ld_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_ae_st_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_must_alloc_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_ma_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_ma_ld_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_ma_st_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_pf_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_pf_ld_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_pf_st_array;
logic [TLB_ALL_ENTRIES_NUM-1: 0] w_pf_inst_array;

// assign w_lrsc_allowed = widthMap(w => Mux((usingDataScratchpad || usingAtomicsOnlyForIO).B, 0.U, c_array(w)))
assign w_lrsc_allowed = w_c_array;
assign w_ae_array = (w_misaligned ? w_eff_array     : 'h0) |
                    (w_cmd_lrsc   ? ~w_lrsc_allowed : 'h0);
assign w_ae_ld_array = w_cmd_read ? w_ae_array | ~w_pr_array : 'h0;
assign w_ae_st_array = (w_cmd_write_perms    ? w_ae_array | ~w_pw_array : 'h0) |
                       (w_cmd_amo_logical    ? ~w_pal_array_if_cached : 'h0) |
                       (w_cmd_amo_arithmetic ? ~w_paa_array_if_cached : 'h0);
assign w_must_alloc_array = (w_cmd_amo_logical    ? ~w_paa_array : 'h0) |
                            (w_cmd_amo_arithmetic ? ~w_pal_array : 'h0) |
                            (w_cmd_lrsc           ? ~'h0         : 'h0);
assign w_ma_ld_array = w_misaligned && w_cmd_read  ? ~w_eff_array : 'h0;
assign w_ma_st_array = w_misaligned && w_cmd_write ? ~w_eff_array : 'h0;
assign w_pf_ld_array = w_cmd_read        ? ~(w_r_array | w_ptw_ae_array) : 'h0;
assign w_pf_st_array = w_cmd_write_perms ? ~(w_w_array | w_ptw_ae_array) : 'h0;
assign w_pf_inst_array = ~(w_x_array | w_ptw_ae_array);

logic                            w_do_refill;
assign w_do_refill = msrh_conf_pkg::USING_VM && ptw_if.resp.valid;

// ---------------
// Request of TLB
// ---------------
assign ptw_if.req.valid = r_state == ST_REQUEST;
assign ptw_if.req.addr  = r_refill_tag;
assign ptw_if.satp      = i_csr_satp;
assign ptw_if.status    = i_csr_status;

// ------------------
// Response of TLB
// ------------------
// assign o_tlb_resp.pf.ld        = (w_bad_va && w_cmd_read) || (|(w_pf_ld_array & w_is_hit));
// assign o_tlb_resp.pf.st        = (w_bad_va && w_cmd_write_perms) || (|(w_pf_st_array & w_is_hit));
// assign o_tlb_resp.pf.inst      = w_bad_va || (|(w_pf_inst_array & w_is_hit));
// assign o_tlb_resp.ae.ld        = w_ae_ld_array & w_vm_enabled ? |w_is_hit : 1'b1;
// assign o_tlb_resp.ae.st        = w_ae_st_array & w_vm_enabled ? |w_is_hit : 1'b1;
// assign o_tlb_resp.ae.inst      = ~w_px_array   & w_vm_enabled ? |w_is_hit : 1'b1;
// assign o_tlb_resp.ma.ld        = w_ma_ld_array & w_vm_enabled ? |w_is_hit : 1'b1;
// assign o_tlb_resp.ma.st        = w_ma_st_array & w_vm_enabled ? |w_is_hit : 1'b1;
// assign o_tlb_resp.ma.inst      = 1'b0;   // this is up to the pipeline to figure out
// assign o_tlb_resp.cacheable    = |(w_c_array & w_is_hit);
// assign o_tlb_resp.must_alloc   = |(w_must_alloc_array & w_is_hit);
// // && edge.manager.managers.forall(m => !m.supportsAcquireB || m.supportsHint).B;
// assign o_tlb_resp.prefetchable = |(w_prefetchable_array & w_is_hit);
assign o_tlb_resp.miss         = w_do_refill | w_tlb_miss /* || multiplehits */;
assign o_tlb_resp.paddr        = {w_ppn, i_tlb_req.vaddr[11: 0]};

assign o_tlb_update = 1'b0;

endmodule // tlb
