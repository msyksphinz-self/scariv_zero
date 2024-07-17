// ------------------------------------------------------------------------
// NAME : scariv_front_decoder
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Instruction Buffer with Register Decoder
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_front_decoder
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import decoder_reg_pkg::*;
  (
   input logic  i_clk,
   input logic  i_reset_n,
   input logic  i_flush_valid,

   /* CSR information */
   csr_info_if.slave csr_info,

   btb_search_if.monitor    btb_search_if,
   bim_search_if.monitor    bim_search_if,
   ras_search_if.slave      ras_search_if,
   gshare_search_if.monitor gshare_search_if,

   input logic                           i_f2_ubtb_predict_valid,
   input scariv_predict_pkg::ubtb_info_t i_f2_ubtb_info,

   output decode_flush_t o_decode_flush,

   output logic                       o_inst_ready,
   input scariv_pkg::inst_buffer_in_t i_f2_inst,
   scariv_front_if.master             ibuf_front_if,

   br_upd_if.slave br_upd_if
   );

// Queue variables
logic    w_inst_buf_empty;
logic    w_inst_buf_full;
logic    w_inst_queue_pop;


logic    w_br_flush;
logic    w_flush_pipeline;
assign w_br_flush       = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_pipeline = i_flush_valid | w_br_flush;

logic    w_ptr_in_fire;
logic    w_ptr_out_fire;

scariv_front_pkg::inst_t[scariv_conf_pkg::ICACHE_DATA_W/16-1: 0] w_f2_expand_inst;
scariv_pkg::vaddr_t                                              w_f2_pc;

logic [scariv_conf_pkg::ICACHE_DATA_W/16-1: 0] r_backup_flag_dispatched;
logic [scariv_conf_pkg::ICACHE_DATA_W/16-1: 0] w_backup_front_inst_valids;
scariv_front_pkg::decoder_inst_t               r_backup_front_inst; // for instruction shifting

scariv_pkg::grp_id_t                           w_f3_inst_disp_mask;
logic [scariv_conf_pkg::DISP_SIZE: 0]          w_f3_inst_disp_mask_tmp;
logic [scariv_conf_pkg::ICACHE_DATA_W/16-1: 0] w_f3_flag_dispatched_next;

logic                     w_f3_valid_next;
logic                     w_f3_fire_next;
scariv_front_pkg::front_t w_ibuf_front_payload_next;
logic [scariv_conf_pkg::ICACHE_DATA_W/16-1: 0] w_f3_front_inst_valids;

logic                                          w_f3_all_inst_dispatched;
logic                                          w_f3_inst_queue_sel;
assign w_f3_all_inst_dispatched = (w_backup_front_inst_valids != 0) ? (w_f3_flag_dispatched_next == w_backup_front_inst_valids) :
                                  (w_f3_inst_disp_mask == w_f3_front_inst_valids);

assign w_f3_inst_queue_sel = (w_backup_front_inst_valids == 'h0) & w_f3_front_inst_valid;

assign w_ptr_in_fire  = i_f2_inst.valid & o_inst_ready;
assign w_ptr_out_fire = !w_inst_buf_empty & w_f3_inst_queue_sel & w_f3_fire_next;

// -----------------------
// Decoder / RVC Expander
// -----------------------
scariv_front_expander
u_front_expander
  (
   .i_clk         (i_clk    ),
   .i_reset_n     (i_reset_n),

   .i_flush_valid (w_flush_pipeline),

   .i_f2_inst        (i_f2_inst       ),
   .o_f2_expand_inst (w_f2_expand_inst),
   .o_f2_pc          (w_f2_pc         )
   );

// ------------------------
// Queue Control Pointer
// ------------------------
scariv_front_pkg::decoder_inst_t w_f2_front_inst;

logic                            w_f3_front_inst_valid;
scariv_front_pkg::decoder_inst_t w_f3_front_inst;
scariv_front_pkg::decoder_inst_t w_f3_front_inst_from_queue;
scariv_front_pkg::decoder_inst_t w_f3_front_inst_next; // for instruction shifting

assign w_f2_front_inst.inst       = w_f2_expand_inst;
assign w_f2_front_inst.pc_addr    = w_f2_pc;
`ifdef SIMULATION
assign w_f2_front_inst.pc_addr_debug = i_f2_inst.pc_dbg;
`endif // SIMULATION

ring_fifo_2ptr
  #(.T(scariv_front_pkg::decoder_inst_t),
    .DEPTH (scariv_pkg::INST_BUF_SIZE)
    )
u_inst_queue
(
 .i_clk     (i_clk    ),
 .i_reset_n (i_reset_n),

 .i_clear   (w_flush_pipeline),

 .i_push (w_ptr_in_fire),
 .i_data (w_f2_front_inst),

 .o_empty (w_inst_buf_empty),
 .o_full  (w_inst_buf_full),

 .i_pop  (w_ptr_out_fire),

 .o_valid0 (w_f3_front_inst_valid),
 .o_data0  (w_f3_front_inst_from_queue),

 .o_valid1 (),
 .o_data1  ()
 );

assign o_inst_ready = !w_inst_buf_full;

generate for (genvar idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin : gen_f3_loop
  assign w_f3_front_inst_valids[idx] = w_f3_front_inst.inst[idx].valid;
  assign w_backup_front_inst_valids[idx] = r_backup_front_inst.inst[idx].valid;
end endgenerate


always_comb begin

  // Selection of the instruction decoder
  w_f3_front_inst = w_f3_inst_queue_sel ? w_f3_front_inst_from_queue : r_backup_front_inst;

  w_f3_front_inst_next.pc_addr       = w_f3_front_inst.pc_addr;
`ifdef SIMULATION
  w_f3_front_inst_next.pc_addr_debug = w_f3_front_inst.pc_addr_debug;
`endif // SIMULATION

  if (w_flush_pipeline) begin
    for (int idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin
      w_f3_front_inst_next.inst[idx].valid = 1'b0;
    end
  end else begin
    /* verilator lint_off CASEX */
    casex (w_f3_inst_disp_mask)
      4'b1xxx : begin
        for (int idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16 - 4; idx++) begin
          w_f3_front_inst_next.inst[idx] = w_f3_front_inst.inst[4 + idx];
        end
        for (int idx = scariv_conf_pkg::ICACHE_DATA_W/16 - 4; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin
          w_f3_front_inst_next.inst[idx].valid = 1'b0;
        end
//         w_f3_front_inst_next.pc_addr       = w_f3_front_inst.pc_addr       + w_f3_front_inst.inst[4].cache_pos;
// `ifdef SIMULATION
//         w_f3_front_inst_next.pc_addr_debug = w_f3_front_inst.pc_addr_debug + {w_f3_front_inst.inst[4].cache_pos, 1'b0};
// `endif // SIMULATION
      end
      4'b01xx : begin
        for (int idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16 - 3; idx++) begin
          w_f3_front_inst_next.inst[idx] = w_f3_front_inst.inst[3 + idx];
        end
        for (int idx = scariv_conf_pkg::ICACHE_DATA_W/16 - 3; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin
          w_f3_front_inst_next.inst[idx].valid = 1'b0;
        end
//         w_f3_front_inst_next.pc_addr       = w_f3_front_inst.pc_addr       + w_f3_front_inst.inst[3].cache_pos;
// `ifdef SIMULATION
//         w_f3_front_inst_next.pc_addr_debug = w_f3_front_inst.pc_addr_debug + {w_f3_front_inst.inst[3].cache_pos, 1'b0};
// `endif // SIMULATION
      end
      4'b001x : begin
        for (int idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16 - 2; idx++) begin
          w_f3_front_inst_next.inst[idx] = w_f3_front_inst.inst[2 + idx];
        end
        for (int idx = scariv_conf_pkg::ICACHE_DATA_W/16 - 2; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin
          w_f3_front_inst_next.inst[idx].valid = 1'b0;
        end
//         w_f3_front_inst_next.pc_addr       = w_f3_front_inst.pc_addr       + w_f3_front_inst.inst[2].cache_pos;
// `ifdef SIMULATION
//         w_f3_front_inst_next.pc_addr_debug = w_f3_front_inst.pc_addr_debug + {w_f3_front_inst.inst[2].cache_pos, 1'b0};
// `endif // SIMULATION
      end
      4'b0001 : begin
        for (int idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16 - 1; idx++) begin
          w_f3_front_inst_next.inst[idx] = w_f3_front_inst.inst[1 + idx];
        end
        for (int idx = scariv_conf_pkg::ICACHE_DATA_W/16 - 1; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin
          w_f3_front_inst_next.inst[idx].valid = 1'b0;
        end
//         w_f3_front_inst_next.pc_addr       = w_f3_front_inst.pc_addr       + w_f3_front_inst.inst[1].cache_pos;
// `ifdef SIMULATION
//         w_f3_front_inst_next.pc_addr_debug = w_f3_front_inst.pc_addr_debug + {w_f3_front_inst.inst[1].cache_pos, 1'b0};
// `endif // SIMULATION
      end
      default : begin
        for (int idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin
          w_f3_front_inst_next.inst[idx] = w_f3_front_inst.inst[idx];
        end
      end
    endcase // casex (w_f3_inst_disp_mask)
  end // else: !if(w_flush_pipeline)
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_backup_front_inst <= 'h0;

    w_backup_front_inst_valids <= 'h0;
  end else begin

    if (w_flush_pipeline) begin
      for (int idx = 0; idx < scariv_conf_pkg::ICACHE_DATA_W/16; idx++) begin
        r_backup_front_inst.inst[idx].valid <= 1'b0;
      end
    end else if (w_f3_fire_next) begin
      r_backup_front_inst <= w_f3_front_inst_next;
    end
  end
end


typedef enum logic [ 3: 0] {
  INST_KIND_ARITH        = 0,
  INST_KIND_MULDIV       = 1,
  INST_KIND_LD           = 2,
  INST_KIND_ST           = 3,
  INST_KIND_MEM          = 4,
  INST_KIND_BRU          = 5,
  INST_KIND_BRU_BRANCH   = 6,
  INST_KIND_CSU          = 7,
  INST_KIND_FPU          = 8,
  INST_KIND_FETCH_EXCEPT = 9,
  INST_KIND_ILLEGAL      = 10,
  INST_KIND_MAX          = 11
} inst_kind_t;


// ----------------------------
// Dispatch Instruction Pickup
// ----------------------------
scariv_pkg::grp_id_t w_f3_inst_kind    [INST_KIND_MAX];
scariv_pkg::grp_id_t w_f3_inst_pick_up [INST_KIND_MAX];
scariv_pkg::grp_id_t w_f3_inst_disp    [INST_KIND_MAX];
scariv_pkg::grp_id_t w_f3_inst_disped  [INST_KIND_MAX];
scariv_pkg::grp_id_t w_f3_inst_is_call;
scariv_pkg::grp_id_t w_f3_inst_is_ret;

// Operand information
rd_t w_f3_rd_field_type [scariv_conf_pkg::DISP_SIZE];
r1_t w_f3_rs1_field_type[scariv_conf_pkg::DISP_SIZE];
r2_t w_f3_rs2_field_type[scariv_conf_pkg::DISP_SIZE];
r3_t w_f3_rs3_field_type[scariv_conf_pkg::DISP_SIZE];

generate for (genvar w_idx = 0; w_idx < scariv_conf_pkg::DISP_SIZE; w_idx++) begin : gen_pickup_loop

  assign w_f3_inst_kind[INST_KIND_ARITH     ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT_ARITH    );
  assign w_f3_inst_kind[INST_KIND_MULDIV    ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT_MULDIV   );
  assign w_f3_inst_kind[INST_KIND_LD        ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT_LD       );
  assign w_f3_inst_kind[INST_KIND_ST        ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT_ST       );
  assign w_f3_inst_kind[INST_KIND_BRU       ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT_BR       );
  assign w_f3_inst_kind[INST_KIND_BRU_BRANCH][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].subcat == decoder_inst_cat_pkg::INST_SUBCAT_BRANCH);
  assign w_f3_inst_kind[INST_KIND_CSU       ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT_CSU      );
  assign w_f3_inst_kind[INST_KIND_FPU       ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT_FPU      );
  assign w_f3_inst_kind[INST_KIND_ILLEGAL   ][w_idx] = w_f3_front_inst_valids[w_idx] & (w_f3_front_inst.inst[w_idx].cat    == decoder_inst_cat_pkg::INST_CAT__        );

  decoder_reg
  u_decoder_reg
    (
     .inst(w_f3_front_inst.inst[w_idx].inst),
     .rd(w_f3_rd_field_type [w_idx]),
     .r1(w_f3_rs1_field_type[w_idx]),
     .r2(w_f3_rs2_field_type[w_idx]),
     .r3(w_f3_rs3_field_type[w_idx])
     );

  logic          w_f3_is_std_call;
  logic          w_f3_is_std_ret;
  assign w_f3_is_std_call = (w_f3_front_inst.inst[w_idx].inst[ 6: 0] == 7'b1101111) &
                            (w_f3_front_inst.inst[w_idx].inst[11: 7] == 5'h1);
  assign w_f3_is_std_ret = w_f3_front_inst.inst[w_idx].inst == 32'h00008067;

  assign w_f3_inst_is_call  [w_idx] = w_f3_front_inst_valids[w_idx] & w_f3_is_std_call;
  assign w_f3_inst_is_ret   [w_idx] = w_f3_front_inst_valids[w_idx] & w_f3_is_std_ret;

end endgenerate

assign w_f3_inst_pick_up[INST_KIND_ARITH        ] = w_f3_inst_kind[INST_KIND_ARITH       ] | w_f3_inst_kind[INST_KIND_MULDIV];
assign w_f3_inst_pick_up[INST_KIND_MULDIV       ] = w_f3_inst_kind[INST_KIND_MULDIV      ];
assign w_f3_inst_pick_up[INST_KIND_MEM          ] = w_f3_inst_kind[INST_KIND_LD          ] | w_f3_inst_kind[INST_KIND_ST];
assign w_f3_inst_pick_up[INST_KIND_LD           ] = w_f3_inst_kind[INST_KIND_LD          ];
assign w_f3_inst_pick_up[INST_KIND_ST           ] = w_f3_inst_kind[INST_KIND_ST          ];
assign w_f3_inst_pick_up[INST_KIND_BRU          ] = w_f3_inst_kind[INST_KIND_BRU         ];
assign w_f3_inst_pick_up[INST_KIND_CSU          ] = w_f3_inst_kind[INST_KIND_CSU         ];
assign w_f3_inst_pick_up[INST_KIND_FPU          ] = w_f3_inst_kind[INST_KIND_FPU         ];
assign w_f3_inst_pick_up[INST_KIND_FETCH_EXCEPT ] = w_f3_inst_kind[INST_KIND_FETCH_EXCEPT];
assign w_f3_inst_pick_up[INST_KIND_ILLEGAL      ] = w_f3_inst_kind[INST_KIND_ILLEGAL     ];

bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::ARITH_DISP_SIZE )) u_arith_disp_pick_up  (.in(w_f3_inst_pick_up[INST_KIND_ARITH        ]), .out(w_f3_inst_disp[INST_KIND_ARITH        ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MULDIV_DISP_SIZE)) u_muldiv_disp_pick_up (.in(w_f3_inst_pick_up[INST_KIND_MULDIV       ]), .out(w_f3_inst_disp[INST_KIND_MULDIV       ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_mem_disp_pick_up    (.in(w_f3_inst_pick_up[INST_KIND_MEM          ]), .out(w_f3_inst_disp[INST_KIND_MEM          ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_ld_disp_pick_up     (.in(w_f3_inst_pick_up[INST_KIND_LD           ]), .out(w_f3_inst_disp[INST_KIND_LD           ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_st_disp_pick_up     (.in(w_f3_inst_pick_up[INST_KIND_ST           ]), .out(w_f3_inst_disp[INST_KIND_ST           ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::BRU_DISP_SIZE   )) u_bru_disp_pick_up    (.in(w_f3_inst_pick_up[INST_KIND_BRU          ]), .out(w_f3_inst_disp[INST_KIND_BRU          ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::CSU_DISP_SIZE   )) u_csu_disp_pick_up    (.in(w_f3_inst_pick_up[INST_KIND_CSU          ]), .out(w_f3_inst_disp[INST_KIND_CSU          ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::FPU_DISP_SIZE   )) u_fpu_disp_pick_up    (.in(w_f3_inst_pick_up[INST_KIND_FPU          ]), .out(w_f3_inst_disp[INST_KIND_FPU          ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(1                                )) u_except_disp_pick_up (.in(w_f3_inst_pick_up[INST_KIND_FETCH_EXCEPT ]), .out(w_f3_inst_disp[INST_KIND_FETCH_EXCEPT ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(1                                )) u_illegal_disp_pick_up(.in(w_f3_inst_pick_up[INST_KIND_ILLEGAL      ]), .out(w_f3_inst_disp[INST_KIND_ILLEGAL      ]));

scariv_pkg::grp_id_t w_f3_inst_disp_or;
assign w_f3_inst_disp_or = w_f3_inst_disp[INST_KIND_ARITH       ] |
                           w_f3_inst_disp[INST_KIND_MEM         ] |
                           w_f3_inst_disp[INST_KIND_BRU         ] |
                           w_f3_inst_disp[INST_KIND_CSU         ] |
                           w_f3_inst_disp[INST_KIND_FPU         ] |
                           w_f3_inst_disp[INST_KIND_ILLEGAL     ] |
                           w_f3_inst_disp[INST_KIND_FETCH_EXCEPT];

bit_extract_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE + 1)) u_inst_msb (.in({1'b1, ~w_f3_inst_disp_or}), .out(w_f3_inst_disp_mask_tmp));

assign w_f3_inst_disp_mask = w_f3_inst_disp_mask_tmp - 1;

always_comb begin
  if (w_f3_fire_next) begin
    /* verilator lint_off CASEINCOMPLETE */
    casex (w_f3_inst_disp_mask)
      4'b1xxx : w_f3_flag_dispatched_next = (r_backup_flag_dispatched << 4) | w_f3_inst_disp_mask;
      4'b01xx : w_f3_flag_dispatched_next = (r_backup_flag_dispatched << 3) | w_f3_inst_disp_mask;
      4'b001x : w_f3_flag_dispatched_next = (r_backup_flag_dispatched << 2) | w_f3_inst_disp_mask;
      4'b0001 : w_f3_flag_dispatched_next = (r_backup_flag_dispatched << 1) | w_f3_inst_disp_mask;
    endcase // casex (w_f3_inst_disp_mask)
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_backup_flag_dispatched <= 'h0;
  end else begin
    if (w_flush_pipeline) begin
      r_backup_flag_dispatched <= 'h0;
    end else if (w_f3_all_inst_dispatched) begin
      r_backup_flag_dispatched <= w_f3_inst_disp_mask;
    end else if (w_f3_fire_next) begin
      r_backup_flag_dispatched <= w_f3_flag_dispatched_next;
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign w_f3_valid_next = |w_f3_inst_disp_mask;
assign w_f3_fire_next  = ~r_ibuf_front_if_valid_raw | ibuf_front_if.ready;

logic r_ibuf_front_if_valid_raw;
assign ibuf_front_if.valid = r_ibuf_front_if_valid_raw & ~w_flush_pipeline;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ibuf_front_if_valid_raw <= 1'b0;
  end else begin
    if (w_flush_pipeline) begin
      r_ibuf_front_if_valid_raw <= 1'b0;
    end else if (w_f3_fire_next) begin
      r_ibuf_front_if_valid_raw <= w_f3_valid_next;
      ibuf_front_if.payload     <= w_ibuf_front_payload_next;
    end
  end
end

assign w_ibuf_front_payload_next.pc_addr           = w_f3_front_inst.pc_addr; //  + r_head_start_pos;
assign w_ibuf_front_payload_next.basicblk_pc_vaddr = 'h0; // w_inst_buf_data[0].pc;
`ifdef SIMULATION
assign w_ibuf_front_payload_next.pc_addr_debug           = w_f3_front_inst.pc_addr_debug; // (w_inst_buf_data[0].pc + r_head_start_pos);
assign w_ibuf_front_payload_next.basicblk_pc_vaddr_debug = 'h0; // w_inst_buf_data[0].pc << 1;
`endif // SIMULATION
assign w_ibuf_front_payload_next.is_br_included   = |w_f3_inst_disped[INST_KIND_BRU];
assign w_ibuf_front_payload_next.tlb_except_valid = 1'b0; // w_fetch_except;
assign w_ibuf_front_payload_next.tlb_except_cause = 1'b0; // w_fetch_except_cause;
assign w_ibuf_front_payload_next.tlb_except_tval  = 1'b0; // w_fetch_except_tval;
assign w_ibuf_front_payload_next.int_inserted     = 1'b0; // w_inst_buf_data[0].int_inserted;

// -------------------------------
// Dispatch Inst, Resource Count
// -------------------------------

bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::ARITH_DISP_SIZE )) u_arith_disped_pick_up   (.in(w_f3_inst_disp[INST_KIND_ARITH ] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_ARITH ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MULDIV_DISP_SIZE)) u_muldiv_disped_pick_up  (.in(w_f3_inst_disp[INST_KIND_MULDIV] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_MULDIV]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_mem_disped_pick_up     (.in(w_f3_inst_disp[INST_KIND_MEM   ] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_MEM   ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_ld_disped_pick_up      (.in(w_f3_inst_disp[INST_KIND_LD    ] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_LD    ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_st_disped_pick_up      (.in(w_f3_inst_disp[INST_KIND_ST    ] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_ST    ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::BRU_DISP_SIZE   )) u_bru_disped_pick_up     (.in(w_f3_inst_disp[INST_KIND_BRU   ] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_BRU   ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::CSU_DISP_SIZE   )) u_csu_disped_pick_up     (.in(w_f3_inst_disp[INST_KIND_CSU   ] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_CSU   ]));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::FPU_DISP_SIZE   )) u_fpu_disped_pick_up     (.in(w_f3_inst_disp[INST_KIND_FPU   ] & w_f3_inst_disp_mask), .out(w_f3_inst_disped[INST_KIND_FPU   ]));

logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_f3_inst_disped_cnt[INST_KIND_MAX];

generate for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_rsrc_loop
  localparam alu_lane_width = scariv_conf_pkg::ARITH_DISP_SIZE / scariv_conf_pkg::ALU_INST_NUM;
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[alu_lane_width];
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(alu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < alu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i * scariv_conf_pkg::ALU_INST_NUM + a_idx), .SEL_WIDTH(scariv_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_f3_inst_disped[INST_KIND_ARITH]), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .WORDS(alu_lane_width)) alu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_alu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign w_ibuf_front_payload_next.resource_cnt.alu_inst_cnt  [a_idx] = w_lane_disp_cnt;
  assign w_ibuf_front_payload_next.resource_cnt.alu_inst_valid[a_idx] = w_lane_disped_valid_or;
end
endgenerate

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_muldiv_inst_cnt (.in(w_f3_inst_disped[INST_KIND_MULDIV]), .out(w_f3_inst_disped_cnt[INST_KIND_MULDIV]));
assign w_ibuf_front_payload_next.resource_cnt.muldiv_inst_cnt = w_f3_inst_disped_cnt[INST_KIND_MULDIV];

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_mem_inst_cnt (.in(w_f3_inst_disped[INST_KIND_MEM]), .out(w_f3_inst_disped_cnt[INST_KIND_MEM]));
bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_ld_inst_cnt  (.in(w_f3_inst_disped[INST_KIND_LD ]), .out(w_f3_inst_disped_cnt[INST_KIND_LD ]));
bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_st_inst_cnt  (.in(w_f3_inst_disped[INST_KIND_ST ]), .out(w_f3_inst_disped_cnt[INST_KIND_ST ]));

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_rsrc_loop
  localparam lsu_lane_width = scariv_conf_pkg::MEM_DISP_SIZE / scariv_conf_pkg::LSU_INST_NUM;
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[lsu_lane_width];
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(lsu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < lsu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i * scariv_conf_pkg::LSU_INST_NUM + l_idx), .SEL_WIDTH(scariv_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_f3_inst_disped[INST_KIND_MEM]), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .WORDS(lsu_lane_width)) lsu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_lsu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign w_ibuf_front_payload_next.resource_cnt.lsu_inst_cnt  [l_idx] = w_lane_disp_cnt;
  assign w_ibuf_front_payload_next.resource_cnt.lsu_inst_valid[l_idx] = w_lane_disped_valid_or;
end endgenerate

assign w_ibuf_front_payload_next.resource_cnt.ld_inst_cnt = w_f3_inst_disped_cnt[INST_KIND_LD];
assign w_ibuf_front_payload_next.resource_cnt.st_inst_cnt = w_f3_inst_disped_cnt[INST_KIND_ST];

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_bru_inst_cnt (.in(w_f3_inst_disped[INST_KIND_BRU]), .out(w_f3_inst_disped_cnt[INST_KIND_BRU]));
assign w_ibuf_front_payload_next.resource_cnt.bru_inst_cnt     = w_f3_inst_disped_cnt[INST_KIND_BRU];
assign w_ibuf_front_payload_next.resource_cnt.bru_inst_valid   = w_f3_inst_disped[INST_KIND_BRU];
assign w_ibuf_front_payload_next.resource_cnt.bru_branch_valid = w_f3_inst_disped[INST_KIND_BRU] & w_f3_inst_kind[INST_KIND_BRU_BRANCH];

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_csu_inst_cnt (.in(w_f3_inst_disped[INST_KIND_CSU]), .out(w_f3_inst_disped_cnt[INST_KIND_CSU]));
assign w_ibuf_front_payload_next.resource_cnt.csu_inst_cnt   = w_f3_inst_disped_cnt[INST_KIND_CSU];
assign w_ibuf_front_payload_next.resource_cnt.csu_inst_valid = w_f3_inst_disped[INST_KIND_CSU];

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_fpu_inst_cnt (.in(w_f3_inst_disped[INST_KIND_FPU]), .out(w_f3_inst_disped_cnt[INST_KIND_FPU]));
generate for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_rsrc_loop
  localparam fpu_lane_width = scariv_conf_pkg::FPU_DISP_SIZE / scariv_conf_pkg::FPU_INST_NUM;
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[fpu_lane_width];
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(fpu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < fpu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i*scariv_conf_pkg::FPU_INST_NUM + f_idx), .SEL_WIDTH(scariv_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_f3_inst_disped[INST_KIND_FPU]), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .WORDS(fpu_lane_width)) fpu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_fpu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign w_ibuf_front_payload_next.resource_cnt.fpu_inst_cnt[f_idx] = w_lane_disp_cnt;
  assign w_ibuf_front_payload_next.resource_cnt.fpu_inst_valid[f_idx] = w_lane_disped_valid_or;
end
endgenerate

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  always_comb begin
    if (w_f3_inst_disp_mask[d_idx]) begin
      w_ibuf_front_payload_next.inst[d_idx].valid          = w_f3_inst_disp_mask[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].illegal_valid  = w_f3_inst_disped[INST_KIND_ILLEGAL][d_idx];
      w_ibuf_front_payload_next.inst[d_idx].inst           = w_f3_front_inst.inst[d_idx].inst;
      w_ibuf_front_payload_next.inst[d_idx].rvc_inst_valid = w_f3_front_inst.inst[d_idx].rvc_inst_valid;
      w_ibuf_front_payload_next.inst[d_idx].rvc_inst       = w_f3_front_inst.inst[d_idx].rvc_inst;
      w_ibuf_front_payload_next.inst[d_idx].pc_addr        = {w_f3_front_inst.pc_addr - w_f3_front_inst.inst[d_idx].fragmented, 1'b0} + {w_f3_front_inst.inst[d_idx].cache_pos, 1'b0} ;

      w_ibuf_front_payload_next.inst[d_idx].wr_reg.valid   = w_f3_rd_field_type[d_idx] != RD__;
      w_ibuf_front_payload_next.inst[d_idx].wr_reg.typ     = w_f3_rd_field_type[d_idx] == RD_R3 ? scariv_pkg::GPR : scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].wr_reg.regidx  = w_f3_front_inst.inst[d_idx].inst[11: 7];

      w_ibuf_front_payload_next.inst[d_idx].rd_regs[0].valid  = w_f3_rs1_field_type[d_idx] != R1__;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[0].typ    = w_f3_rs1_field_type[d_idx] == R1_R1 ? scariv_pkg::GPR : scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[0].regidx = w_f3_front_inst.inst[d_idx].inst[19:15];

      w_ibuf_front_payload_next.inst[d_idx].rd_regs[1].valid  = w_f3_rs2_field_type[d_idx] != R2__;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[1].typ    = w_f3_rs2_field_type[d_idx] == R2_R2 ? scariv_pkg::GPR : scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[1].regidx = w_f3_front_inst.inst[d_idx].inst[24:20];

      w_ibuf_front_payload_next.inst[d_idx].rd_regs[2].valid  = w_f3_rs3_field_type[d_idx] != R3__;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[2].typ    = scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[2].regidx = w_f3_front_inst.inst[d_idx].inst[31:27];

      w_ibuf_front_payload_next.inst[d_idx].cat        = w_f3_front_inst.inst[d_idx].cat;
      w_ibuf_front_payload_next.inst[d_idx].subcat     = w_f3_front_inst.inst[d_idx].subcat;

      w_ibuf_front_payload_next.inst[d_idx].pred_taken        = 'h0; // w_predict_taken_valid_lsb[d_idx] |
                                                                     // w_inst_is_call[d_idx] |
                                                                     // w_inst_is_ret [d_idx];
      w_ibuf_front_payload_next.inst[d_idx].bim_value         = 'h0; // w_expand_pred_info[d_idx].bim_value;
      w_ibuf_front_payload_next.inst[d_idx].btb_valid         = 'h0; // w_expand_pred_info[d_idx].btb_valid;
      w_ibuf_front_payload_next.inst[d_idx].pred_target_vaddr = 'h0; /* w_inst_is_call[d_idx] ? iq_call_next_vaddr_oh :
                                                                      w_inst_is_ret [d_idx] ? w_iq_ras_ret_vaddr :
                                                                      w_expand_pred_info[d_idx].pred_target_vaddr; */

      w_ibuf_front_payload_next.inst[d_idx].is_cond           = 1'b0; // w_expand_pred_info[d_idx].is_cond;
      w_ibuf_front_payload_next.inst[d_idx].is_call           = w_f3_inst_is_call[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].is_ret            = w_f3_inst_is_ret [d_idx];
      w_ibuf_front_payload_next.inst[d_idx].ras_index         = 'h0;  // r_ras_index; // w_expand_ras_info[d_idx].ras_index;

      w_ibuf_front_payload_next.inst[d_idx].gshare_index      = 'h0; // w_expand_pred_info[d_idx].gshare_index     ;
      w_ibuf_front_payload_next.inst[d_idx].gshare_bhr        = 'h0; // w_expand_pred_info[d_idx].gshare_bhr       ;

`ifdef SIMULATION
      w_ibuf_front_payload_next.inst[d_idx].kanata_id = r_kanata_cycle_count + d_idx;
`endif // SIMULATION

    end else begin // if (w_f3_inst_disp_mask[d_idx])
      w_ibuf_front_payload_next.inst[d_idx] = 'h0;
    end // else: !if(w_f3_inst_disp_mask[d_idx])
  end // always_comb
end
endgenerate

`ifdef SIMULATION
logic [ 63: 0] r_kanata_cycle_count;
scariv_pkg::grp_id_t w_valid_grp_id;
generate for (genvar g_idx = 0; g_idx < scariv_conf_pkg::DISP_SIZE; g_idx++) begin : sim_grp_loop
  assign w_valid_grp_id[g_idx] = w_ibuf_front_payload_next.inst[g_idx].valid;
end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_kanata_cycle_count <= 'h0;
  end else begin
    if (w_f3_valid_next & ibuf_front_if.ready) begin
      r_kanata_cycle_count <= r_kanata_cycle_count + $countones(w_valid_grp_id);
    end
  end
end
`endif // SIMULATION

`ifdef SIMULATION
function void dump_json(int fp);
  $fwrite(fp, "  \"scariv_inst_buffer\" : {\n");

  // for(int idx=0; idx < scariv_pkg::INST_BUF_SIZE; idx++) begin
  //   if (r_inst_queue[idx].valid) begin
  //     $fwrite(fp, "    \"r_inst_queue[%d]\" : {\n", idx);
  //     $fwrite(fp, "      valid     : \"%d\",\n", r_inst_queue[idx].valid);
  //     $fwrite(fp, "      data    : \"0x%x\",\n", r_inst_queue[idx].data);
  //     $fwrite(fp, "      pc      : \"0x%x\",\n", r_inst_queue[idx].pc << 1);
  //     $fwrite(fp, "      byte_en : \"0x%x\",\n", r_inst_queue[idx].byte_en);
  //     $fwrite(fp, "    },\n");
  //   end
  // end

  for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    if (ibuf_front_if.payload.inst[d_idx].valid) begin
      $fwrite(fp, "    \"ibuf_front_if.payload.inst[%d]\" : {", d_idx);
      $fwrite(fp, "      valid : %d,",      ibuf_front_if.payload.inst[d_idx].valid);
      $fwrite(fp, "      inst  : \"0x%08x\",",      ibuf_front_if.payload.inst[d_idx].inst);
      $fwrite(fp, "      pc_addr : \"0x%0x\",",    ibuf_front_if.payload.inst[d_idx].pc_addr);

      $fwrite(fp, "      rd_valid   : %d,", ibuf_front_if.payload.inst[d_idx].wr_reg.valid);
      $fwrite(fp, "      rd_type    : \"%d\",", ibuf_front_if.payload.inst[d_idx].wr_reg.typ);
      $fwrite(fp, "      rd_regidx  : %d,", ibuf_front_if.payload.inst[d_idx].wr_reg.regidx);

      $fwrite(fp, "      rs1_valid  : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[0].valid);
      $fwrite(fp, "      rs1_type   : \"%d\",", ibuf_front_if.payload.inst[d_idx].rd_regs[0].typ);
      $fwrite(fp, "      rs1_regidx : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[0].regidx);

      $fwrite(fp, "      rf2_valid  : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[1].valid);
      $fwrite(fp, "      rf2_type   : \"%d\",", ibuf_front_if.payload.inst[d_idx].rd_regs[1].typ);
      $fwrite(fp, "      rf2_regidx : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[1].regidx);

      $fwrite(fp, "      \"cat[d_idx]\" : \"%d\",", ibuf_front_if.payload.inst[d_idx].cat);
      $fwrite(fp, "    },\n");
    end
  end

  $fwrite(fp, "  },\n");
endfunction // dump

logic [63: 0] r_sim_cycle_count;
logic [63: 0] r_sim_ibuf_max_period;
logic [63: 0] r_sim_ibuf_entry_count;
logic [63: 0] r_sim_ibuf_issue_count;
logic [63: 0] r_sim_ibuf_issue_inst_count;

disp_t sim_disp_valid;

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : sim_disp_loop
  assign sim_disp_valid[d_idx] = ibuf_front_if.payload.inst[d_idx].valid;
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_sim_ibuf_max_period  <= 'h0;
    r_sim_ibuf_entry_count <= 'h0;
    r_sim_cycle_count  <= 'h0;
    r_sim_ibuf_issue_count <= 'h0;
    r_sim_ibuf_issue_inst_count <= 'h0;
  end else begin
    r_sim_cycle_count <= r_sim_cycle_count + 'h1;
    if (r_sim_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_sim_ibuf_max_period  <= 'h0;
      r_sim_ibuf_entry_count <= 'h0;
      r_sim_ibuf_issue_count <= 'h0;
      r_sim_ibuf_issue_inst_count <= 'h0;
    end else begin
      if (!w_inst_buf_empty) begin
        if (w_inst_buf_full) begin
          r_sim_ibuf_max_period  <= r_sim_ibuf_max_period + 'h1;
        end
        r_sim_ibuf_entry_count <= r_sim_ibuf_entry_count + $countones(u_inst_queue.r_valids);
      end
      if (ibuf_front_if.valid & ibuf_front_if.ready) begin
        r_sim_ibuf_issue_count <= r_sim_ibuf_issue_count + 'h1;
        r_sim_ibuf_issue_inst_count <= r_sim_ibuf_issue_inst_count + $countones(sim_disp_valid);
      end
    end // else: !if(r_sim_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

function void dump_perf (int fp);
  $fwrite(fp, "  \"inst_buffer\" : {");
  $fwrite(fp, "  \"issued_times\" : %5d, ", r_sim_ibuf_issue_count);
  $fwrite(fp, "  \"issued_insts\" : %5d, ", r_sim_ibuf_issue_inst_count);
  $fwrite(fp, "  \"max_period\" : %5d, ", r_sim_ibuf_max_period);
  $fwrite(fp, "  \"average count\" : %5f},\n", r_sim_ibuf_entry_count / 1000.0);
endfunction // dump_perf

  `ifdef DUMP_KANATA

import "DPI-C" function void log_dispatch
(
 input longint timeinfo,
 input longint id,
 input longint paddr,
 input int     inst
);

import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (ibuf_front_if.valid & ibuf_front_if.ready) begin
      for (int i = 0; i < scariv_conf_pkg::DISP_SIZE; i++) begin
        if (ibuf_front_if.payload.inst[i].valid) begin
          log_dispatch ($time, ibuf_front_if.payload.inst[i].kanata_id,
                        ibuf_front_if.payload.inst[i].pc_addr, ibuf_front_if.payload.inst[i].inst);
          log_stage (ibuf_front_if.payload.inst[i].kanata_id, "Di");
        end
      end
    end
  end
end

  `endif // DUMP_KANATA

`endif // SIMULATION


endmodule // scariv_front_decoder
