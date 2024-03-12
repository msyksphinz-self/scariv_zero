// ------------------------------------------------------------------------
// NAME : scariv_vlsu_address_gen
// TYPE : module
// ------------------------------------------------------------------------
// Address Generator for Vector LSU
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vlsu_address_gen
  import decoder_lsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 input logic                     i_valid,
 input logic                     i_flush_valid,

 input riscv_pkg::xlen_t         i_rs1_base,

 input logic                     i_is_last_lmul_index,
 input scariv_vec_pkg::vec_pos_t i_vec_step_index,
 output scariv_pkg::vaddr_t      o_vaddr,
 output logic [$clog2(scariv_vec_pkg::DLENB)-1: 0]   o_reg_offset,
 output logic                    o_stall,
 output logic                    o_req_splitted
 );

logic [$clog2(scariv_vec_pkg::VLENB*8)-1: 0]    r_acc_addr_offset;
logic [$clog2(scariv_vec_pkg::DLENB)-1: 0]    r_reg_offset;
scariv_vec_pkg::vec_pos_t r_vec_step_index;

logic [riscv_pkg::VADDR_W-1:$clog2(DCACHE_DATA_B_W)] r_vaddr_next_cacheline;

always_comb begin
  if (r_state == USTRIDE_GEN) begin
    o_vaddr      = {r_vaddr_next_cacheline, {$clog2(DCACHE_DATA_B_W){1'b0}}};
    o_reg_offset = r_reg_offset;
  end else begin
    o_vaddr      = i_rs1_base + r_acc_addr_offset;
    o_reg_offset = 'h0;
  end
end

typedef enum logic [ 1: 0] {
   INIT = 0,
   USTRIDE_GEN = 1
} state_t;

state_t r_state;

logic        w_cache_misaligned;
generate if (DCACHE_DATA_B_W <= scariv_vec_pkg::DLENB) begin
  assign w_cache_misaligned = o_vaddr[$clog2(scariv_vec_pkg::DLENB)-1: 0] != 'h0;
end else begin
  assign w_cache_misaligned = (&o_vaddr[$clog2(DCACHE_DATA_B_W)-1: $clog2(scariv_vec_pkg::DLENB)])  &
                              (o_vaddr[$clog2(scariv_vec_pkg::DLENB)-1: 0] != 0);
end endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= INIT;
    r_acc_addr_offset <= 'h0;
  end else begin
    if (i_flush_valid) begin
      r_state <= INIT;
      r_acc_addr_offset <= 'h0;
    end else begin
      case (r_state)
        INIT : begin
          if (i_valid) begin
            if (w_cache_misaligned) begin
              r_state <= USTRIDE_GEN;
              r_vec_step_index       <= i_vec_step_index;
              r_vaddr_next_cacheline <= o_vaddr[riscv_pkg::VADDR_W-1:$clog2(DCACHE_DATA_B_W)] + 'h1;
              r_reg_offset           <= scariv_vec_pkg::DLENB - o_vaddr[scariv_vec_pkg::DLENB-1: 0];
            end else begin
              r_acc_addr_offset <= update_offset (i_vec_step_index, r_acc_addr_offset);
            end
          end
        end
        USTRIDE_GEN : begin
          r_state           <= INIT;
          r_acc_addr_offset <= update_offset (r_vec_step_index, r_acc_addr_offset);
          r_reg_offset      <= 'h0;
        end
        default : begin
          r_state <= INIT;
        end
      endcase // case (r_state)
    end // else: !if(i_flush_valid)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_stall        = (r_state == INIT) & w_cache_misaligned & i_valid;
assign o_req_splitted = (r_state != INIT);

function automatic logic [$clog2(scariv_vec_pkg::VLENB*8)-1: 0] update_offset (scariv_vec_pkg::vec_pos_t step, logic [$clog2(scariv_vec_pkg::VLENB*8)-1: 0] current_offset);
  if (i_is_last_lmul_index & (step == scariv_vec_pkg::VEC_STEP_W-1)) begin
    return 'h0;
  end else begin
    return current_offset + scariv_vec_pkg::DLENB;
  end
endfunction // update_offset


endmodule // scariv_vlsu_address_gen
