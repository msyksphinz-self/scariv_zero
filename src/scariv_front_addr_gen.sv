// ------------------------------------------------------------------------
// NAME : scariv_front_addr_gen
// TYPE : module
// ------------------------------------------------------------------------
// Frontend Instruction Address Generator
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_front_addr_gen
  import scariv_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 // PC Update from Committer
 commit_if.monitor commit_if,
 // Branch Tag Update Signal
 br_upd_if.slave     br_upd_if,

 /* CSR information */
 csr_info_if.slave  csr_info,

 input  logic   i_f0_req_ready,
 input  vaddr_t i_f0_vaddr,
 output logic   o_int_flush_valid,
 output vaddr_t o_vaddr
 );


logic   w_br_flush;
assign w_br_flush  = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;


always_comb begin
  o_int_flush_valid = 1'b0;
  if (commit_if.is_flushed_commit()) begin
    if (commit_if.payload.int_valid) begin
      case (commit_if.payload.except_type)
        riscv_common_pkg::MACHINE_EXTERNAL_INT : begin
          /* verilator lint_off WIDTHCONCAT */
          o_vaddr = {csr_info.mtvec [riscv_pkg::XLEN_W-1: 1], 1'b0} + {riscv_common_pkg::MACHINE_EXTERNAL_INT, 2'b00};
          o_int_flush_valid = 1'b1;
        end
        riscv_common_pkg::SUPER_EXTERNAL_INT : begin
          /* verilator lint_off WIDTHCONCAT */
          o_vaddr = {csr_info.mtvec [riscv_pkg::XLEN_W-1: 1], 1'b0} + {riscv_common_pkg::SUPER_EXTERNAL_INT, 2'b00};
          o_int_flush_valid = 1'b1;
        end
        riscv_common_pkg::MACHINE_TIMER_INT : begin
          /* verilator lint_off WIDTHCONCAT */
          o_vaddr = {csr_info.mtvec [riscv_pkg::XLEN_W-1: 1], 1'b0} + {riscv_common_pkg::MACHINE_TIMER_INT, 2'b00};
          o_int_flush_valid = 1'b1;
        end
        riscv_common_pkg::SUPER_TIMER_INT : begin
          /* verilator lint_off WIDTHCONCAT */
          o_vaddr = {csr_info.mtvec [riscv_pkg::XLEN_W-1: 1], 1'b0} + {riscv_common_pkg::SUPER_TIMER_INT, 2'b00};
          o_int_flush_valid = 1'b1;
        end
        riscv_common_pkg::MACHINE_SOFT_INT : begin
          /* verilator lint_off WIDTHCONCAT */
          o_vaddr = {csr_info.mtvec [riscv_pkg::XLEN_W-1: 1], 1'b0} + {riscv_common_pkg::MACHINE_SOFT_INT, 2'b00};
          o_int_flush_valid = 1'b1;
        end
        riscv_common_pkg::SUPER_SOFT_INT : begin
          /* verilator lint_off WIDTHCONCAT */
          o_vaddr = {csr_info.mtvec [riscv_pkg::XLEN_W-1: 1], 1'b0} + {riscv_common_pkg::SUPER_SOFT_INT, 2'b00};
          o_int_flush_valid = 1'b1;
        end
      endcase // case (commit_if.payload.except_type)
    end else begin
      case (commit_if.payload.except_type)
        SILENT_FLUSH   : o_vaddr = commit_if.payload.epc + 4;
        LMUL_CHANGE    : o_vaddr = scariv_vec_pkg::LMUL_CHANGE_HANDLER_BASE_ADDR;
        SELF_KILL_REPLAY : o_vaddr = commit_if.payload.epc;
        ANOTHER_FLUSH  : o_vaddr = commit_if.payload.epc;
        MRET           : o_vaddr = csr_info.mepc [riscv_pkg::XLEN_W-1: 0];
        SRET           : o_vaddr = csr_info.sepc [riscv_pkg::XLEN_W-1: 0];
        URET           : o_vaddr = csr_info.uepc [riscv_pkg::XLEN_W-1: 0];
        ECALL_M,
        ECALL_S,
        ECALL_U,
        BREAKPOINT,
        INST_ACC_FAULT,
        LOAD_ACC_FAULT,
        STAMO_ACC_FAULT,
        INST_PAGE_FAULT,
        LOAD_PAGE_FAULT,
        STAMO_PAGE_FAULT,
        INST_ADDR_MISALIGN,
        LOAD_ADDR_MISALIGN,
        STAMO_ADDR_MISALIGN,
        ILLEGAL_INST        :
          if (csr_info.medeleg[commit_if.payload.except_type]) begin
            o_vaddr = csr_info.stvec[riscv_pkg::XLEN_W-1: 0];
          end else begin
            o_vaddr = csr_info.mtvec[riscv_pkg::XLEN_W-1: 0];
          end
        default           : begin
          o_vaddr = 'h0;
`ifdef SIMULATION
          $fatal (0, "This exception not supported now : %d", commit_if.payload.except_type);
`endif // SIMULATION
        end
      endcase // case (commit_if.payload.except_type)
    end // else: !if(commit_if.payload.int_valid)
  end else if (w_br_flush) begin
    o_vaddr = br_upd_if.target_vaddr;
  end else if (!i_f0_req_ready) begin
    o_vaddr = i_f0_vaddr;
  end else begin // if (|(commit_if.payload.except_valid & ~commit_if.payload.dead_id))
    o_vaddr = (i_f0_vaddr & ~((1 << $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W))-1)) +
              (1 << $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W));
  end
end // always_comb

endmodule // scariv_front_addr_gen
