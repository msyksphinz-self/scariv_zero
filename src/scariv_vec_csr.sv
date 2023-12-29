// ------------------------------------------------------------------------
// NAME : scariv_vec_csu
// TYPE : module
// ------------------------------------------------------------------------
// Vector CSR Access Unit
// ------------------------------------------------------------------------
// vl / vtype / vlenb / vstart / vrm / vcsr / vxsat
// ------------------------------------------------------------------------

module scariv_vec_csr
  import scariv_pkg::*;
  import scariv_vec_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   csr_rd_if.slave  read_csr_vec_if,
   csr_wr_if.slave  write_csr_vec_if,

   input scariv_pkg::commit_blk_t i_commit,

   output logic o_lmul_exception_mode
   );

riscv_pkg::xlen_t             r_vstart;
logic [$clog2(VLENBMAX)-1: 0] r_vl;
typedef struct packed {
  logic          vma;
  logic          vta;
  logic [ 2: 0]  vsew;
  logic [ 2: 0]  vlmul;
} vtype_t;
vtype_t          r_vtype;
logic            r_vill;
logic [$clog2(VLENBMAX)-1: 0] w_vlmax;

riscv_pkg::xlen_t r_vxrm;
riscv_pkg::xlen_t r_vcsr;
riscv_pkg::xlen_t r_vxsat;

logic [31: 0]                 r_vscratch; // keep for VLMUL change

logic                         r_lmul_exception_mode;

assign w_vlmax = (VLENB << r_vtype.vlmul) >> r_vtype.vsew;

always_comb begin
  read_csr_vec_if.resp_error = 1'b0;
  if (read_csr_vec_if.valid) begin
    case (read_csr_vec_if.addr)
      `SYSREG_ADDR_VSTART   : read_csr_vec_if.data = r_vstart;
      `SYSREG_ADDR_VXSAT    : read_csr_vec_if.data = r_vxsat;
      `SYSREG_ADDR_VXRM     : read_csr_vec_if.data = r_vxrm;
      `SYSREG_ADDR_VCSR     : read_csr_vec_if.data = r_vcsr;
      `SYSREG_ADDR_VL       : read_csr_vec_if.data = r_vl;
      `SYSREG_ADDR_VTYPE    : read_csr_vec_if.data = r_vtype;
      `SYSREG_ADDR_VSCRATCH : read_csr_vec_if.data = r_vscratch;
      `SYSREG_ADDR_VLENB    : read_csr_vec_if.data = VLENB;
      default : begin
        read_csr_vec_if.data = 'h0;
        read_csr_vec_if.resp_error = 1'b1;
      end
    endcase // case (read_csr_vec_if.addr)
  end else begin
    read_csr_vec_if.data = 'h0;
  end // if (read_csr_vec_if.valid)
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_lmul_exception_mode <= 1'b0;
  end else begin
    if (is_flushed_commit(i_commit)) begin
      case (i_commit.except_type)
        LMUL_CHANGE : begin
          r_lmul_exception_mode <= 1'b1;
          r_vscratch <= i_commit.tval;
        end
        MRET,
        SRET,
        URET        : r_lmul_exception_mode <= 1'b0;
        default     : begin end
      endcase // case (i_commit.except_type)
    end
  end
end

assign o_lmul_exception_mode = r_lmul_exception_mode;

endmodule // scariv_vec_csr
