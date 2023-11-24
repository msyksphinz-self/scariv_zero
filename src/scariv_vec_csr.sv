// ------------------------------------------------------------------------
// NAME : scariv_vec_csu
// TYPE : module
// ------------------------------------------------------------------------
// Vector CSR Access Unit
// ------------------------------------------------------------------------
// vl / vtype / vlenb / vstart / vrm / vcsr / vxsat
// ------------------------------------------------------------------------

module scariv_vec_csr
  import scariv_vec_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   csr_rd_if.slave  read_csr_vec_if,
   csr_wr_if.slave  write_csr_vec_if,

   vec_csr_if.master vec_csr_if
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

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    vec_csr_if.info <= 'h0;
  end else begin
    vec_csr_if.info.vl    <= r_vl;
    vec_csr_if.info.vlmax <= w_vlmax;
    vec_csr_if.info.vlmul <= r_vtype.vlmul;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_vl <= 'h0;
    r_vtype <= 'h0;
  end else begin
    if (vec_csr_if.write.valid) begin
      r_vl    <= vec_csr_if.write.vl;
      r_vtype <= vec_csr_if.write.vtype;
      r_vill  <= vec_csr_if.write.vill;
    end
  end
end

assign w_vlmax = (VLENB << r_vtype.vlmul) >> r_vtype.vsew;


always_comb begin
  read_csr_vec_if.resp_error = 1'b0;
  if (read_csr_vec_if.valid) begin
    case (read_csr_vec_if.addr)
      `SYSREG_ADDR_VSTART : read_csr_vec_if.data = r_vstart;
      `SYSREG_ADDR_VXSAT  : read_csr_vec_if.data = r_vxsat;
      `SYSREG_ADDR_VXRM   : read_csr_vec_if.data = r_vxrm;
      `SYSREG_ADDR_VCSR   : read_csr_vec_if.data = r_vcsr;
      `SYSREG_ADDR_VL     : read_csr_vec_if.data = r_vl;
      `SYSREG_ADDR_VTYPE  : read_csr_vec_if.data = r_vtype;
      `SYSREG_ADDR_VLENB  : read_csr_vec_if.data = VLENB;
      default : begin
        read_csr_vec_if.data = 'h0;
        read_csr_vec_if.resp_error = 1'b1;
      end
    endcase // case (read_csr_vec_if.addr)
  end else begin
    read_csr_vec_if.data = 'h0;
  end // if (read_csr_vec_if.valid)
end // always_comb

endmodule // scariv_vec_csr
