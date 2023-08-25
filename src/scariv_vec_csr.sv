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

   vec_csr_if.master vec_csr_if
   );

riscv_pkg::xlen_t             r_start;
logic [$clog2(VLENBMAX)-1: 0] r_vl;
typedef struct packed {
  logic [ 2: 0]  vlmul;
  logic [ 2: 0]  vsew;
  logic          vta;
  logic          vma;
} vtype_t;
vtype_t          r_vtype;
logic            r_vill;
logic [$clog2(VLENBMAX)-1: 0] w_vlmax;

riscv_pkg::xlen_t r_vrm;
riscv_pkg::xlen_t r_vcsr;
riscv_pkg::xlen_t r_vxsat;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    vec_csr_if.info <= 'h0;
  end else begin
    vec_csr_if.info.vl    <= r_vl;
    vec_csr_if.info.vlmax <= w_vlmax;
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


endmodule // scariv_vec_csr
