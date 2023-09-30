package scariv_vec_pkg;

parameter VLEN_W = riscv_vec_conf_pkg::VLEN_W;
parameter VLENB = VLEN_W / 8;
parameter VLENBMAX = VLENB * 8;
parameter VLENBMAX_W = $clog2(VLENBMAX);
typedef logic [$clog2(VLENBMAX)-1: 0] vlenbmax_t;
parameter VEC_STEP_W = riscv_vec_conf_pkg::VLEN_W / riscv_vec_conf_pkg::DLEN_W;

typedef logic [$clog2(VEC_STEP_W)-1: 0]         vec_pos_t;
typedef logic [riscv_vec_conf_pkg::VLEN_W-1: 0] vlen_t;
typedef logic [riscv_vec_conf_pkg::DLEN_W-1: 0] dlen_t;

parameter VEC_RNID_SIZE = 128;
parameter VEC_RNID_W    = $clog2(VEC_RNID_SIZE);

parameter VLVTYPE_REN_SIZE = 8;
parameter VLVTYPE_REN_W = $clog2(VLVTYPE_REN_SIZE);
typedef logic [$clog2(VLVTYPE_REN_SIZE)-1: 0] vlvtype_ren_idx_t;

typedef struct packed {
  logic [ 2: 0]  vlmul;
  logic [ 2: 0]  vsew;
  logic          vta;
  logic          vma;
} vtype_t;

typedef struct packed {
  vlenbmax_t vl;
  vtype_t    vtype;
} vlvtype_t;

typedef struct packed {
  logic          valid;
  vtype_t        vtype;
  logic          vill;
  vlenbmax_t     vl;
} csr_write_t;
typedef struct packed {
  vlenbmax_t vl;
  vlenbmax_t vlmax;
} csr_info_t;

function automatic vlenbmax_t calc_vlmax(logic [ 2: 0] vlmul,
                                         logic [ 2: 0] vsew);
  return (VLENB << vlmul) >> vsew;

endfunction

endpackage // scariv_vec_pkg


// ======================
// Vector Interfaces
// ======================
interface vec_csr_if;

  import scariv_vec_pkg::*;

  csr_write_t write;
  csr_info_t  info;

  modport master (
    input  write,
    output info
  );

  modport slave (
    output write,
    input  info
  );

endinterface // vec_csr_if


interface vlvtype_upd_if;
  import scariv_vec_pkg::*;

  logic             valid;
  vlvtype_t         vlvtype;
  vlvtype_ren_idx_t index;

  modport master (
    output valid,
    output vlvtype,
    output index
  );

  modport slave (
    input valid,
    input vlvtype,
    input index
  );

endinterface // vlvtype_upd_if


interface vlvtype_commit_if;
  import scariv_vec_pkg::*;

  logic             valid;
// vlvtype_ren_idx_t index;

  modport master (
    output valid
   //  output index
  );

  modport slave (
    input valid
    // input index
  );

endinterface // vlvtype_commit_if



interface vlvtype_req_if;

  import scariv_vec_pkg::*;

  logic             valid;
  logic             checkpt_push_valid;
  logic             ready;
  logic             full;
  vlvtype_ren_idx_t index;
  vlvtype_t         vlvtype;

  modport master (
    output valid,
    output checkpt_push_valid,
    input  ready,
    input  full,
    input  index,
    input  vlvtype
  );

  modport slave (
    input  valid,
    input  checkpt_push_valid,
    output ready,
    output full,
    output index,
    output vlvtype
  );

endinterface // vlvtype_resolve_if


interface vec_regread_if;

  localparam WIDTH = riscv_vec_conf_pkg::DLEN_W;

  logic                      valid;
  scariv_pkg::rnid_t         rnid;
  scariv_vec_pkg::vec_pos_t  pos;
  logic [WIDTH-1: 0]         data;

  modport master(output valid, output rnid, output pos, input data);

  modport slave(input valid, input rnid, input pos, output data);

endinterface // vec_regread_if


interface vec_regwrite_if;

  localparam WIDTH = riscv_vec_conf_pkg::DLEN_W;

  logic                     valid;
  scariv_pkg::rnid_t        rd_rnid;
  scariv_vec_pkg::vec_pos_t rd_pos;
  logic [WIDTH-1: 0]        rd_data;

  modport master (
    output valid,
    output rd_rnid,
    output rd_pos,
    output rd_data
  );

  modport slave (
    input valid,
    input rd_rnid,
    input rd_pos,
    input rd_data
  );

endinterface // vec_regwrite_if
