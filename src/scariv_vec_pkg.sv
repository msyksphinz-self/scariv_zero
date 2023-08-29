package scariv_vec_pkg;

parameter VLEN = 128;
parameter VLENB = VLEN / 8;
parameter VLENBMAX = VLENB * 8;
parameter VLENBMAX_W = $clog2(VLENBMAX);
typedef logic [$clog2(VLENBMAX)-1: 0] vlenbmax_t;

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
