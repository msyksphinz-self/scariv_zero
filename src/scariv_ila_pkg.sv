package scariv_ila_pkg;

typedef struct packed {
  scariv_pkg::cmt_id_t      head_ptr;
  scariv_pkg::cmt_id_t      tail_ptr;
  scariv_pkg::rob_entry_t   entry;
  scariv_pkg::rob_payload_t payload;
} ila_debug_rob_t;


typedef struct packed {
  ila_debug_rob_t rob;
} ila_debug_tile_t;


endpackage // scariv_ila_pkg
