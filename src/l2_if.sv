interface l2_req_if;
  mrh_pkg::l2_req_t payload;
  modport master(
    output valid,
    output payload
  );
  modport slave(
    input ready
  );
endinterface

interface l2_resp_if;
  mrh_pkg::l2_resp_t payload;
  modport master(
    output ready
  );
  modport slave(
    input valid,
    input payload
  );
endinterface

