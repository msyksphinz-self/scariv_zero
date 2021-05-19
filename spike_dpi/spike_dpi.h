#pragma once

extern "C" {
  void initial_spike (const char *filename, int rv_xlen);
  void step_spike(long long time, long long rtl_pc,
                  int rtl_priv,
                  int rtl_exception, int rtl_exception_cause,
                  int rtl_cmt_id, int rtl_grp_id,
                  int rtl_insn,
                  int rtl_wr_valid, int rtl_wr_gpr_addr,
                  int rtl_wr_gpr_rnid, long long rtl_wr_val);
  void stop_sim(int code);
}
