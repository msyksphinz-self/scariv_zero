#pragma once
#include <svdpi.h>

extern "C" {
  void initial_ras(long long ras_length);
  void step_ras (long long rtl_time,
                 int rtl_cmt_id, int rtl_grp_id,
                 long long ras_index);
}
