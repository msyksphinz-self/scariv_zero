#pragma once
#include <svdpi.h>

extern "C" {
  void log_dispatch(long long id, long long pc, int inst);
  void log_stage (long long id, char *stage);
}
