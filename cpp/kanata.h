#pragma once
#include <svdpi.h>

void init_kanata ();
void start_kanata (long long cycle);
void proceed_kanata_cycle(int cycle);

extern "C" {
  void log_dispatch(long long time, long long id, long long pc, int inst);
  void log_stage (long long id, const char *stage);
  void retire_inst (long long id, long long retire_id, bool dead);
}
