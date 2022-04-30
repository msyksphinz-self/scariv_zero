#include <map>
#include "disasm.h"
#include "kanata.h"

FILE *kanata_fp = NULL;
disassembler_t *disasm;
bool log_started = false;

void init_kanata ()
{
  if ((kanata_fp = fopen("kanata.log", "w")) == NULL) {
    perror("failed to open log file");
    exit(EXIT_FAILURE);
  }
  fprintf(kanata_fp, "Kanata 0004\n");
  disasm = new disassembler_t (64);
}

void start_kanata (long long cycle)
{
  fprintf (kanata_fp, "C=   %lld\n", cycle);
}

void proceed_kanata_cycle(int cycle)
{
  if (log_started) {
    fprintf (kanata_fp, "C   %d\n", cycle);
  }
}


std::map<long long, const char *> stage_map;

void log_dispatch(long long time, long long id, long long pc, int inst)
{
  if (!log_started) {
    start_kanata (time);
    log_started = true;
  }
  fprintf (kanata_fp, "L %lld 0 %08llx:%s\n",
           id, pc, disasm->disassemble(inst).c_str());
}


void log_stage (long long id, const char *stage)
{
  decltype(stage_map)::iterator it = stage_map.find(id);
  if (it != stage_map.end()) {
    fprintf (kanata_fp, "E %lld 0 %s\n", id, it->second);
    stage_map.erase (id);
  }
  fprintf (kanata_fp, "S %lld 0 %s\n", id, stage);
  stage_map.insert (std::make_pair(id, stage));
}


void retire_inst (long long id, bool retire)
{
  decltype(stage_map)::iterator it = stage_map.find(id);
  if (it != stage_map.end()) {
    stage_map.erase (id);
    fprintf (kanata_fp, "E %lld 0 %s\n", id, it->second);
  }
  fprintf (kanata_fp, "R %lld %lld %d\n", id, id, retire ? 0 : 1);
}
