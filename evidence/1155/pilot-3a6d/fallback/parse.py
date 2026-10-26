#!/usr/bin/env python3
"""Parse successful one-call tactic counters and preserve attempted-rule evidence separately."""
import csv,json,pathlib,re
p=pathlib.Path(__file__).resolve().parent;results=json.loads((p/'results.json').read_text());rows=[]
for case in ['guide','supplied']:
 run=next(x for x in results if x['case']==case and x['mode']=='heartbeats')
 log=(p/f'{case}-heartbeats.log').read_text();match=re.fullmatch(r'\s*(\d+)\s*',log)
 raw=int(match[1]) if match and run['returncode']==0 else None
 src=(p/run['source']).read_text();line=next(i for i,l in enumerate(src.splitlines(),1) if '#count_heartbeats polytime' in l)
 trace=(p/f'{case}-rules.log').read_text();applications=[]
 for n,l in enumerate(trace.splitlines(),1):
  if '[Meta.Tactic.fun_prop]' in l and 'applying:' in l:
   applications.append(dict(trace_line=n,text=l.strip(),theorem=l.split('applying:',1)[1].strip(),locally_successful_trace_marker=('✅' in l),final_proof_contribution=None))
 (p/f'{case}-attempted-rules.json').write_text(json.dumps(applications,indent=2)+'\n')
 rows.append(dict(case=case,source_pin='3a6d770645c1217689da774f519cd785c253d8a2',instrumented_source=run['source'],authored_counter_line=line,mapping='one authored positive/counter per file; manually anchored, not profiler export',acceptance='pass at original200000; separate baseline',counter_exit=run['returncode'],inclusive_raw_heartbeats=raw,inclusive_user_heartbeats=raw/1000 if raw is not None else None,user_heartbeat_limit=200000,async_false_inside_counter=True,added_import='Mathlib.Util.CountHeartbeats',counter_includes='saveState/options/evalTactic overhead; no restore with revert=false; logging excluded',counter_process_wall_seconds=run['process_wall_seconds'],per_call_wall_seconds=None,attempted_funprop_application_lines=len(applications),attempts_are_final_proof=False,final_proof_rules=None,negative_heartbeat_count=None,negative_status='separate original fail_if_success passed; no failure count measured',censored_nodes='unknown; tactic counter emits only on success'))
(p/'parsed.json').write_text(json.dumps(rows,indent=2)+'\n')
with (p/'parsed.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
print(json.dumps(rows,indent=2))
