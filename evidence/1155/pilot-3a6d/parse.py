#!/usr/bin/env python3
"""Validate existing Firefox export granularity, without inventing per-call measurements."""
import csv,json,pathlib
p=pathlib.Path(__file__).resolve().parent
runs={mode:json.loads((p/f'{mode}-results.json').read_text()) for mode in ['baseline','wall']}
rows=[]
for b,w in zip(runs['baseline'],runs['wall']):
 d=json.loads((p/f'{b["case"]}-wall.profile.json').read_text())
 frames=[];names=[]; located=0;markers=0
 for t in d['threads']:
  f=t['funcTable'];n=f['length'];frames.extend([None]*n)
  located+=sum(any(f[k][i] is not None for k in ['fileName','lineNumber','columnNumber']) for i in range(n))
  names.extend(t['stringArray'][i] for i in f['name'])
  markers+=t['markers']['length']
 tags=sorted(set(x for x in names if 'tacticPolytime' in x))
 rows.append(dict(case=b['case'],baseline_exit=b['returncode'],baseline_process_wall_seconds=b['process_wall_seconds'],wall_diagnostic_exit=w['returncode'],wall_diagnostic_process_wall_seconds=w['process_wall_seconds'],single_run_process_wall_difference_seconds=w['process_wall_seconds']-b['process_wall_seconds'],maxHeartbeats=200000,async_override=False,export_threads=len(d['threads']),export_function_entries=len(frames),entries_with_any_source_coordinate=located,polytime_frame_tags=tags,export_markers=markers,authored_call_wall_ms=None,authored_call_raw_heartbeats=None,authored_call_user_heartbeats=None,final_proof_rules=None,heartbeat_run='not run: authored-span mapping unsuitable',rule_trace_run='not run: authored-span mapping unsuitable',node_failure_or_censor_status='not recoverable from this export',measurement_status='process wall only; no attributable authored-call metric'))
(p/'parsed.json').write_text(json.dumps(rows,indent=2)+'\n')
with (p/'parsed.csv').open('w',newline='') as f:
 writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');writer.writeheader();writer.writerows(rows)
print(json.dumps(rows,indent=2))
