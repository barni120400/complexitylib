#!/usr/bin/env python3
"""Validate only the three manually mapped pilot records; never impute missing data."""
import pathlib,json,csv,hashlib
p=pathlib.Path(__file__).resolve().parent
side=json.loads((p/'sidecar.json').read_text());sha=hashlib.sha256((p/'sidecar.json').read_bytes()).hexdigest()
assert hashlib.sha256((p/'Wrapper.lean').read_bytes()).hexdigest()==side['implementation_sha256']
runs=json.loads((p/'results.json').read_text());mapping={x['call_token']:x for x in side['calls']}
assert len(mapping)==3 and len(set(x['call_id'] for x in mapping.values()))==3
assert all(x['returncode']==0 and x['run_id']==side['run_id'] and x['sidecar_sha256']==sha for x in runs)
assert len(runs)==6
records=[]
for f in p.glob('*.events.jsonl'):
 for n,l in enumerate(f.read_text().splitlines(),1):
  x=json.loads(l)
  assert x['call_token'] in mapping and x['run_id']==side['run_id'] and x['sidecar_sha256']==sha
  records.append(x)
assert len(records)==6
rows=[]
for token,item in mapping.items():
 begins=[x for x in records if x['call_token']==token and x['phase']=='begin']
 assert len(begins)==1
 b=begins[0];ends=[x for x in records if x['phase']=='end' and x['event_id']==b['event_id']]
 assert len(ends)<=1
 e=ends[0] if ends else None
 status=e['status'] if e else 'censored_unknown'
 agrees=(e is not None and status==item['expected'])
 if status=='returned':agrees=agrees and e['goals_after']==0
 assert b['maxHeartbeats_user']==200000 and b['child_kind']=='Cslib.Tactic.PolyTime.tacticPolytime'
 rows.append(dict(case=item['case'],call_token=token,full_call_id=item['call_id'],original_path=item['original_path'],original_line=item['original_line'],original_byte_start=item['original_byte_start'],original_byte_end=item['original_byte_end'],run_id=side['run_id'],sidecar_sha256=sha,runtime_status=status,goals_after=e['goals_after'] if e else None,raw_current_thread_heartbeats=e['raw_thread_heartbeats'] if e else None,user_heartbeats=e['raw_thread_heartbeats']/1000 if e else None,forwarded_interval_wall_ns=e['wall_nanoseconds'] if e else None,async_option=b['async_option'],user_limit=200000,baseline_import_wrapped_commands_pass=True,expected_outcome_agrees=agrees,following_proof_restoration_control=(item['case']=='missing' and agrees),final_proof_dependencies=None,methodology_approved=False,censored=(e is None)))
assert all(x['expected_outcome_agrees'] for x in rows),'stop on mapping/outcome mismatch'
(p/'parsed.json').write_text(json.dumps(rows,indent=2)+'\n')
with (p/'parsed.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
print(json.dumps(rows,indent=2))
