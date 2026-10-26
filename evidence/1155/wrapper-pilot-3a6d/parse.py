#!/usr/bin/env python3
"""Parse only the bounded attempted experiment; never treat absent/endless events as success."""
import pathlib,json,csv
p=pathlib.Path(__file__).resolve().parent
mapping=json.loads((p/'sidecar.json').read_text());runs=json.loads((p/'results.json').read_text())
events=[]
for f in p.glob('*.events.jsonl'):
 for n,line in enumerate(f.read_text().splitlines(),1):events.append((f.name,n,json.loads(line)))
rows=[]
for item in mapping:
 ev=[x for _,_,x in events if x['call_id']==item['call_id']]
 begins=[x for x in ev if x['phase']=='begin'];ends=[x for x in ev if x['phase']=='end']
 for b in begins:
  finish=[x for x in ends if x['event_id']==b['event_id']]
  assert len(finish)<=1,'ambiguous/duplicate end'
  e=finish[0] if finish else None
  rows.append(dict(case=item['case'],call_id=item['call_id'],runtime_event=b['event_id'],status=e['status'] if e else 'censored_unknown',goals_after=e.get('goals_after') if e else None,raw_thread_heartbeats=e.get('raw_thread_heartbeats') if e else None,user_heartbeats=e['raw_thread_heartbeats']/1000 if e else None,wall_nanoseconds=e.get('wall_nanoseconds') if e else None,command_returncode=next(x['returncode'] for x in runs if x['mode']=='wrapped' and x['file']=='guide'),accepted_measurement=False,disposition='command rejected by unchanged Verso line-length check; no proof-completion claim',async_option=b['async_option'],maxHeartbeats_user=b['maxHeartbeats_user']))
 if not begins:rows.append(dict(case=item['case'],call_id=item['call_id'],runtime_event=None,status='not_run_after_stop',goals_after=None,raw_thread_heartbeats=None,user_heartbeats=None,wall_nanoseconds=None,command_returncode=None,accepted_measurement=False,disposition='stopped on guide command mismatch',async_option=None,maxHeartbeats_user=None))
(p/'parsed.json').write_text(json.dumps(rows,indent=2)+'\n')
with (p/'parsed.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
print(json.dumps(rows,indent=2))
