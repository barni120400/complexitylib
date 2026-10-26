#!/usr/bin/env python3
"""Cloud-only artifact validation; no Lean execution or edits to earlier raw data."""
import pathlib,json,hashlib,csv,sys
p=pathlib.Path(__file__).resolve().parent;prep=p.parent/'cloud-source-prep-3a6d'
sys.path.insert(0,str(prep))
from cloud_acceptance import require_complete_cloud
cfg=json.loads((prep/'acceptance-config.json').read_text());mapping=(prep/'mapping.json').read_bytes()
side_bytes=(p/'runtime-sidecar.json').read_bytes();side=json.loads(side_bytes)
commands=json.loads((p/'results.json').read_text());records=[]
for path in sorted(p.glob('*.events.jsonl')):
    records.extend(json.loads(line) for line in path.read_text().splitlines())
assert require_complete_cloud(cfg,mapping,side_bytes,commands,records)
assert all(row['actual_ilean_context_verified'] for row in commands)
assert not (p/'baseline.events.jsonl').exists() and not (p/'import-only.events.jsonl').exists()
rows=[]
for call in side['calls']:
    begin=next(x for x in records if x['call_token']==call['call_token'] and x['phase']=='begin')
    end=next(x for x in records if x['call_token']==call['call_token'] and x['phase']=='end')
    rows.append(dict(case=call['case'],full_call_id=call['call_id'],call_token=call['call_token'],original_line=call['original_line'],original_byte_start=call['original_byte_start'],original_byte_end=call['original_byte_end'],thread_id=begin['thread_id'],run_id=side['run_id'],sidecar_sha256=hashlib.sha256(side_bytes).hexdigest(),status=end['status'],goals_after=end['goals_after'],raw_current_thread_heartbeats=end['raw_thread_heartbeats'],user_heartbeats=end['raw_thread_heartbeats']/1000,forwarded_wall_nanoseconds=end['wall_nanoseconds'],async_option=begin['async_option'],user_limit=begin['maxHeartbeats_user'],whole_file_acceptance_agrees=True,actual_main_module=cfg['module_name'],final_proof_dependencies=None,methodology_approved=False))
(p/'parsed.json').write_text(json.dumps(rows,indent=2)+'\n')
with (p/'parsed.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
print(json.dumps(rows,indent=2))
