#!/usr/bin/env python3
"""Execute exact restored automatic source blocks, no library/tactic edits or budget overrides."""
import argparse,pathlib,subprocess,time,json
p=argparse.ArgumentParser();p.add_argument('checkout');p.add_argument('--trace-failures',action='store_true');a=p.parse_args()

expected_head='3a6d770645c1217689da774f519cd785c253d8a2'
actual_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=pathlib.Path(a.checkout).resolve(),text=True).strip()
if actual_head!=expected_head:raise SystemExit(f'Refusing measurement: expected source {expected_head}, got {actual_head}')
out=pathlib.Path(__file__).resolve().parent;root=pathlib.Path(a.checkout).resolve();dest=root/'pilot1155/step2';dest.mkdir(parents=True,exist_ok=True)
rows=[]
if a.trace_failures:
 cases=[x['case'] for x in json.loads((out/'results.json').read_text()) if x['returncode']!=0]
else:cases=['AddTrivial','LiuPass','Hardness1063']
for case in cases:
 source=(out/f'{case}-original.lean').read_text()
 if a.trace_failures:
  if case!='LiuPass':raise SystemExit('Unmapped failed theorem; no broad trace fallback')
  source=source.replace('private theorem computableInPolyTime_thresholdValue', 'set_option trace.Meta.Tactic.fun_prop true in\nprivate theorem computableInPolyTime_thresholdValue',1)
 target=dest/f"{case}-{'trace' if a.trace_failures else 'original'}.lean"
 target=pathlib.Path(str(target));target.write_text(source)
 if a.trace_failures:(out/f'{case}-trace.lean').write_text(source)
 mode='trace' if a.trace_failures else 'baseline'
 cmd=['lake','env','lean','-DwarningAsError=true']+[str(target)]
 start=time.monotonic()
 with (out/f'{case}-{mode}.log').open('w') as f:res=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
 rows.append(dict(case=case,mode=mode,command=cmd,returncode=res.returncode,process_wall_seconds=time.monotonic()-start,maxHeartbeats='unchanged default200000 per original command',scope='whole current module with only historical automatic proof restored',per_call_heartbeats=None))
 (out/('trace-results.json' if a.trace_failures else 'results.json')).write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
