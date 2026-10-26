#!/usr/bin/env python3
"""One existing tactic-form counter and separate attempted-rule trace per positive."""
import argparse,json,pathlib,subprocess,time
p=argparse.ArgumentParser();p.add_argument('checkout');a=p.parse_args()

expected_head='3a6d770645c1217689da774f519cd785c253d8a2'
actual_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=pathlib.Path(a.checkout).resolve(),text=True).strip()
if actual_head!=expected_head:raise SystemExit(f'Refusing measurement: expected source {expected_head}, got {actual_head}')
out=pathlib.Path(__file__).resolve().parent;old=out.parent;root=pathlib.Path(a.checkout).resolve();dest=root/'pilot1155';results=[]
g=(old/'guide-baseline.lean').read_text();header=g.split('#doc (Manual)',1)[0]
goal=g.split('```lean\n',1)[1].split('\n```',1)[0]
# Same goal/full chapter imports/options, ordinary top-level diagnostic rather than Verso doc.
guide=header.replace('import VersoManual','import VersoManual\nimport Mathlib.Util.CountHeartbeats')+'open Cslib.Complexity Turing.MultiTapeTM\n\n'+goal+'\n'
s=(old/'operands-baseline.lean').read_text().split('-- Neither callback premise',1)[0].rstrip()+'\n'
s=s.replace('import Complexity.Tactic.PolyTime','import Complexity.Tactic.PolyTime\nimport Mathlib.Util.CountHeartbeats')
for case,source in [('guide',guide),('supplied',s)]:
 for mode in ['import-baseline','heartbeats','rules']:
  text=source.replace('  polytime','  #count_heartbeats polytime') if mode=='heartbeats' else source
  name=f'{case}-{mode}.lean';(out/name).write_text(text);target=dest/name;target.write_text(text)
  opts=['-DwarningAsError=true']
  if mode=='rules':opts+=['-Dtrace.Meta.Tactic.fun_prop=true','-Dtrace.aesop=true']
  cmd=['lake']+(['-d','guide'] if case=='guide' else [])+['env','lean']+opts+[str(target)]
  start=time.monotonic()
  with (out/f'{case}-{mode}.log').open('w') as f:proc=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
  results.append(dict(case=case,mode=mode,command=cmd,returncode=proc.returncode,process_wall_seconds=time.monotonic()-start,maxHeartbeats=200000,source=name,async_false_inside_counter=(mode=='heartbeats'),added_import='Mathlib.Util.CountHeartbeats'))
  (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
  if proc.returncode:print(json.dumps(results,indent=2));raise SystemExit(proc.returncode)
print(json.dumps(results,indent=2))
