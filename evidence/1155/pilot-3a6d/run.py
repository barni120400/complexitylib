#!/usr/bin/env python3
"""Small sequential Lean CLI pilot; no package/source mutation or budget overrides."""
import argparse, json, pathlib, subprocess, time
p=argparse.ArgumentParser();p.add_argument('checkout');p.add_argument('mode',choices=['baseline','wall']);a=p.parse_args()

expected_head='3a6d770645c1217689da774f519cd785c253d8a2'
actual_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=pathlib.Path(a.checkout).resolve(),text=True).strip()
if actual_head!=expected_head:raise SystemExit(f'Refusing measurement: expected source {expected_head}, got {actual_head}')
evidence=pathlib.Path(__file__).resolve().parent
root=pathlib.Path(a.checkout).resolve(); dest=root/'pilot1155';dest.mkdir(exist_ok=True)
results=[]
for case in ['guide','operands']:
    source=(evidence/f'{case}-baseline.lean').read_text()
    target=dest/f'{case}-{a.mode}.lean';target.write_text(source)
    output=evidence/f'{case}-{a.mode}.profile.json'
    opts=['-DwarningAsError=true']
    if a.mode=='wall':
        opts += ['-Dtrace.profiler=true','-Dtrace.profiler.threshold=0','-Dtrace.profiler.useHeartbeats=false',f'-Dtrace.profiler.output={output}']
    cmd=['lake']+(['-d','guide'] if case=='guide' else [])+['env','lean']+opts+[str(target)]
    start=time.monotonic()
    with (evidence/f'{case}-{a.mode}.log').open('w') as log:
        proc=subprocess.run(cmd,cwd=root,stdout=log,stderr=subprocess.STDOUT)
    results.append(dict(case=case,mode=a.mode,command=cmd,returncode=proc.returncode,process_wall_seconds=time.monotonic()-start,source=str(target),profile_exists=output.exists(),maxHeartbeats=200000,async_override=False))
    (evidence/f'{a.mode}-results.json').write_text(json.dumps(results,indent=2)+'\n')
    if proc.returncode: break
print(json.dumps(results,indent=2))
