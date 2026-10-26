#!/usr/bin/env python3
"""Exactly three manually selected original calls, not automatic census instrumentation."""
import argparse,hashlib,json,os,pathlib,re,subprocess,time
p=argparse.ArgumentParser();p.add_argument('checkout');a=p.parse_args()
root=pathlib.Path(a.checkout).resolve();out=pathlib.Path(__file__).resolve().parent
pin='3a6d770645c1217689da774f519cd785c253d8a2'
if subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()!=pin:raise SystemExit('Refusing non-pinned source')
# Diagnostic-only files; never edits a tracked production/package file.
dest=root/'pilot1155';dest.mkdir(exist_ok=True)
old=out.parent/'pilot-3a6d'
guide_path='guide/ComplexityGuide/NPCompleteness.lean'
operand_path='ComplexityTests/GuideFilterPolyTime.lean'
g=(root/guide_path).read_text();f=(root/operand_path).read_text()
starts=[(guide_path,g.index('example : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.filter')),
 (operand_path,f.index('example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}')),
 (operand_path,f.index('example {α : Type} {input : α ↪ List Bool} {left _right : α → ℕ}'))]
sidecar=[]
for (path,start),case in zip(starts,['guide','supplied','missing']):
 data=(root/path).read_text();pos=data.index('polytime',start);b=len(data[:pos].encode());e=b+len(b'polytime');sha=hashlib.sha256(data.encode()).hexdigest()
 label=f'{sha}:{path}:{b}-{e}:polytime'
 assert data.encode()[b:e]==b'polytime'
 sidecar.append(dict(case=case,call_id=label,pin=pin,original_path=path,original_sha256=sha,original_byte_start=b,original_byte_end=e,original_line=data[:pos].count('\n')+1,original_text='polytime',selection='manual authored occurrence; not quoted/generated',expected='exception' if case=='missing' else 'returned'))
(out/'sidecar.json').write_text(json.dumps(sidecar,indent=2)+'\n')
results=[]
for file,calls in [('guide',sidecar[:1]),('operands',sidecar[1:])]:
 baseline=(old/f'{file}-baseline.lean').read_text()
 assert len(list(re.finditer(r'\bpolytime\b',baseline)))==len(calls)
 for mode in ['baseline','import-only','wrapped']:
  source=baseline
  if mode!='baseline':source=source.replace('import Complexity.Tactic.PolyTime','import Complexity.Tactic.PolyTime\nimport Diag1155.Wrapper',1)
  if mode=='wrapped':
   it=iter(calls);source=re.sub(r'\bpolytime\b',lambda m:'diag1155_call '+json.dumps(next(it)['call_id'])+' => '+m[0],source)
  name=f'{file}-{mode}.lean';target=dest/name;target.write_text(source);(out/name).write_text(source)
  telemetry=out/f'{file}-{mode}.events.jsonl'
  if telemetry.exists():raise SystemExit('Refusing to overwrite event evidence')
  cmd=['lake']+(['-d','guide'] if file=='guide' else [])+['env','lean','-DwarningAsError=true',str(target)]
  env=os.environ.copy();env['DIAG1155_OUTPUT']=str(telemetry)
  start=time.monotonic()
  with (out/f'{file}-{mode}.log').open('w') as log:r=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
  results.append(dict(file=file,mode=mode,returncode=r.returncode,process_wall_seconds=time.monotonic()-start,command=cmd,source_sha256=hashlib.sha256(source.encode()).hexdigest(),telemetry_exists=telemetry.exists(),maxHeartbeats='unchanged original default/explicit200000',async_override=False))
  (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
  if r.returncode:print(json.dumps(results,indent=2));raise SystemExit(r.returncode)
print(json.dumps(results,indent=2))
