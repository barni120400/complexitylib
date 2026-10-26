#!/usr/bin/env python3
"""ONE fixed Cloud file: baseline/import-only/wrapped, no other source collection."""
import argparse,hashlib,json,os,pathlib,subprocess,time,uuid
p=argparse.ArgumentParser();p.add_argument('checkout');a=p.parse_args()
out=pathlib.Path(__file__).resolve().parent;prep=out.parent/'cloud-source-prep-3a6d';root=pathlib.Path(a.checkout).resolve()
if (out/'results.json').exists() or (out/'runtime-sidecar.json').exists():raise SystemExit('Refusing archived output overwrite')
config=json.loads((prep/'acceptance-config.json').read_text());mapping_bytes=(prep/'mapping.json').read_bytes()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==config['source_pin']
assert subprocess.run(['git','diff','--quiet'],cwd=root).returncode==0
assert hashlib.sha256((root/'Diag1155/Wrapper.lean').read_bytes()).hexdigest()==config['implementation_sha256']
# Read options only. NEVER use copied setup importArts, which can retain foreign absolute paths.
setup=root/'.lake/build/ir/Complexity/Computability/PCP/Encoded/Cloud.setup.json'
assert json.loads(setup.read_text())['options']==config['options_from_original_lakefile']
run_id='cloud-3a6d-'+str(uuid.uuid4())
side=dict(state='executed',run_id=run_id,source_pin=config['source_pin'],implementation_sha256=config['implementation_sha256'],mapping_sha256=hashlib.sha256(mapping_bytes).hexdigest(),calls=config['expected_calls'])
(out/'runtime-sidecar.json').write_text(json.dumps(side,indent=2)+'\n');digest=hashlib.sha256((out/'runtime-sidecar.json').read_bytes()).hexdigest()
options=['-DwarningAsError=true']+[f'-D{k}={str(v).lower()}' for k,v in config['options_from_original_lakefile'].items()]
private=root/'.lake/diag1155/cloud';private.mkdir(parents=True,exist_ok=True)
results=[];contexts={}
for mode in config['required_modes']:
 variant_root=prep/mode;source=variant_root/config['source_path'];expected=config['variant_sha256'][mode]
 assert hashlib.sha256(source.read_bytes()).hexdigest()==expected
 telemetry=out/f'{mode}.events.jsonl'
 if telemetry.exists():raise SystemExit('Refusing telemetry overwrite')
 ilean=private/f'{mode}.ilean'
 cmd=['lake','env','lean',*options,'--root='+str(variant_root),'-i',str(ilean),str(source)]
 env=os.environ.copy();env.update(DIAG1155_OUTPUT=str(telemetry),DIAG1155_RUN_ID=run_id,DIAG1155_SIDECAR_SHA256=digest)
 start=time.monotonic()
 with (out/f'{mode}.log').open('w') as f:result=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 row=dict(mode=mode,returncode=result.returncode,process_wall_seconds=time.monotonic()-start,command=cmd,run_id=run_id,sidecar_sha256=digest,source_sha256=expected,module_name=None,actual_ilean_context_verified=False)
 if result.returncode==0:
  data=json.loads(ilean.read_text());row['module_name']=data['module']
  context=dict(module=data['module'],directImports=data['directImports'],source_declaration_names=sorted(data['decls']),private_ilean_sha256=hashlib.sha256(ilean.read_bytes()).hexdigest(),compiled_output_published=False)
  contexts[mode]=context
  assert data['module']==config['module_name'],'main-module mismatch'
  if mode=='baseline':
   assert [x[0] for x in data['directImports']]==[line.split('import ',1)[1] for line in source.read_text().splitlines() if line.startswith(('import ','public import '))]
  else:
   assert data['directImports'][:-1]==contexts['baseline']['directImports'],'original import context mismatch'
   assert data['directImports'][-1][0]=='Diag1155.Wrapper'
   assert context['source_declaration_names']==contexts['baseline']['source_declaration_names'],'source declaration context mismatch'
  row['actual_ilean_context_verified']=True
 results.append(row)
 (out/'results.json').write_text(json.dumps(results,indent=2)+'\n');(out/'actual-contexts.json').write_text(json.dumps(contexts,indent=2)+'\n')
 if result.returncode:print(json.dumps(results,indent=2));raise SystemExit(result.returncode)
print(json.dumps([{'mode':x['mode'],'returncode':x['returncode'],'context_verified':x['actual_ilean_context_verified']} for x in results],indent=2))
