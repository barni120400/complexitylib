#!/usr/bin/env python3
"""Fixed three-file/five-call preparation only; not a census instrumenter."""
import pathlib,subprocess,json,hashlib,re
out=pathlib.Path(__file__).resolve().parent
pin='3a6d770645c1217689da774f519cd785c253d8a2'
selected=[('parameters','Complexity/Computability/Complexity/CookLevin/Parameters.lean',['computableInPolyTime_parameters']),('hardcore','Complexity/Crypto/Computational/GoldreichLevin/HardCore.lean',['polyTime_paddedFunction','polyTime_paddedPredicate','isPPT_paddedPredictor']),('matrix','Complexity/Crypto/Computational/Pseudoentropy/MatrixExtraction.lean',['isPPTOn_extractMatrixLabels'])]
kinds={'polytime':'Cslib.Tactic.PolyTime.tacticPolytime','fun_prop':'Mathlib.Meta.FunProp.funPropTacStx','ppt':'Cslib.Tactic.PPT.tacticPpt'}
files=[];tokens=set()
for case,path,declarations in selected:
 raw=subprocess.check_output(['git','show',pin+':'+path]);text=raw.decode();sha=hashlib.sha256(raw).hexdigest()
 matches=list(re.finditer(r'(?m)^  (polytime|fun_prop|ppt)$',text))
 assert len(matches)==len(declarations) and '`(' not in text
 assert not re.search(r'(?m)^(?:.*\s)?(?:macro_rules|elab_rules|syntax)\b',text)
 # Every literal target occurrence is one inspected standalone call or a fun_prop attribute.
 reduced=re.sub(r'@\[fun_prop\]','',text)
 assert len(re.findall(r'\b(?:polytime|fun_prop|ppt)\b',reduced))==len(matches)
 calls=[]
 for m,decl in zip(matches,declarations):
  tactic=m[1];start=len(text[:m.start(1)].encode());end=start+len(tactic)
  assert raw[start:end]==tactic.encode()
  ident=f'{sha}:{path}:{start}-{end}:{tactic}';token='c'+hashlib.sha256(ident.encode()).hexdigest()[:16]
  assert token not in tokens;tokens.add(token)
  calls.append(dict(case=decl,call_id=ident,call_token=token,tactic=tactic,expected_kind=kinds[tactic],pin=pin,original_path=path,original_sha256=sha,original_byte_start=start,original_byte_end=end,original_line=text[:m.start(1)].count('\n')+1,original_text=tactic,expected='returned'))
 imports=[l for l in text.splitlines() if l.startswith(('import ','public import '))]
 anchor=imports[-1]+'\n';assert text.count(anchor)==1
 added='import Diag1155.Wrapper\n';imported=text.replace(anchor,anchor+added,1)
 iterator=iter(calls)
 wrapped=re.sub(r'(?m)^  (polytime|fun_prop|ppt)$',lambda m:'  diag1155_call '+json.dumps(next(iterator)['call_token'])+' => '+m[1],imported)
 restored=re.sub(r'(?m)^  diag1155_call "c[0-9a-f]{16}" => (polytime|fun_prop|ppt)$',r'  \1',wrapped)
 assert restored==imported and imported.replace(added,'',1)==text
 variants={'baseline':text,'import-only':imported,'wrapped':wrapped}
 for mode,src in variants.items():
  f=out/case/mode/path;f.parent.mkdir(parents=True,exist_ok=True);f.write_text(src)
 files.append(dict(case=case,path=path,module_name=path[:-5].replace('/','.'),source_sha256=sha,calls=calls,original_imports=imports,variant_sha256={m:hashlib.sha256(s.encode()).hexdigest() for m,s in variants.items()},explicit_private_declarations=len(re.findall(r'(?m)^private\s',text)),original_option_directives=re.findall(r'(?m)^set_option.*$',text),source_lines=len(text.splitlines())))
assert len(files)<=3 and sum(len(f['calls']) for f in files)==5<=20
impl=out.parent/'wrapper-compact-3a6d/Wrapper.lean'
mapping=dict(state='prepared_not_executed',source_pin=pin,implementation_sha256=hashlib.sha256(impl.read_bytes()).hexdigest(),files=files,selected_calls=5,unsupported_candidates_excluded={'Encryption/PolyTime':'nested inline refine/by fun_prop','OneWay/Collision':'nested parenthesized by ppt'},remainder='unmeasured; no full census expansion')
(out/'mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(json.dumps({'files':len(files),'selected_calls':5,'tactics':[c['tactic'] for f in files for c in f['calls']],'exact_reversibility':True},indent=2))
