#!/usr/bin/env python3
"""Read git sources and prepare ONLY this manually inspected Cloud file; never invokes Lean."""
import pathlib,subprocess,hashlib,json,re
out=pathlib.Path(__file__).resolve().parent
pin='3a6d770645c1217689da774f519cd785c253d8a2'
path='Complexity/Computability/PCP/Encoded/Cloud.lean'
data=subprocess.check_output(['git','show',pin+':'+path]);text=data.decode()
sha=hashlib.sha256(data).hexdigest()
# Manually inspected grammar: three standalone authored polytime lines, no args/quotes.
occ=list(re.finditer(r'(?m)^  (polytime)$',text))
assert len(occ)==3 and len(re.findall(r'\bpolytime\b',text))==3
assert '`(' not in text and 'macro_rules' not in text and 'elab_rules' not in text
calls=[]
for match,name in zip(occ,['isPolyTime_halfEdges','isPolyTime_endpoint','isPolyTime_cloud']):
 start=len(text[:match.start(1)].encode());end=start+8
 assert data[start:end]==b'polytime'
 ident=f'{sha}:{path}:{start}-{end}:polytime'
 calls.append(dict(case=name,call_id=ident,call_token='c'+hashlib.sha256(ident.encode()).hexdigest()[:16],pin=pin,original_path=path,original_sha256=sha,original_byte_start=start,original_byte_end=end,original_line=text[:match.start(1)].count('\n')+1,original_text='polytime',expected='returned',selection='manual standalone authored tactic, no quote/generated selection'))
assert len({x['call_token'] for x in calls})==3
added='import Diag1155.Wrapper\n'
anchor='import Mathlib.Data.List.ProdSigma\n'
assert text.count(anchor)==1
imported=text.replace(anchor,anchor+added,1)
iterator=iter(calls)
wrapped=re.sub(r'(?m)^  polytime$',lambda _: '  diag1155_call '+json.dumps(next(iterator)['call_token'])+' => polytime',imported)
variants={'baseline':text,'import-only':imported,'wrapped':wrapped}
for mode,source in variants.items():
 target=out/mode/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(source)
# Exact reversibility, including all unrelated source/proof text and import ordering.
restored=re.sub(r'(?m)^  diag1155_call "c[0-9a-f]{16}" => (polytime)$',r'  \1',wrapped)
assert restored==imported and imported.replace(added,'',1)==text
assert (out/'baseline'/path).read_bytes()==data
impl=out.parent/'wrapper-compact-3a6d/Wrapper.lean'
mapping=dict(state='prepared_not_executed',source_pin=pin,source_path=path,source_sha256=sha,module_name='Complexity.Computability.PCP.Encoded.Cloud',implementation_sha256=hashlib.sha256(impl.read_bytes()).hexdigest(),calls=calls,counts=dict(authored_polytime=3,authored_fun_prop=0,authored_ppt=0,fun_prop_attributes_excluded=3),all_other_tactics='unchanged and unmeasured',explicit_private_declarations=0,expose_public_section=True,whole_source_lines=len(text.splitlines()))
(out/'mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
config=dict(state='prepared_not_executed',source_pin=pin,source_path=path,module_name=mapping['module_name'],mapping_sha256=hashlib.sha256((out/'mapping.json').read_bytes()).hexdigest(),implementation_sha256=mapping['implementation_sha256'],required_modes=['baseline','import-only','wrapped'],variant_sha256={m:hashlib.sha256(s.encode()).hexdigest() for m,s in variants.items()},user_maxHeartbeats=200000,expected_calls=calls,strict_requirements=['all three whole-source commands return0','exact source/module/variant/run/sidecar provenance','one begin and one end for each mapped original call','returned and zero goals with nonnegative measured costs','no partial/censored/unknown/duplicate/repeated/unmatched events'],options_from_original_lakefile={'autoImplicit':False,'weak.linter.mathlibStandardSet':True,'weak.linter.flexible':True,'weak.linter.pythonStyle':False,'weak.linter.checkInitImports':False,'weak.linter.allScriptsDocumented':False,'weak.linter.unicodeLinter':False},async_override=False)
(out/'acceptance-config.json').write_text(json.dumps(config,indent=2)+'\n')
print(json.dumps({'state':'prepared_not_executed','authored_target_calls':3,'baseline_byte_identical':True,'wrapped_exactly_reversible':True,'Lean_runs':0},indent=2))
