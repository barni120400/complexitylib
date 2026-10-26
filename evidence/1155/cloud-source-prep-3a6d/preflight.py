#!/usr/bin/env python3
"""Source mapping + SYNTHETIC acceptance-contract checks; zero Lean executions."""
import pathlib,json,hashlib,copy
from cloud_acceptance import require_complete_cloud
p=pathlib.Path(__file__).resolve().parent
cfg=json.loads((p/'acceptance-config.json').read_text());mb=(p/'mapping.json').read_bytes();mapping=json.loads(mb)
path=cfg['source_path'];baseline=(p/'baseline'/path).read_bytes()
assert hashlib.sha256(baseline).hexdigest()==mapping['source_sha256']
for call in mapping['calls']:
    assert baseline[call['original_byte_start']:call['original_byte_end']]==b'polytime'
for mode,sha in cfg['variant_sha256'].items():
    assert hashlib.sha256((p/mode/path).read_bytes()).hexdigest()==sha
# These are in-memory mock data only, never measurements or runtime acceptance claims.
side=dict(state='executed',run_id='SYNTHETIC-contract-check',calls=cfg['expected_calls'],
          **{k:cfg[k] for k in ('source_pin','implementation_sha256','mapping_sha256')})
sb=json.dumps(side).encode();digest=hashlib.sha256(sb).hexdigest()
cmd=[dict(mode=m,returncode=0,run_id=side['run_id'],sidecar_sha256=digest,
          source_sha256=cfg['variant_sha256'][m],module_name=cfg['module_name']) for m in cfg['required_modes']]
ev=[]
for i,call in enumerate(mapping['calls']):
    base=dict(event_id='SYNTHETIC-'+str(i),call_token=call['call_token'],run_id=side['run_id'],
              sidecar_sha256=digest,thread_id=1)
    ev += [dict(base,phase='begin',maxHeartbeats_user=200000,
                child_kind='Cslib.Tactic.PolyTime.tacticPolytime'),
           dict(base,phase='end',status='returned',goals_after=0,
                raw_thread_heartbeats=0,wall_nanoseconds=0)]
assert require_complete_cloud(cfg,mb,sb,cmd,ev)
checks=[]
def rejects(name,commands=cmd,events=ev,sidecar=sb):
    try:require_complete_cloud(cfg,mb,sidecar,commands,events)
    except ValueError as ex:checks.append(dict(name=name,synthetic=True,rejected=True,reason=str(ex)));return
    raise AssertionError('invalid synthetic dataset accepted: '+name)
rejects('partial_events',events=ev[:-1]);rejects('unobserved_calls',events=[])
rejects('duplicate_end',events=ev[:-1]+[ev[1]])
bad=copy.deepcopy(ev);bad[-1]['status']='censored_unknown';bad[-1]['raw_thread_heartbeats']=None
rejects('censored_status',events=bad)
bad=copy.deepcopy(ev);bad[1]['event_id']='SYNTHETIC-other';rejects('unmatched_attempt',events=bad)
bad=copy.deepcopy(cmd);bad[-1]['returncode']=1;rejects('failed_whole_file',commands=bad)
rejects('missing_baseline_command',commands=cmd[1:])
bad=copy.deepcopy(cmd);bad[-1]=copy.deepcopy(cmd[0]);rejects('duplicate_mode',commands=bad)
bad=copy.deepcopy(ev);bad[0]['sidecar_sha256']='0'*64;rejects('sidecar_mismatch',events=bad)
rejects('prep_is_not_execution',sidecar=mb)
report=dict(state='SOURCE_PREPARATION_ONLY',actual_Cloud_elaborations=0,bootstrap_or_cache_operations=0,
            source_mapping_verified=True,synthetic_complete_contract_smoke_passed=True,
            synthetic_rejections=checks,actual_Cloud_result='NOT_RUN; explicit builder handoff required')
(p/'preflight-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'mapping':'verified','synthetic_rejections':len(checks),'actual_Cloud_runs':0},indent=2))
