#!/usr/bin/env python3
"""Synthetic parser controls only; never runs Lean or rewrites real measurements."""
import copy
import hashlib
import json
import pathlib
from pilot_parser import PilotParseError, parse_partial, require_complete_pilot

here = pathlib.Path(__file__).resolve().parent
raw = here.parent / 'wrapper-compact-3a6d'
side_bytes = (raw / 'sidecar.json').read_bytes()
implementation = (raw / 'Wrapper.lean').read_bytes()
side = json.loads(side_bytes)
commands = json.loads((raw / 'results.json').read_text())
records = []
inputs = []
for path in sorted(raw.glob('*.events.jsonl')):
    inputs.append({'path': str(path.relative_to(here.parent)),
                   'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    records.extend(json.loads(line) for line in path.read_text().splitlines())
by_case = {item['case']: item['call_token'] for item in side['calls']}
gb = next(x for x in records if x['call_token'] == by_case['guide'] and x['phase'] == 'begin')
ge = next(x for x in records if x['call_token'] == by_case['guide'] and x['phase'] == 'end')
me = next(x for x in records if x['call_token'] == by_case['missing'] and x['phase'] == 'end')
results = []


def rejected_acceptance(parsed, command_rows=commands):
    try:
        require_complete_pilot(side_bytes, command_rows, parsed)
    except PilotParseError:
        return True
    raise AssertionError('partial/invalid control passed strict pilot acceptance')


def record(name, transformation, detail, synthetic=True):
    results.append(dict(name=name, synthetic=synthetic, transformation=transformation,
                        passed=True, detail=detail))


# Reconciliation reads but NEVER rewrites approved real parsed outputs.
real = parse_partial(side_bytes, implementation, records)
assert require_complete_pilot(side_bytes, commands, real)
old = json.loads((raw / 'parsed.json').read_text())
for call in real:
    before = next(x for x in old if x['case'] == call['case'])
    attempt = call['attempts'][0]
    for key, previous in [('status', 'runtime_status'), ('goals_after', 'goals_after'),
                          ('raw_thread_heartbeats', 'raw_current_thread_heartbeats'),
                          ('user_heartbeats', 'user_heartbeats'),
                          ('wall_nanoseconds', 'forwarded_interval_wall_ns')]:
        assert attempt[key] == before[previous]
    assert call['call_id'] == before['full_call_id']
record('complete_real_pilot_unchanged', 'none; read-only reconciliation',
       'same three invocation outcomes/costs/IDs; strict six-command acceptance passes', False)

partial = parse_partial(side_bytes, implementation, [copy.deepcopy(gb)])
attempt = next(x for x in partial if x['case'] == 'guide')['attempts'][0]
assert attempt['status'] == 'censored_unknown'
assert all(attempt[k] is None for k in ('raw_thread_heartbeats', 'user_heartbeats',
                                      'wall_nanoseconds', 'goals_after'))
assert rejected_acceptance(partial)
record('begin_without_end', 'retain guide begin only',
       'censored_unknown; all costs/goals null; strict pilot acceptance rejects')

absent = parse_partial(side_bytes, implementation, [])
assert all(x['observation'] == 'not_observed' and x['attempts'] == [] for x in absent)
assert rejected_acceptance(absent)
record('no_observed_begin', 'remove all events',
       'not_observed with no invented attempts/costs; strict acceptance rejects')

failure = parse_partial(side_bytes, implementation,
                        [copy.deepcopy(x) for x in records if x['call_token'] == by_case['missing']])
assert next(x for x in failure if x['case'] == 'missing')['attempts'][0]['status'] == 'exception'
assert rejected_acceptance(failure)
record('caught_ordinary_failure', 'retain missing-operand pair only',
       'invocation remains exception; cannot confer complete pilot acceptance')

retry = copy.deepcopy([gb, ge])
for x in retry:
    x['event_id'] += ':SYNTHETIC-retry'
retry[1]['status'] = 'exception'
retry[1]['goals_after'] = None
repeated = parse_partial(side_bytes, implementation, records + retry)
guide_attempts = next(x for x in repeated if x['case'] == 'guide')['attempts']
assert len(guide_attempts) == 2 and len({x['event_id'] for x in guide_attempts}) == 2
assert [x['status'] for x in guide_attempts] == ['returned', 'exception']
assert len(repeated) == 3 and rejected_acceptance(repeated)
record('repeated_backtracked_call_attempts', 'clone guide pair with distinct synthetic event ID; second exception',
       'two runtime attempts under ONE authored call; final retention unknown; strict fixed pilot rejects')


def expect_parse_error(name, data, transformation, side=side_bytes, impl=implementation):
    try:
        parse_partial(side, impl, data)
    except PilotParseError as ex:
        record(name, transformation, 'fail closed: ' + str(ex))
        return
    raise AssertionError(name + ' did not fail closed')


expect_parse_error('duplicate_begin', records + [copy.deepcopy(gb)], 'duplicate guide begin')
expect_parse_error('duplicate_end', records + [copy.deepcopy(ge)], 'duplicate guide end')
expect_parse_error('unmatched_end', [copy.deepcopy(ge)], 'guide end without begin')


def changed_end(key, value):
    result = copy.deepcopy(records)
    next(x for x in result if x['event_id'] == ge['event_id'] and x['phase'] == 'end')[key] = value
    return result


expect_parse_error('cross_call_event_reuse', changed_end('call_token', by_case['supplied']),
                   'end uses existing different call token')
expect_parse_error('event_sidecar_hash_mismatch', changed_end('sidecar_sha256', '0' * 64),
                   'forge one event digest')
expect_parse_error('run_mismatch', changed_end('run_id', 'SYNTHETIC-other-run'), 'forge event run')
expect_parse_error('unknown_token', changed_end('call_token', 'SYNTHETIC-unknown'), 'forge call token')
expect_parse_error('thread_mismatch', changed_end('thread_id', ge['thread_id'] + 1), 'forge end thread')
expect_parse_error('unknown_phase', changed_end('phase', 'SYNTHETIC-other'), 'forge event phase')
expect_parse_error('invalid_cost', changed_end('raw_thread_heartbeats', -1), 'negative synthetic cost')
expect_parse_error('implementation_hash_mismatch', records, 'alter implementation bytes',
                   impl=implementation + b'\n-- SYNTHETIC\n')
changed_side = copy.deepcopy(side)
changed_side['run_id'] = 'SYNTHETIC-other-sidecar'
expect_parse_error('changed_sidecar', records, 'alter sidecar bytes without matching provenance',
                   side=json.dumps(changed_side).encode())

incomplete = parse_partial(side_bytes, implementation,
                           [copy.deepcopy(x) for x in records if x != ge])
assert rejected_acceptance(incomplete)
record('partial_cannot_use_real_command_success', 'remove guide end but retain all actual successful commands',
       'real command return codes cannot bless censored attempt')

wrong_negative = copy.deepcopy(records)
bad = next(x for x in wrong_negative if x['event_id'] == me['event_id'] and x['phase'] == 'end')
bad['status'], bad['goals_after'] = 'returned', 0
assert rejected_acceptance(parse_partial(side_bytes, implementation, wrong_negative))
record('negative_as_success_rejected', 'synthetically change missing invocation to returned',
       'parse retains observed status; strict expected-outcome acceptance rejects')

for name, rows in [('missing_command', commands[:-1]),
                   ('duplicate_command', commands[:-1] + [commands[0]])]:
    assert rejected_acceptance(real, rows)
    record(name, 'remove/duplicate one command row', 'strict command acceptance rejects')
failed = copy.deepcopy(commands)
failed[-1]['returncode'] = 1
assert rejected_acceptance(real, failed)
record('failed_command', 'set one command returncode to 1', 'strict acceptance rejects')

report = dict(scope='parser-level SYNTHETIC controls; no new Lean/runtime measurements',
              original_evidence_head='b83da912f9c0230bd9047e5f473ad9a27cff28b3',
              original_event_sources=inputs,
              original_sidecar_sha256=hashlib.sha256(side_bytes).hexdigest(),
              original_parsed_sha256=hashlib.sha256((raw / 'parsed.json').read_bytes()).hexdigest(),
              real_measurement_rows_written=False, controls=results,
              all_passed=all(x['passed'] for x in results))
(here / 'control-results.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'checks': len(results), 'all_passed': report['all_passed'],
                  'real_artifacts_reconciled_unchanged': True, 'Lean_runs': 0}, indent=2))
