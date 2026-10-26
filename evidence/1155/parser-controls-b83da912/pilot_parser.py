"""Data-only parser for the fixed three-call pilot; not a collector or survey framework."""
import hashlib
import json


class PilotParseError(ValueError):
    pass


def need(condition, message):
    if not condition:
        raise PilotParseError(message)


def parse_partial(sidecar_bytes, implementation_bytes, records):
    """Retain partial attempts without asserting whole-command/pilot acceptance."""
    side = json.loads(sidecar_bytes)
    digest = hashlib.sha256(sidecar_bytes).hexdigest()
    need(hashlib.sha256(implementation_bytes).hexdigest() == side['implementation_sha256'],
         'implementation digest mismatch')
    calls = side['calls']
    need(len(calls) == 3 and {x['case'] for x in calls} == {'guide', 'supplied', 'missing'},
         'not the fixed three-call pilot')
    mapping = {x['call_token']: x for x in calls}
    need(len(mapping) == 3 and len({x['call_id'] for x in calls}) == 3, 'duplicate mapping')
    for call in calls:
        full = (f"{call['original_sha256']}:{call['original_path']}:"
                f"{call['original_byte_start']}-{call['original_byte_end']}:polytime")
        need(call['call_id'] == full, 'inconsistent original ID')
        need(call['call_token'] == 'c' + hashlib.sha256(full.encode()).hexdigest()[:16],
             'inconsistent compact token')
        need(call['pin'] == side['source_pin'], 'source pin mismatch')
    attempts = {}
    for record in records:
        token = record.get('call_token')
        need(token in mapping, 'unknown call token')
        need(record.get('run_id') == side['run_id'], 'run mismatch')
        need(record.get('sidecar_sha256') == digest, 'sidecar digest mismatch')
        event = record.get('event_id')
        need(isinstance(event, str) and bool(event), 'missing event ID')
        phase = record.get('phase')
        need(phase in ('begin', 'end'), 'unknown phase')
        group = attempts.setdefault(event, {'call_token': token})
        need(group['call_token'] == token, 'event reused across calls')
        need(phase not in group, f'duplicate {phase}')
        group[phase] = record
    output = []
    for call in calls:
        observed = []
        for event, group in attempts.items():
            if group['call_token'] != call['call_token']:
                continue
            need('begin' in group, 'unmatched end')
            begin, end = group['begin'], group.get('end')
            need(begin.get('maxHeartbeats_user') == 200000, 'changed budget')
            need(begin.get('child_kind') == 'Cslib.Tactic.PolyTime.tacticPolytime',
                 'changed child kind')
            need(type(begin.get('thread_id')) is int and begin['thread_id'] >= 0,
                 'invalid begin thread')
            need(type(begin.get('async_option')) is bool, 'missing async option')
            if end is None:
                observed.append(dict(event_id=event, status='censored_unknown',
                                     raw_thread_heartbeats=None, user_heartbeats=None,
                                     wall_nanoseconds=None, goals_after=None))
                continue
            need(end.get('thread_id') == begin['thread_id'], 'thread mismatch')
            status = end.get('status')
            need(status in {'returned', 'exception', 'heartbeat_exception',
                            'recursion_exception', 'interrupt_exception'}, 'unknown outcome')
            for key in ('raw_thread_heartbeats', 'wall_nanoseconds'):
                need(type(end.get(key)) is int and end[key] >= 0, f'invalid {key}')
            goals = end.get('goals_after')
            if status == 'returned':
                need(type(goals) is int and goals >= 0, 'missing returned goals')
            else:
                need(goals is None, 'exception has fabricated returned goals')
            observed.append(dict(event_id=event, status=status,
                                 raw_thread_heartbeats=end['raw_thread_heartbeats'],
                                 user_heartbeats=end['raw_thread_heartbeats'] / 1000,
                                 wall_nanoseconds=end['wall_nanoseconds'], goals_after=goals))
        output.append(dict(case=call['case'], call_id=call['call_id'],
                           observation='observed' if observed else 'not_observed',
                           attempts=observed))
    return output


def require_complete_pilot(sidecar_bytes, command_results, parsed):
    """Strict acceptance is separate: partial/repeated data never passes the original pilot."""
    side = json.loads(sidecar_bytes)
    digest = hashlib.sha256(sidecar_bytes).hexdigest()
    expected_commands = {(file, mode) for file in ('guide', 'operands')
                         for mode in ('baseline', 'import-only', 'wrapped')}
    need(len(command_results) == 6, 'incomplete command results')
    seen = set()
    for command in command_results:
        key = (command.get('file'), command.get('mode'))
        need(key in expected_commands and key not in seen, 'duplicate/unknown command')
        seen.add(key)
        need(command.get('returncode') == 0, 'command failed')
        need(command.get('run_id') == side['run_id'], 'command run mismatch')
        need(command.get('sidecar_sha256') == digest, 'command sidecar mismatch')
    need(seen == expected_commands, 'missing command')
    expected = {x['case']: x for x in side['calls']}
    need(len(parsed) == 3 and {x['case'] for x in parsed} == set(expected), 'missing call')
    for call in parsed:
        spec = expected[call['case']]
        need(call['call_id'] == spec['call_id'], 'call ID mismatch')
        need(call['observation'] == 'observed' and len(call['attempts']) == 1,
             'unobserved/partial/repeated pilot call')
        attempt = call['attempts'][0]
        need(attempt['status'] == spec['expected'], 'unexpected invocation outcome')
        if attempt['status'] == 'returned':
            need(attempt['goals_after'] == 0, 'remaining goals')
    return True
