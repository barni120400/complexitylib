"""Fixed Cloud-only future acceptance contract; preparation, not an execution driver."""
import hashlib
import json


def require_complete_cloud(config, mapping_bytes, sidecar_bytes, commands, events):
    def need(ok, reason):
        if not ok:
            raise ValueError(reason)
    need(hashlib.sha256(mapping_bytes).hexdigest() == config['mapping_sha256'], 'mapping hash')
    side = json.loads(sidecar_bytes)
    need(side.get('state') == 'executed', 'no executed run')
    for key in ('source_pin', 'implementation_sha256', 'mapping_sha256'):
        need(side.get(key) == config[key], key)
    need(side.get('calls') == config['expected_calls'], 'different original calls')
    run = side.get('run_id')
    need(isinstance(run, str) and bool(run), 'run ID')
    digest = hashlib.sha256(sidecar_bytes).hexdigest()
    need(len(commands) == 3, 'partial/duplicate commands')
    modes = set()
    for command in commands:
        mode = command.get('mode')
        need(mode in config['required_modes'] and mode not in modes, 'command mode')
        modes.add(mode)
        need(command.get('returncode') == 0, 'whole-file command failed')
        need(command.get('run_id') == run and command.get('sidecar_sha256') == digest, 'command provenance')
        need(command.get('source_sha256') == config['variant_sha256'][mode], 'variant source')
        need(command.get('module_name') == config['module_name'], 'module/private-name context')
    need(modes == set(config['required_modes']), 'missing mode')
    tokens = {x['call_token'] for x in config['expected_calls']}
    need(len(tokens) == 3 and len(events) == 6, 'partial/censored/repeated events')
    grouped = {}
    for event in events:
        token, phase = event.get('call_token'), event.get('phase')
        need(token in tokens and phase in ('begin', 'end'), 'unknown event')
        need(event.get('run_id') == run and event.get('sidecar_sha256') == digest, 'event provenance')
        pair = grouped.setdefault(token, {})
        need(phase not in pair, 'duplicate/repeated attempt')
        pair[phase] = event
    need(set(grouped) == tokens, 'unobserved call')
    for pair in grouped.values():
        need(set(pair) == {'begin', 'end'}, 'unmatched/censored attempt')
        begin, end = pair['begin'], pair['end']
        need(isinstance(begin.get('event_id'), str) and bool(begin['event_id']), 'event ID')
        need(begin['event_id'] == end.get('event_id'), 'different attempts')
        need(begin.get('thread_id') == end.get('thread_id'), 'different threads')
        need(begin.get('maxHeartbeats_user') == config['user_maxHeartbeats'], 'budget')
        need(begin.get('child_kind') == 'Cslib.Tactic.PolyTime.tacticPolytime', 'child syntax')
        need(end.get('status') == 'returned' and end.get('goals_after') == 0, 'unexpected/partial result')
        for field in ('raw_thread_heartbeats', 'wall_nanoseconds'):
            need(type(end.get(field)) is int and end[field] >= 0, 'missing/invalid cost')
    return True
