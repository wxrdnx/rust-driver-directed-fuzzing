import argparse
import sys
import json
from collections import Counter, deque

from backward_slice import build_program_index, read_jsonl

def discover_entries(functions, registration_paths):

    # First index all analyzed Rust functions
    functions_by_name = {}
    for function in functions:
        metadata = function['function']
        for name in [metadata['name'], metadata['linkage_name']]:
            if name is None:
                continue
            if name not in functions_by_name:
                functions_by_name[name] = []
            functions_by_name[name].append(metadata['id'])

    # Read callback registrations produced by the LLVM analyzer
    entries = {}
    for path in registration_paths:
        with open(path) as file:
            analysis = json.load(file)
        for registration in analysis['callback_registrations']:
            for function_id in functions_by_name.get(registration['callback'], []):
                if function_id not in entries:
                    entries[function_id] = []
                entries[function_id].append(registration)

    return entries

def trace_target(target, callers, names, entries):

    # Start from one panic target and walk backward
    # Find whether the panic is triggerable from the userspace

    start = target['function_id']
    pending = deque([(start, (start,))])
    visited = {start}
    paths = []

    # Walk from panic to callers
    # Keep the shortest path to each functions
    while pending:
        function_id, path = pending.popleft()
        if function_id in entries:
            # Store the path in its normal direction (callback -> panic)
            entry_path = tuple(reversed(path))

            function_names = []
            for path_function in entry_path:
                function_names.append(names[path_function])

            for registration in entries[function_id]:
                paths.append({
                    'operation': registration['operation'],
                    'entry': names[function_id],
                    'registration': registration,
                    'functions': function_names,
                    'function_ids': list(entry_path),
                })

            continue

        for call in callers.get(function_id, []):
            caller = call['function']
            if caller not in visited:
                visited.add(caller)
                pending.append((caller, path + (caller,)))

    classification = 'unknown'

    if paths:
        classification = 'reachable'

    return {
        'target': target,
        'classification': classification,
        'paths': paths,
        'visited_function_count': len(visited),
    }

def analyze(cfg_path, dataflow_path, target_path, registration_paths, output_path):

    functions = read_jsonl(cfg_path)
    dataflows = read_jsonl(dataflow_path)
    with open(target_path) as file:
        target_data = json.load(file)

    _, callers = build_program_index(functions, dataflows)
    names = {}
    for function in functions:
        function_id = function['function']['id']
        name = function['function']['name']
        names[function_id] = name

    entries = discover_entries(functions, registration_paths)

    results = []
    counts = Counter()
    for target in target_data['panic_sites']:
        result = trace_target(target, callers, names, entries)
        results.append(result)
        counts[result['classification']] += 1

    report = {
        'target_count': len(results),
        'status_counts': dict(counts),
        'entries': entries,
        'targets': results,
    }

    with open(output_path, 'w') as file:
        json.dump(report, file, indent=2)
        file.write('\n')

    return True

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('dataflow')
    parser.add_argument('targets')
    parser.add_argument('output')
    parser.add_argument('--registrations', nargs='+', required=True)
    args = parser.parse_args()

    if not analyze(args.cfg, args.dataflow, args.targets, args.registrations, args.output):
        sys.exit(1)
