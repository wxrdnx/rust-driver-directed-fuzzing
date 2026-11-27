import argparse
import sys
import json
from collections import Counter, deque

from backward_slice import build_program_index, read_jsonl

def add_c_callers(functions, callers, analysis_paths):
    # Connects C call graph to Rust call graph
    # Assume LLVM reports the direct call:
    #     __do_sys_ioctl -> vfs_ioctl
    # And assume callback analysis (syscall_discovery.py) resolves:
    #     vfs_ioctl -> rust_binder_ioctl
    # Backward slicing can then continue across the Rust-C border:
    #     panic -> Rust helper -> rust_binder_ioctl -> vfs_ioctl -> __do_sys_ioctl -> ioctl

    # Load the C analysis file
    records = []
    calls = []
    for path in analysis_paths:
        with open(path) as file:
            analysis = json.load(file)
        records.extend(analysis['function_records'])
        calls.extend(analysis['calls'])

    # Index Rust functions
    functions_by_symbol = {}
    for function in functions:
        metadata = function['function']
        for symbol in [metadata['name'], metadata['linkage_name']]:
            if symbol is None:
                continue
            if symbol not in functions_by_symbol:
                functions_by_symbol[symbol] = []
            functions_by_symbol[symbol].append(metadata['id'])

    # Add the C functions to the same index
    for record in records:
        functions.append({'function': record})
        symbol = record['linkage_name']
        if symbol not in functions_by_symbol:
            functions_by_symbol[symbol] = []
        functions_by_symbol[symbol].append(record['id'])

    # Collect all function IDs and examine record emitted by the C LLVM analyzer
    function_ids = set()
    for function in functions:
        function_ids.add(function['function']['id'])
    for call in calls:
        # We only care about direct calls currently
        # TODO: indirect calls
        if call['call_kind'] != 'direct':
            continue

        targets = []
        if call['callee_id'] in function_ids:
            targets.append(call['callee_id'])
        else:
            targets.extend(functions_by_symbol.get(call['callee_symbol'], []))
        for target in targets:
            if target not in callers:
                callers[target] = []
            callers[target].append({ 'function': call['caller_id'], 'operation': None, 'arguments': {}})

def discover_entries(functions, registration_paths):

    # First index all analyzed Rust functions
    functions_by_name = {}
    for function in functions:
        metadata = function['function']
        for name in [metadata['id'], metadata['name'], metadata['linkage_name']]:
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
            function_ids = []
            if registration['callback_id'] in functions_by_name:
                function_ids.extend(functions_by_name[registration['callback_id']])
            function_ids.extend(functions_by_name.get(registration['callback'], []))
            for function_id in function_ids:
                if function_id not in entries:
                    entries[function_id] = []
                if registration not in entries[function_id]:
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

def analyze(cfg_path, dataflow_path, target_path, registration_paths, c_analysis_paths, output_path):

    functions = read_jsonl(cfg_path)
    dataflows = read_jsonl(dataflow_path)
    with open(target_path) as file:
        target_data = json.load(file)

    _, callers = build_program_index(functions, dataflows)
    add_c_callers(functions, callers, c_analysis_paths)
    names = {}
    for function in functions:
        function_id = function['function']['id']
        name = function['function']['name']
        names[function_id] = name

    # Match the callback symbol to Rust functions
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
    parser.add_argument('--c-analysis', nargs='*', default=[])
    args = parser.parse_args()

    if not analyze(args.cfg, args.dataflow, args.targets, args.registrations, args.c_analysis, args.output):
        sys.exit(1)
