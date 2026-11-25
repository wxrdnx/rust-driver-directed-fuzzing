import argparse
import json

from backward_slice import build_program_index, read_jsonl
from constraint_ir import ConstraintBuilder
from expression_resolver import ExpressionResolver

def analyze(cfg_path, dataflow_path, target_path, output_path):
    functions = read_jsonl(cfg_path)
    dataflows = read_jsonl(dataflow_path)
    with open(target_path) as file:
        target_data = json.load(file)
    targets = target_data.get('targets')
    if targets is None:
        targets = target_data.get('panic_sites', [])
    indexes, _ = build_program_index(functions, dataflows)
    resolver = ExpressionResolver(indexes)
    records = []
    counts = {'complete': 0, 'partial': 0, 'skipped': 0}
    for target in targets:
        function_id = target['function_id']
        use_id = None
        if function_id in indexes and 'mir_location' in target:
            block = target['mir_location']['basic_block']
            operation_id = f'{function_id}:bb{block}:term'
            operation = indexes[function_id]['operations'].get(operation_id)
            if operation:
                for use in operation['uses']:
                    if use['role'] == 'condition':
                        use_id = use['id']
                        break
        if use_id is None:
            counts['skipped'] += 1
            continue
        resolved = resolver.result(function_id, use_id)
        constraint = ConstraintBuilder().assertion(resolved, target['expected'])
        counts[constraint['status']] += 1
        records.append({'target': target, 'constraint': constraint})
    report = {
        'schema_version': 1,
        'target_count': len(targets),
        'condition_count': len(records),
        'status_counts': counts,
        'targets': records,
    }
    with open(output_path, 'w') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    return True


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('dataflow')
    parser.add_argument('targets')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.cfg, args.dataflow, args.targets, args.output)
