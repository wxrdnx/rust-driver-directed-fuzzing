import argparse
import json

from backward_slice import read_jsonl

def operation_index(functions):
    operations = {}
    for function in functions:
        function_id = function['function']['id']
        function_name = function['function']['name']
        for block in function['blocks']:
            for operation in block['statements'] + [block['terminator']]:
                operations[operation['id']] = {
                    'function_id': function_id,
                    'function': function_name,
                    'operation': operation,
                }

    return operations

def unsupported_types(value, records):
    if isinstance(value, list):
        for item in value:
            unsupported_types(item, records)
        return

    if not isinstance(value, dict):
        return
    if value.get('kind') == 'unsupported' and 'source' in value:
        source = value['source']
        record = {'reason': 'unsupported_type', 'type_kind': source['kind']}
        if 'rust' in source:
            record['rust_type'] = source['rust']
        if record not in records:
            records.append(record)

    for child in value.values():
        unsupported_types(child, records)

def enrich_fragment(fragment, operations):
    record = dict(fragment)
    operation_id = fragment.get('operation')
    if operation_id not in operations:
        return record

    indexed = operations[operation_id]
    operation = indexed['operation']
    record['function_id'] = indexed['function_id']
    record['function'] = indexed['function']
    record['operation_kind'] = operation['kind']

    if 'span' in operation:
        record['span'] = operation['span']
    if 'mir_kind' in operation:
        record['mir_kind'] = operation['mir_kind']
    if 'expression' in operation:
        record['mir_expression'] = operation['expression']

    return record

def summarize(partial_targets):
    reasons = {}
    details = {}
    for target in partial_targets:
        for fragment in target['fragments']:
            reason = fragment['reason']
            if reason not in reasons:
                reasons[reason] = {'reason': reason, 'occurrence_count': 0, 'targets': set()}
            reasons[reason]['occurrence_count'] += 1
            reasons[reason]['targets'].add(target['target']['id'])

            detail = fragment.get('intrinsic') or fragment.get('rust_type') or fragment.get('operation_kind') or fragment.get('expression_kind') or fragment.get('type_kind')
            key = reason, detail
            if key not in details:
                details[key] = {'reason': reason, 'detail': detail, 'occurrence_count': 0, 'targets': set()}
            details[key]['occurrence_count'] += 1
            details[key]['targets'].add(target['target']['id'])

    reason_records = []
    for record in reasons.values():
        record['target_count'] = len(record['targets'])
        record['targets'] = sorted(record['targets'])
        reason_records.append(record)
    reason_records.sort(key=lambda record: (-record['target_count'], record['reason']))

    detail_records = []
    for record in details.values():
        record['target_count'] = len(record['targets'])
        record['targets'] = sorted(record['targets'])
        detail_records.append(record)
    detail_records.sort(key=lambda record: (-record['target_count'], record['reason'], record['detail'] or ''))

    return reason_records, detail_records

def analyze(cfg_path, constraint_path, output_path):
    operations = operation_index(read_jsonl(cfg_path))
    with open(constraint_path) as file:
        constraints = json.load(file)

    partial_targets = []
    for target_record in constraints['targets']:
        constraint = target_record['constraint']
        if constraint['status'] != 'partial':
            continue

        fragments = []
        for fragment in constraint['unsupported']:
            enriched = enrich_fragment(fragment, operations)
            if enriched not in fragments:
                fragments.append(enriched)

        type_fragments = []
        unsupported_types(constraint['expression'], type_fragments)
        for fragment in type_fragments:
            if fragment not in fragments:
                fragments.append(fragment)
        partial_targets.append({'target': target_record['target'], 'fragments': fragments})

    reasons, details = summarize(partial_targets)
    report = {
        'schema_version': 1,
        'partial_target_count': len(partial_targets),
        'unsupported_by_reason': reasons,
        'unsupported_by_detail': details,
        'targets': partial_targets,
    }

    with open(output_path, 'w') as file:
        json.dump(report, file, indent=2)
        file.write('\n')
    return True

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('constraints')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.cfg, args.constraints, args.output)
