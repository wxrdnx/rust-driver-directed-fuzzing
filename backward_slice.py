import argparse

def read_jsonl(path):
    records = []
    with open(path) as file:
        for line in file:
            if line.strip():
                records.append(json.loads(line))
    return records

def operation_maps(function):
    pass

def control_dependencies(function):
    pass

def target_operation(function, target):
    pass

def slice_function(function, dataflow, target):
    operations, operation_blocks = operation_maps(function)
    definitions = {}
    for definition in function['definitions']:
        definitions[definition['id']] = definition
    for definition in dataflow['argument_definitions']:
        definitions[definition['id']] = definition

    reaching = {}
    for edge in dataflow['edges']:
        if edge['target'] not in reaching:
            reaching[edge['target']] = []
        reaching[edge['target']].append(edge['source'])

    dependencies = control_dependencies(function)
    start = target_operation(function, target)
    if start not in operations:
        return None

    selected_operations = set()
    selected_definitions = set()
    selected_uses = set()
    selected_inputs = set()
    unresolved = set()
    conditions = {}
    pending = [start]
    while pending:
        operation_id = pending.pop()
        if operation_id in selected_operations:
            continue
        selected_operations.add(operation_id)
        operation = operations[operation_id]

        block_id = operation_blocks[operation_id]
        for dependency in dependencies[block_id]:
            condition_id = dependency['operation']
            conditions[condition_id] = dependency
            if condition_id not in selected_operations:
                pending.append(condition_id)

        for use in operation.get('uses', []):
            use_id = use['id']
            selected_uses.add(use_id)
            sources = reaching.get(use_id, [])
            if not sources:
                unresolved.add(use_id)
            for definition_id in sources:
                selected_definitions.add(definition_id)
                definition = definitions[definition_id]
                if definition.get('kind') == 'argument':
                    selected_inputs.add(definition_id)
                    continue
                defining_operation = definition.get('operation')
                if defining_operation and defining_operation not in selected_operations:
                    pending.append(defining_operation)

    return {
        'target': target,
        'functions': [function['function']['id']],
        'operations': sorted(selected_operations),
        'definitions': sorted(selected_definitions),
        'uses': sorted(selected_uses),
        'control_conditions': list(conditions.values()),
        'inputs': sorted(selected_inputs),
        'unresolved': sorted(unresolved),
    }

def analyze(cfg_path, dataflow_path, target_path, output_path):
    cfgs = read_jsonl(cfg_path)
    dataflows = read_jsonl(dataflow_path)

    with open(target_path) as file:
        target_data = json.load(file)

    # support either
    # 1. a manually provided target file
    # 2. Rust analyzer's output (panic sites)
    # 3. TODO: unsafe blocks
    targets = target_data.get('targets')
    if targets is None:
        targets = target_data.get('panic_sites', [])

    dataflow_by_function = {}
    for dataflow in dataflows:
        dataflow_by_function[dataflow['function']['id']] = dataflow

    slices = []
    for target in targets:
        for function in cfgs:
            if function['function']['name'] != target['function']:
                continue
            function_id = function['function']['id']
            if function_id not in dataflow_by_function:
                continue
            result = slice_function(function, dataflow_by_function[function_id], target)
            if result:
                slices.append(result)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('dataflow')
    parser.add_argument('targets')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.cfg, args.dataflow, args.targets, args.output)
