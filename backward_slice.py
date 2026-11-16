import argparse
import json

def read_jsonl(path):
    records = []
    with open(path) as file:
        for line in file:
            if line.strip():
                records.append(json.loads(line))
    return records

def operation_maps(function):
    operations = {}
    operation_blocks = {}
    for block in function['blocks']:
        for statement in block['statements']:
            operations[statement['id']] = statement
            operation_blocks[statement['id']] = block['id']
        terminator = block['terminator']
        operations[terminator['id']] = terminator
        operation_blocks[terminator['id']] = block['id']
    return operations, operation_blocks

def control_dependencies(function):
    # Determine which branch condition controls which blocks executed
    # e.g.
    # bb0: check size == 0
    #     if true -> bb1
    #     if false -> bb2
    # In this case bb1 only executes when the condition in bb0 is true
    # So bb1 is control dependent on bb0

    successors = {}
    for block in function['blocks']:
        successors[block['id']] = []
    for edge in function['edges']:
        successors[edge['source']].append(edge['target'])

    successors['__exit__'] = []
    for block, targets in successors.items():
        if block != '__exit__' and not targets:
            targets.append('__exit__')

    all_blocks = set(successors)

    # Post-dominators
    # A block bb0 post-dominates bb1 when every path from bb0 ends in bb1
    # e.g.
    #    bb0
    #   /   \
    # bb2   bb3
    #   \   /
    #    bb1
    # In this case bb1 post-dominates bb0
    # However, bb2 does not post-dominates bb0 because the path may go through bb3
    postdominators = {}
    for block in successors:
        postdominators[block] = set(all_blocks)
    postdominators['__exit__'] = {'__exit__'}
    changed = True
    while changed:
        changed = False
        for block, targets in successors.items():
            if block == '__exit__':
                continue
            common = set(postdominators[targets[0]])
            for target in targets[1:]:
                common.intersection_update(postdominators[target])
            result = {block}
            result.update(common)
            if result != postdominators[block]:
                postdominators[block] = result
                changed = True

    # Find the closest post-dominator of every block
    # e.g.
    #    bb0
    #   /   \
    # bb2   bb3
    #   \   /
    #    bb1
    #     |
    #    bb4
    #     |
    #  __exit__
    # In this case  bb1, bb4, and __exit are all bb0's post-dominator
    # But bb1 is the closest, so the closest post-dominator of bb0 is bb1
    immediate = {}
    for block in successors:
        if block == '__exit__':
            continue
        candidates = postdominators[block] - {block}
        for candidate in candidates:
            closest = True
            for other in candidates:
                if other != candidate and candidate in postdominators[other]:
                    closest = False
                    break
            if closest:
                immediate[block] = candidate
                break

    dependencies = {}
    for block in successors:
        if block != '__exit__':
            dependencies[block] = []

    # Build block lookup table
    blocks = {}
    for block in function['blocks']:
        blocks[block['id']] = block

    # Examine every CFG edge and find SwitchInt
    # Only switch conditions need to be handled because it's the main representation for branches
    for edge in function['edges']:
        source = edge['source']
        target = edge['target']
        if target in postdominators[source]:
            continue
        terminator = blocks[source]['terminator']

        # Currently we only deal with control dependencies of "regular" branches
        # e.g. match, if-else, loop, ...
        # These all becomes SwitchInt in the MIR representation
        if terminator['kind'] == 'switch':
            runner = target
            stop = immediate.get(source)
            while runner != stop and runner != '__exit__':
                dependency = {
                    'operation': terminator['id'],
                    'block': source,
                    'edge': {key: value for key, value in edge.items() if key != 'condition'},
                }
                if dependency not in dependencies[runner]:
                    dependencies[runner].append(dependency)
                runner = immediate.get(runner, '__exit__')
        else:
            # TODO: other kinds
            pass
    return dependencies

def target_operation(function, target):
    if target.get('operation'):
        return target['operation']
    location = target['mir_location']
    basic_block = location['basic_block']
    block_id = f'bb{basic_block}'
    for block in function['blocks']:
        if block['id'] != block_id:
            continue
        if location.get('terminator'):
            return block['terminator']['id']
        statement = location.get('statement_index')
        if statement is not None:
            return block['statements'][statement]['id']
    return None

def build_program_index(functions, dataflows):
    dataflow_by_function = {}
    for dataflow in dataflows:
        dataflow_by_function[dataflow['function']['id']] = dataflow
    indexes = {}
    callers = {}
    for function in functions:
        function_id = function['function']['id']
        if function_id not in dataflow_by_function:
            continue
        dataflow = dataflow_by_function[function_id]
        operations, operation_blocks = operation_maps(function)
        definitions = {}
        uses = {}
        for definition in function['definitions']:
            definitions[definition['id']] = definition
        for definition in dataflow['argument_definitions']:
            definitions[definition['id']] = definition
        for operation in operations.values():
            for use in operation.get('uses', []):
                uses[use['id']] = use
        reaching = {}
        for edge in dataflow['edges']:
            if edge['target'] not in reaching:
                reaching[edge['target']] = []
            reaching[edge['target']].append(edge['source'])
        indexes[function_id] = {
            'operations': operations,
            'operation_blocks': operation_blocks,
            'definitions': definitions,
            'uses': uses,
            'reaching': reaching,
            'dependencies': control_dependencies(function),
        }

        for operation in operations.values():
            if operation['kind'] != 'call':
                continue
            data = operation.get('data') or {}
            callee_id = data.get('callee_id')
            if not callee_id:
                continue
            if callee_id not in callers:
                callers[callee_id] = []
            arguments = {}
            for use in operation.get('uses', []):
                role = use.get('role', '')
                if role.startswith('argument_'):
                    arguments[int(role.removeprefix('argument_'))] = use['id']
            callers[callee_id].append({'function': function_id, 'operation': operation['id'], 'arguments': arguments})
    return indexes, callers

def slice_program(functions, dataflows, target_function, target, program=None):
    if program is None:
        program = build_program_index(functions, dataflows)
    indexes, callers = program
    target_function_id = target_function['function']['id']
    if target_function_id not in indexes:
        return None
    start = target_operation(target_function, target)
    if start not in indexes[target_function_id]['operations']:
        return None

    selected_functions = set()
    selected_operations = set()
    selected_definitions = set()
    selected_uses = set()
    selected_inputs = set()
    unresolved = set()
    conditions = {}
    visited = set()
    pending = [(target_function_id, start, None)]
    while pending:
        function_id, operation_id, selected_use = pending.pop()
        work = function_id, operation_id, selected_use
        if work in visited:
            continue
        visited.add(work)
        index = indexes[function_id]
        selected_functions.add(function_id)
        selected_operations.add(operation_id)
        operation = index['operations'][operation_id]

        block_id = index['operation_blocks'][operation_id]
        for dependency in index['dependencies'][block_id]:
            condition_id = dependency['operation']
            conditions[condition_id] = dependency
            pending.append((function_id, condition_id, None))

        operation_uses = operation.get('uses', [])
        if selected_use:
            operation_uses = [index['uses'][selected_use]]
        for use in operation_uses:
            use_id = use['id']
            selected_uses.add(use_id)
            sources = index['reaching'].get(use_id, [])
            if not sources:
                unresolved.add(use_id)
            for definition_id in sources:
                selected_definitions.add(definition_id)
                definition = index['definitions'][definition_id]
                if definition.get('kind') == 'argument':
                    argument_index = definition.get('argument_index')
                    if argument_index is None:
                        argument_index = int(definition_id.rsplit(':argument:', 1)[1])
                    mapped = False
                    for call in callers.get(function_id, []):
                        caller_use = call['arguments'].get(argument_index)
                        if caller_use:
                            pending.append((call['function'], call['operation'], caller_use))
                            mapped = True
                    if not mapped:
                        selected_inputs.add(definition_id)
                    continue
                defining_operation = definition.get('operation')
                if defining_operation:
                    pending.append((function_id, defining_operation, None))

    return {
        'target': target,
        'functions': sorted(selected_functions),
        'operations': sorted(selected_operations),
        'definitions': sorted(selected_definitions),
        'uses': sorted(selected_uses),
        'control_conditions': list(conditions.values()),
        'inputs': sorted(selected_inputs),
        'unresolved': sorted(unresolved),
    }

def slice_function(function, dataflow, target):
    return slice_program([function], [dataflow], function, target)

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
    program = build_program_index(cfgs, dataflows)

    slices = []
    for target in targets:
        for function in cfgs:
            if function['function']['name'] != target['function']:
                continue
            function_id = function['function']['id']
            if function_id not in dataflow_by_function:
                continue
            result = slice_program(cfgs, dataflows, function, target, program)
            if result:
                slices.append(result)

    with open(output_path, 'w') as output:
        for result in slices:
            output.write(json.dumps(result, separators=(',', ':')) + '\n')
    return bool(slices)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('dataflow')
    parser.add_argument('targets')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.cfg, args.dataflow, args.targets, args.output)
