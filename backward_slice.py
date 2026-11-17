import argparse
import json

# Number of recent call sites used to distinguish visited states
CALL_CONTEXT_DEPTH = 2
# Maximum number of call sites kept in a recorded call path
MAX_CALL_PATH_DEPTH = 16

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

def extend_call_history(call_history, frame):
    if not call_history:
        return (frame,)
    if call_history[-1][2] == frame[0]:
        call_history = call_history + (frame,)
        return call_history[-MAX_CALL_PATH_DEPTH:]
    if frame[2] == call_history[0][0]:
        call_history = (frame,) + call_history
        return call_history[-MAX_CALL_PATH_DEPTH:]
    return (frame,)

# TODO: Interprocedural control dependency analysis

def control_dependencies(function):
    # Intraprocedural control dependency analysis
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
            # postdominators(block) = {block} union (postdominators(successor 0) intersect ... intersect postdominators(successor n))
            common = set(successors)
            for target in targets:
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
    immediate_postdominator = {}
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
                immediate_postdominator[block] = candidate
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
    # Currently we only deal with control dependencies of "regular" branches
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
            stop = immediate_postdominator.get(source)
            while runner != stop and runner != '__exit__':
                dependency = {
                    'operation': terminator['id'],
                    'block': source,
                    'edge': {key: value for key, value in edge.items() if key != 'condition'},
                }
                if dependency not in dependencies[runner]:
                    dependencies[runner].append(dependency)
                runner = immediate_postdominator.get(runner, '__exit__')
        else:
            # TODO: other kinds
            pass
    return dependencies

def build_program_index(functions, dataflows):
    # Reorganize CFG + DFG into lookup tables used by interprocedural backward slicing
    # Repeatedly scanning lists during slicing is too slow
    # So we build a dictionary indexed by IDs instead

    dataflow_by_function = {}
    for dataflow in dataflows:
        dataflow_by_function[dataflow['function']['id']] = dataflow

    # indexes contains analysis information for every function

    # e.g.
    # fn helper(value: usize) -> usize {
    #     value + 1
    # }
    # fn caller_a(input: usize) {
    #     let result = helper(input);
    # }
    # fn caller_b(size: usize) {
    #     let result = helper(size);
    # }
    #
    # For the helper function, the result will be
    #
    # indexes = {
    #     'helper': {
    #         'operations': {
    #             'helper:bb0:stmt0': {'kind': 'assignment'},
    #             'helper:bb0:term': {'kind': 'return'},
    #         },
    #         'operation_blocks': {
    #             'helper:bb0:stmt0': 'bb0',
    #             'helper:bb0:term': 'bb0',
    #         },
    #         'definitions': {
    #             'helper:bb0:stmt0:def': {'operation': 'helper:bb0:stmt0'},
    #         },
    #         'uses': {
    #             'helper:bb0:term:use0': {'role': 'return_value'},
    #         },
    #         'returns': [('helper:bb0:term', 'helper:bb0:term:use0')],
    #         'reaching': {
    #             'helper:bb0:term:use0': ['helper:bb0:stmt0:def'],
    #         },
    #         'dependencies': {
    #             'bb0': [],
    #         },
    #     }
    # }
    indexes = {}

    # callers maps each callee to its call sites

    # e.g.
    # fn helper(value: usize) -> usize {
    #     value + 1
    # }
    # fn caller_a(input: usize) {
    #     let result = helper(input);
    # }
    # fn caller_b(size: usize) {
    #     let result = helper(size);
    # }
    # Then helper is the callee, and caller_a and caller_b each contains a call site that calls helper
    # 
    # The result will be
    # callers = {
    #     'helper': [
    #         {
    #             'function': 'caller_a',
    #             'operation': 'caller_a:bb0:term',
    #             'arguments': {
    #                 0: 'caller_a:bb0:term:use0',
    #             },
    #         },
    #         {
    #             'function': 'caller_b',
    #             'operation': 'caller_b:bb2:term',
    #             'arguments': {
    #                 0: 'caller_b:bb2:term:use0',
    #             },
    #         },
    #     ]
    # }

    callers = {}

    for function in functions:
        function_id = function['function']['id']
        dataflow = dataflow_by_function[function_id]
        operations, operation_blocks = operation_maps(function)
        definitions = {}
        uses = {}
        returns = []

        # Combine MIR definitions and argument pseudo-definitions
        for definition in function['definitions']:
            definitions[definition['id']] = definition
        for definition in dataflow['argument_definitions']:
            definitions[definition['id']] = definition

        for operation in operations.values():
            for use in operation.get('uses', []):
                uses[use['id']] = use
                if operation['kind'] == 'return' and use.get('role') == 'return_value':
                    returns.append((operation['id'], use['id']))
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
            'returns': returns,
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

def slice_program(program, target_function, target):
    indexes, callers = program
    target_function_id = target_function['function']['id']
    if target_function_id not in indexes:
        return None
    start = target.get('operation')
    if not start:
        location = target['mir_location']
        basic_block = location['basic_block']
        block_id = f'bb{basic_block}'
        for block in target_function['blocks']:
            if block['id'] != block_id:
                continue
            if location.get('terminator'):
                start = block['terminator']['id']
            else:
                statement_index = location.get('statement_index')
                if statement_index is not None:
                    start = block['statements'][statement_index]['id']
            break
    if start not in indexes[target_function_id]['operations']:
        return None

    selected_functions = set()
    selected_operations = set()
    selected_definitions = set()
    selected_uses = set()
    selected_inputs = set()
    unresolved = set()
    conditions = {}
    call_paths = set()
    visited = set()
    pending = [(target_function_id, start, None, (), ())]
    while pending:
        function_id, operation_id, selected_use, call_stack, call_history = pending.pop()
        context = []
        for frame in call_stack[-CALL_CONTEXT_DEPTH:]:
            context.append(frame[1])
        context = tuple(context)
        work = function_id, operation_id, selected_use, context
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
            pending.append((function_id, condition_id, None, call_stack, call_history))

        operation_uses = operation.get('uses', [])
        if selected_use is False:
            operation_uses = []
        elif selected_use is not None:
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
                    mapped = False
                    possible_callers = callers.get(function_id, [])
                    matching_callers = []
                    next_stack = call_stack
                    matched_stack = False
                    if call_stack and call_stack[-1][2] == function_id:
                        frame = call_stack[-1]
                        for call in possible_callers:
                            if call['function'] == frame[0] and call['operation'] == frame[1]:
                                matching_callers.append(call)
                        next_stack = call_stack[:-1]
                        matched_stack = True
                    else:
                        matching_callers = possible_callers
                    for call in matching_callers:
                        caller_use = call['arguments'].get(argument_index)
                        if caller_use:
                            history = call_history
                            if not matched_stack:
                                frame = call['function'], call['operation'], function_id
                                history = extend_call_history(call_history, frame)
                            pending.append((call['function'], call['operation'], caller_use, next_stack, history))
                            if history:
                                call_paths.add(history)
                            mapped = True
                    if not mapped:
                        selected_inputs.add(definition_id)
                        if call_history:
                            call_paths.add(call_history)
                    continue
                defining_operation = definition.get('operation')
                if defining_operation:
                    defining = index['operations'][defining_operation]

                    # Interprocedural return value mapping

                    # For function assignments like
                    #     let result = calculate(num)
                    # In this case reult is defined by the call
                    #     result <- call calculate(num)
                    # But in fact, the actual value comes from _0
                    #     result <- callee _0
                    if definition.get('role') == 'return_value' and defining['kind'] == 'call':
                        data = defining.get('data') or {}
                        callee_id = data.get('callee_id')
                        if callee_id in indexes and indexes[callee_id]['returns']:
                            pending.append((function_id, defining_operation, False, call_stack, call_history))
                            frame = function_id, defining_operation, callee_id
                            callee_stack = call_stack + (frame,)
                            callee_history = extend_call_history(call_history, frame)
                            call_paths.add(callee_history)
                            for return_operation, return_use in indexes[callee_id]['returns']:
                                pending.append((callee_id, return_operation, return_use, callee_stack, callee_history))
                            continue

                    # For other ordinary assignments like
                    #     let foo = bar + 1
                    # Adds the entire assignment operation
                    pending.append((function_id, defining_operation, None, call_stack, call_history))

    formatted_paths = []
    for path in sorted(call_paths):
        formatted = []
        for caller, operation, callee in path:
            formatted.append({'caller': caller, 'operation': operation, 'callee': callee})
        formatted_paths.append(formatted)

    return {
        'target': target,
        'functions': sorted(selected_functions),
        'operations': sorted(selected_operations),
        'definitions': sorted(selected_definitions),
        'uses': sorted(selected_uses),
        'control_conditions': list(conditions.values()),
        'inputs': sorted(selected_inputs),
        'unresolved': sorted(unresolved),
        'call_paths': formatted_paths,
    }

def slice_function(function, dataflow, target):
    program = build_program_index([function], [dataflow])
    return slice_program(program, function, target)

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

    functions_by_id = {}
    for function in cfgs:
        functions_by_id[function['function']['id']] = function
    program = build_program_index(cfgs, dataflows)

    slices = []
    for target in targets:
        function = functions_by_id[target['function_id']]
        result = slice_program(program, function, target)
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
