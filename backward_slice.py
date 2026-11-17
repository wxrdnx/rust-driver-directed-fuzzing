import argparse
import json
import os

SHARD_SIZE = 50000

class ContextTable:
    def __init__(self):
        self.records = [None]
        self.names = ['context-0']
        self.transitions = {}

    def extend(self, context_id, direction, frame):
        transition = context_id, direction, frame
        if transition in self.transitions:
            return self.transitions[transition]
        next_id = len(self.records)
        self.transitions[transition] = next_id
        self.records.append((context_id, direction, frame))
        self.names.append(f'context-{next_id}')
        return next_id

    def name(self, context_id):
        return self.names[context_id]

    def contains(self, context_id, frame):
        while context_id:
            parent, _, value = self.records[context_id]
            if value == frame:
                return True
            context_id = parent
        return False

    def parent(self, context_id):
        return self.records[context_id][0]

    def serialized(self):
        records = [{'id': 'context-0', 'parent': None, 'direction': None, 'frame': None}]
        for context_id in range(1, len(self.records)):
            parent, direction, frame = self.records[context_id]
            caller, operation, callee = frame
            records.append({
                'id': f'context-{context_id}',
                'parent': f'context-{parent}',
                'direction': direction,
                'frame': {'caller': caller, 'operation': operation, 'callee': callee},
            })
        return records

class StackTable:
    def __init__(self):
        self.records = [None]
        self.names = ['stack-0']
        self.transitions = {}

    def push(self, stack_id, frame):
        transition = stack_id, frame
        if transition in self.transitions:
            return self.transitions[transition]
        next_id = len(self.records)
        self.transitions[transition] = next_id
        self.records.append((stack_id, frame))
        self.names.append(f'stack-{next_id}')
        return next_id

    def name(self, stack_id):
        return self.names[stack_id]

    def top(self, stack_id):
        return self.records[stack_id][1]

    def pop(self, stack_id):
        return self.records[stack_id][0]

    def serialized(self):
        records = [{'id': 'stack-0', 'parent': None, 'frame': None}]
        for stack_id in range(1, len(self.records)):
            parent, frame = self.records[stack_id]
            caller, operation, callee = frame
            records.append({
                'id': f'stack-{stack_id}',
                'parent': f'stack-{parent}',
                'frame': {'caller': caller, 'operation': operation, 'callee': callee},
            })
        return records

class DependencyGraph:
    def __init__(self, program):
        self.indexes, self.callers = program
        self.nodes = {}
        self.node_ids = {}
        self.edges = []
        self.edge_ids = set()
        self.pending = []
        self.contexts = ContextTable()
        self.stacks = StackTable()

    def add_target(self, target_function, target):
        function_id = target_function['function']['id']
        if function_id not in self.indexes:
            return None
        operation_id = target.get('operation')
        if not operation_id:
            location = target['mir_location']
            basic_block = location['basic_block']
            block_id = f'bb{basic_block}'
            for block in target_function['blocks']:
                if block['id'] != block_id:
                    continue
                if location.get('terminator'):
                    operation_id = block['terminator']['id']
                else:
                    statement_index = location.get('statement_index')
                    if statement_index is not None:
                        operation_id = block['statements'][statement_index]['id']
                break
        if operation_id not in self.indexes[function_id]['operations']:
            return None
        return self.add_node('operation', function_id, operation_id, None, 0, 0)

    def add_node(self, kind, function_id, item_id, selected_use, call_stack, call_context):
        identity = kind, function_id, item_id, selected_use, call_stack, call_context
        if identity in self.node_ids:
            return self.node_ids[identity]
        node_id = f'node-{len(self.node_ids) + 1}'
        self.node_ids[identity] = node_id
        self.nodes[node_id] = {
            'id': node_id,
            'kind': kind,
            'function': function_id,
            'item': item_id,
            'selected_use': selected_use,
            'call_stack': self.stacks.name(call_stack),
            'call_context': self.contexts.name(call_context),
        }
        self.pending.append(identity)
        return node_id

    def add_edge(self, source, target, relation, role):
        identity = source, target, relation, role
        if identity in self.edge_ids:
            return
        self.edge_ids.add(identity)
        self.edges.append({'source': source, 'target': target, 'relation': relation, 'role': role})

    def add_cutoff(self, context, frame):
        identity = 'recursion_cutoff', context, frame
        if identity in self.node_ids:
            return self.node_ids[identity]
        node_id = f'node-{len(self.node_ids) + 1}'
        self.node_ids[identity] = node_id
        caller, operation, callee = frame
        self.nodes[node_id] = {
            'id': node_id,
            'kind': 'recursion_cutoff',
            'call_context': self.contexts.name(context),
            'frame': {'caller': caller, 'operation': operation, 'callee': callee},
        }
        return node_id

    def expand(self):
        while self.pending:
            kind, function_id, item_id, selected_use, call_stack, call_context = self.pending.pop()
            node_id = self.node_ids[(kind, function_id, item_id, selected_use, call_stack, call_context)]
            index = self.indexes[function_id]
            if kind == 'use':
                sources = index['reaching'].get(item_id, [])
                if not sources:
                    self.nodes[node_id]['unresolved'] = True
                for definition_id in sources:
                    child = self.add_node('definition', function_id, definition_id, None, call_stack, call_context)
                    self.add_edge(node_id, child, 'one_of', 'reaching_definition')
                continue

            if kind == 'definition':
                self.expand_definition(node_id, function_id, item_id, call_stack, call_context)
                continue

            operation = index['operations'][item_id]
            block_id = index['operation_blocks'][item_id]
            for dependency in index['dependencies'][block_id]:
                child = self.add_node('operation', function_id, dependency['operation'], None, call_stack, call_context)
                self.add_edge(node_id, child, 'all_of', 'control')
            operation_uses = operation.get('uses', [])
            if selected_use is False:
                operation_uses = []
            elif selected_use is not None:
                operation_uses = [index['uses'][selected_use]]
            for use in operation_uses:
                child = self.add_node('use', function_id, use['id'], None, call_stack, call_context)
                self.add_edge(node_id, child, 'all_of', 'data')

    def expand_definition(self, node_id, function_id, item_id, call_stack, call_context):
        index = self.indexes[function_id]
        definition = index['definitions'][item_id]
        if definition.get('kind') == 'argument':
            self.expand_argument(node_id, function_id, definition, call_stack, call_context)
            return
        defining_operation = definition.get('operation')
        if not defining_operation:
            self.nodes[node_id]['unresolved'] = True
            return
        defining = index['operations'][defining_operation]
        if definition.get('role') == 'return_value' and defining['kind'] == 'call':
            data = defining.get('data') or {}
            callee_id = data.get('callee_id')
            if callee_id in self.indexes and self.indexes[callee_id]['returns']:
                child = self.add_node('operation', function_id, defining_operation, False, call_stack, call_context)
                self.add_edge(node_id, child, 'all_of', 'call')
                frame = function_id, defining_operation, callee_id
                # TODO: Use fixed-point SCC summaries to preserve recursive dependencies instead of cutting them off
                if self.contexts.contains(call_context, frame):
                    child = self.add_cutoff(call_context, frame)
                    self.add_edge(node_id, child, 'one_of', 'return_value')
                    return
                callee_stack = self.stacks.push(call_stack, frame)
                callee_context = self.contexts.extend(call_context, 'append', frame)
                for return_operation, return_use in self.indexes[callee_id]['returns']:
                    child = self.add_node('operation', callee_id, return_operation, return_use, callee_stack, callee_context)
                    self.add_edge(node_id, child, 'one_of', 'return_value')
                return
        child = self.add_node('operation', function_id, defining_operation, None, call_stack, call_context)
        self.add_edge(node_id, child, 'all_of', 'definition')

    def expand_argument(self, node_id, function_id, definition, call_stack, call_context):
        argument_index = definition.get('argument_index')
        possible_callers = self.callers.get(function_id, [])
        matching_callers = []
        next_stack = call_stack
        next_context = call_context
        matched_stack = False
        if call_stack and self.stacks.top(call_stack)[2] == function_id:
            frame = self.stacks.top(call_stack)
            for call in possible_callers:
                if call['function'] == frame[0] and call['operation'] == frame[1]:
                    matching_callers.append(call)
            next_stack = self.stacks.pop(call_stack)
            next_context = self.contexts.parent(call_context)
            matched_stack = True
        else:
            matching_callers = possible_callers
        mapped = False
        for call in matching_callers:
            caller_use = call['arguments'].get(argument_index)
            if not caller_use:
                continue
            context = next_context
            if not matched_stack:
                frame = call['function'], call['operation'], function_id
                if self.contexts.contains(call_context, frame):
                    child = self.add_cutoff(call_context, frame)
                    self.add_edge(node_id, child, 'one_of', 'caller')
                    mapped = True
                    continue
                context = self.contexts.extend(call_context, 'prepend', frame)
            child = self.add_node('operation', call['function'], call['operation'], caller_use, next_stack, context)
            self.add_edge(node_id, child, 'one_of', 'caller')
            mapped = True
        if not mapped:
            self.nodes[node_id]['external_input'] = True

    def result(self, root=None):
        result = {
            'nodes': list(self.nodes.values()),
            'edges': self.edges,
            'call_contexts': self.contexts.serialized(),
            'call_stacks': self.stacks.serialized(),
        }
        if root:
            result['root'] = root
        return result

def write_atomic_json(path, value):
    temporary_path = path + '.tmp'
    with open(temporary_path, 'w') as output:
        json.dump(value, output, separators=(',', ':'))
    os.replace(temporary_path, path)

def write_shards(records, output_path, directory, prefix):
    shard_path = os.path.join(output_path, directory)
    os.makedirs(shard_path, exist_ok=True)
    shards = []
    chunk = []
    for record in records:
        chunk.append(record)
        if len(chunk) < SHARD_SIZE:
            continue
        shard_name = f'{prefix}-{len(shards) + 1:06d}.json'
        write_atomic_json(os.path.join(shard_path, shard_name), chunk)
        shards.append(os.path.join(directory, shard_name))
        chunk = []
    if chunk:
        shard_name = f'{prefix}-{len(shards) + 1:06d}.json'
        write_atomic_json(os.path.join(shard_path, shard_name), chunk)
        shards.append(os.path.join(directory, shard_name))
    return shards

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
    graph = DependencyGraph(program)
    root = graph.add_target(target_function, target)
    if not root:
        return None
    graph.expand()
    return {'target': target, 'graph': graph.result(root)}

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

    os.makedirs(output_path, exist_ok=True)
    manifest_path = os.path.join(output_path, 'manifest.json')
    if os.path.exists(manifest_path):
        os.unlink(manifest_path)

    graph = DependencyGraph(program)
    target_roots = []
    for target in targets:
        function = functions_by_id[target['function_id']]
        root = graph.add_target(function, target)
        if not root:
            continue
        target_roots.append({'target': target, 'root': root})
    if not target_roots:
        return False

    graph.expand()
    write_atomic_json(os.path.join(output_path, 'targets.json'), target_roots)
    node_shards = write_shards(graph.nodes.values(), output_path, 'nodes', 'nodes')
    edge_shards = write_shards(graph.edges, output_path, 'edges', 'edges')
    write_atomic_json(os.path.join(output_path, 'call-contexts.json'), graph.contexts.serialized())
    write_atomic_json(os.path.join(output_path, 'call-stacks.json'), graph.stacks.serialized())
    manifest = {
        'complete': True,
        'targets': 'targets.json',
        'node_shards': node_shards,
        'edge_shards': edge_shards,
        'call_contexts': 'call-contexts.json',
        'call_stacks': 'call-stacks.json',
        'node_count': len(graph.nodes),
        'edge_count': len(graph.edges),
        'shard_size': SHARD_SIZE,
    }
    # Publish the manifest only after every graph file is complete
    write_atomic_json(manifest_path, manifest)
    return True

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('dataflow')
    parser.add_argument('targets')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.cfg, args.dataflow, args.targets, args.output)
