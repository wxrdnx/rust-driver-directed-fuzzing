import argparse
import json
import os

SHARD_SIZE = 50000

def call_arguments(operation):
    arguments = {}
    for use in operation.get('uses', []):
        role = use.get('role', '')
        if role.startswith('argument_'):
            index = int(role.removeprefix('argument_'))
            arguments[index] = {'kind': 'use', 'id': use['id']}
    data = operation.get('data') or {}
    for index, operand in enumerate(data.get('arguments', [])):
        if index not in arguments and operand.get('kind') == 'constant':
            arguments[index] = {'kind': 'constant', 'operand': operand}
    return arguments

def call_targets(operation):
    data = operation.get('data') or {}
    # callee_ids: indirect call, multiple possible targets
    if 'callee_ids' in data:
        return data['callee_ids']
    # callee_id: statically known target
    if data.get('callee_id') is not None:
        return [data['callee_id']]
    return []

def function_ids(value):
    found = set()

    # Find the function ID stored anywhere in the MIR structure
    # This can be either a dict or list, so we do it recursively
    if isinstance(value, dict):
        function_id = value.get('function_id')
        if function_id:
            found.add(function_id)
        for nested in value.values():
            found |= function_ids(nested)
    elif isinstance(value, list):
        for nested in value:
            found |= function_ids(nested)
    return found

def resolve_indirect_calls(indexes):
    # Determines target functions of indirect calls (calls through pointerss)

    def resolve_use(index, use_id, visited):
        # Traces function pointer backward to find possible function values
        if use_id in visited:
            return set()
        visited.add(use_id)
        targets = set()
        for definition_id in index['reaching'].get(use_id, []):
            definition = index['definitions'][definition_id]
            operation_id = definition.get('operation')
            if not operation_id:
                continue
            operation = index['operations'][operation_id]
            targets |= function_ids(operation.get('expression'))
            for nested_use in operation.get('uses', []):
                targets |= resolve_use(index, nested_use['id'], visited)
        return targets

    for index in indexes.values():
        for operation in index['operations'].values():
            if operation['kind'] != 'call' or call_targets(operation):
                continue
            callee_use = None
            for use in operation.get('uses', []):
                if use.get('role') == 'callee':
                    callee_use = use['id']
                    break
            if callee_use:
                data = operation.get('data') or {}
                data['callee_ids'] = sorted(resolve_use(index, callee_use, set()))

class ContextTable:

    # The same function may be reached through different callers:
    # e.g.
    # fn update_ref(value: u32) {
    #     check(value);
    # }
    # fn ioctl_a(user_value: u32) {
    #     process.update_ref(user_value);
    # }
    #
    # fn ioctl_b(default_value: u32) {
    #     process.update_ref(default_value);
    # }
    #
    # Thus
    #      ioctl_a -> Process::update_ref
    #      and
    #      ioctl_b -> Process::update_ref
    # Both reaches Process::update_ref via different paths
    # When slicing backward from it, the analysis could combine ioctl_a and ioctl_b:
    #      value <- ioctl_a.some_value
    #      value <- ioctl_b.other_value
    # They can make dependencies from different paths look like one execution
    # With call contexts, the become different nodes:
    #      Process::update_ref
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

    def find(self, context_id, frame):
        while context_id:
            parent, _, value = self.records[context_id]
            if value == frame:
                return context_id
            context_id = parent
        return None

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

class FunctionSummaries:
    def __init__(self, indexes):
        self.indexes = indexes
        self.cache = {}
        self.visiting = set()
        self.components, self.component_by_function = self.find_components()
        self.building_components = set()

    def find_components(self):
        calls = {}
        for function_id, index in self.indexes.items():
            calls[function_id] = set()
            for operation in index['operations'].values():
                if operation['kind'] != 'call':
                    continue
                for callee_id in call_targets(operation):
                    if callee_id in self.indexes:
                        calls[function_id].add(callee_id)
        next_index = 0
        indices = {}
        lowlinks = {}
        stack = []
        on_stack = set()
        components = []

        def visit(function_id):
            nonlocal next_index
            indices[function_id] = next_index
            lowlinks[function_id] = next_index
            next_index += 1
            stack.append(function_id)
            on_stack.add(function_id)
            for callee_id in calls[function_id]:
                if callee_id not in indices:
                    visit(callee_id)
                    lowlinks[function_id] = min(lowlinks[function_id], lowlinks[callee_id])
                elif callee_id in on_stack:
                    lowlinks[function_id] = min(lowlinks[function_id], indices[callee_id])
            if lowlinks[function_id] != indices[function_id]:
                return
            component = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == function_id:
                    break
            components.append(component)

        for function_id in self.indexes:
            if function_id not in indices:
                visit(function_id)
        component_by_function = {}
        for component_id, component in enumerate(components):
            for function_id in component:
                component_by_function[function_id] = component_id
        recursive = set()
        for component_id, component in enumerate(components):
            if len(component) > 1 or component[0] in calls[component[0]]:
                recursive.add(component_id)
        return {'members': components, 'recursive': recursive}, component_by_function

    def get(self, function_id):
        if function_id in self.cache:
            return self.cache[function_id]
        component_id = self.component_by_function[function_id]
        if component_id in self.components['recursive']:
            self.build_component(component_id)
            return self.cache.get(function_id)
        if function_id in self.visiting:
            return None
        self.visiting.add(function_id)
        summary = self.build(function_id)
        self.visiting.remove(function_id)
        self.cache[function_id] = summary
        return summary

    def build_component(self, component_id):
        if component_id in self.building_components:
            return
        self.building_components.add(component_id)
        members = self.components['members'][component_id]
        member_set = set(members)
        arguments = {}
        for function_id in members:
            arguments[function_id] = set()
        changed = True
        valid = True
        while changed and valid:
            changed = False
            for function_id in members:
                summary = self.build(function_id, member_set, arguments)
                if summary is None:
                    valid = False
                    break
                found = set()
                for node in summary['nodes']:
                    if node['kind'] == 'argument':
                        found.add(node['index'])
                found |= arguments[function_id]
                if found != arguments[function_id]:
                    arguments[function_id] = found
                    changed = True
        if valid:
            for function_id in members:
                self.cache[function_id] = self.build(function_id, member_set, arguments)
        else:
            for function_id in members:
                self.cache[function_id] = None
        self.building_components.remove(component_id)

    def argument_nodes(self, summary):
        arguments = []
        for node in summary['nodes']:
            if node['kind'] == 'argument':
                arguments.append(node)
        arguments.sort(key=lambda node: node['index'])
        return arguments

    def argument_node_id(self, argument_index):
        return f'summary-argument-{argument_index}'

    def build(self, function_id, component=None, recursive_arguments=None):
        index = self.indexes[function_id]
        if not index['returns']:
            return None
        nodes = {}
        node_ids = {}
        edges = []
        edge_ids = set()
        pending = []
        root = 'summary-root'
        nodes[root] = {'id': root, 'kind': 'return_value'}
        return_sites = []
        callees = set()

        def add_node(kind, item_id, selected_use=None, expand=True, operand=None):
            identity = kind, item_id, selected_use
            if identity in node_ids:
                return node_ids[identity]
            if kind == 'argument':
                node_id = self.argument_node_id(item_id)
            else:
                node_id = f'summary-node-{len(node_ids) + 1}'
            node_ids[identity] = node_id
            node = {'id': node_id, 'kind': kind}
            if kind == 'operation':
                node['operation'] = item_id
                node['selected_use'] = selected_use
            elif kind == 'use':
                node['use'] = item_id
            elif kind == 'definition':
                node['definition'] = item_id
            elif kind == 'argument':
                node['index'] = item_id
            elif kind == 'constant':
                node['operand'] = operand
            else:
                node['function'] = selected_use
                node['operation'] = item_id
                node['argument_bindings'] = []
            nodes[node_id] = node
            if expand:
                pending.append(identity)
            return node_id

        def add_edge(source, target, relation, role):
            identity = source, target, relation, role
            if identity in edge_ids:
                return
            edge_ids.add(identity)
            edges.append({'source': source, 'target': target, 'relation': relation, 'role': role})

        for operation_id, use_id in index['returns']:
            return_site = add_node('operation', operation_id, use_id)
            return_sites.append(return_site)
            add_edge(root, return_site, 'one_of', 'return_site')
        while pending:
            kind, item_id, selected_use = pending.pop()
            node_id = node_ids[(kind, item_id, selected_use)]
            if kind == 'use':
                sources = index['reaching'].get(item_id, [])
                if not sources:
                    return None
                for definition_id in sources:
                    definition = index['definitions'][definition_id]
                    if definition.get('kind') == 'argument':
                        child = add_node('argument', definition.get('argument_index'), expand=False)
                    else:
                        child = add_node('definition', definition_id)
                    add_edge(node_id, child, 'one_of', 'reaching_definition')
                continue
            if kind == 'definition':
                definition = index['definitions'][item_id]
                defining_operation = definition.get('operation')
                if not defining_operation:
                    return None
                defining = index['operations'][defining_operation]
                if definition.get('role') == 'return_value' and defining['kind'] == 'call':
                    targets = []
                    for callee_id in call_targets(defining):
                        if callee_id in self.indexes:
                            targets.append(callee_id)
                    if targets:
                        callee_use = False
                        for use in defining.get('uses', []):
                            if use.get('role') == 'callee':
                                callee_use = use['id']
                                break
                        child = add_node('operation', defining_operation, callee_use)
                        add_edge(node_id, child, 'all_of', 'call')
                        relation = 'all_of'
                        if len(targets) > 1:
                            relation = 'one_of'
                        arguments = call_arguments(defining)
                    for callee_id in targets:
                        if component and callee_id in component:
                            callee_arguments = sorted(recursive_arguments[callee_id])
                        else:
                            callee = self.get(callee_id)
                            if callee is None:
                                return None
                            callee_arguments = []
                            for argument in self.argument_nodes(callee):
                                callee_arguments.append(argument['index'])
                        nested = add_node('nested_summary', defining_operation, callee_id, False)
                        add_edge(node_id, nested, relation, 'return_summary')
                        callees.add(callee_id)
                        for argument_index in callee_arguments:
                            if argument_index not in arguments:
                                return None
                            argument = arguments[argument_index]
                            if argument['kind'] == 'use':
                                child = add_node('use', argument['id'])
                            else:
                                constant_id = f'{defining_operation}:argument:{argument_index}'
                                child = add_node('constant', constant_id, expand=False, operand=argument['operand'])
                            add_edge(nested, child, 'all_of', 'summary_argument')
                            binding = {
                                'summary_node': self.argument_node_id(argument_index),
                                'index': argument_index,
                                'target': child,
                            }
                            if binding not in nodes[nested]['argument_bindings']:
                                nodes[nested]['argument_bindings'].append(binding)
                    if targets:
                        continue
                child = add_node('operation', defining_operation)
                add_edge(node_id, child, 'all_of', 'definition')
                continue
            operation = index['operations'][item_id]
            block_id = index['operation_blocks'][item_id]
            for dependency in index['dependencies'][block_id]:
                child = add_node('operation', dependency['operation'])
                add_edge(node_id, child, 'all_of', 'control')
            operation_uses = operation.get('uses', [])
            if selected_use is False:
                operation_uses = []
            elif selected_use is not None:
                operation_uses = [index['uses'][selected_use]]
            for use in operation_uses:
                child = add_node('use', use['id'])
                add_edge(node_id, child, 'all_of', 'data')
        return {
            'function': function_id,
            'root': root,
            'return_sites': return_sites,
            'nodes': list(nodes.values()),
            'edges': edges,
            'callees': sorted(callees),
        }

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
        self.summaries = FunctionSummaries(self.indexes)

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

    def add_summary(self, summary):
        identity = 'function_summary', summary['function']
        if identity in self.node_ids:
            return self.node_ids[identity]
        node_id = f'node-{len(self.node_ids) + 1}'
        self.node_ids[identity] = node_id
        self.nodes[node_id] = {
            'id': node_id,
            'kind': 'function_summary',
            'function': summary['function'],
            'root': summary['root'],
            'return_sites': summary['return_sites'],
            'nodes': summary['nodes'],
            'edges': summary['edges'],
        }
        for callee_id in summary['callees']:
            callee = self.summaries.get(callee_id)
            if callee is not None:
                self.add_summary(callee)
        return node_id

    def add_summary_instance(self, function_id, operation_id, callee_id, call_stack, call_context):
        identity = 'summary_instance', function_id, operation_id, callee_id, call_stack, call_context
        if identity in self.node_ids:
            return self.node_ids[identity]
        node_id = f'node-{len(self.node_ids) + 1}'
        self.node_ids[identity] = node_id
        self.nodes[node_id] = {
            'id': node_id,
            'kind': 'summary_instance',
            'function': function_id,
            'operation': operation_id,
            'callee': callee_id,
            'call_stack': self.stacks.name(call_stack),
            'call_context': self.contexts.name(call_context),
            'argument_bindings': [],
        }
        return node_id

    def add_constant(self, function_id, operation_id, argument_index, operand, call_stack, call_context):
        identity = 'constant', function_id, operation_id, argument_index, call_stack, call_context
        if identity in self.node_ids:
            return self.node_ids[identity]
        node_id = f'node-{len(self.node_ids) + 1}'
        self.node_ids[identity] = node_id
        self.nodes[node_id] = {
            'id': node_id,
            'kind': 'constant',
            'function': function_id,
            'operation': operation_id,
            'argument_index': argument_index,
            'operand': operand,
            'call_stack': self.stacks.name(call_stack),
            'call_context': self.contexts.name(call_context),
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
            targets = []
            for callee_id in call_targets(defining):
                if callee_id in self.indexes and self.indexes[callee_id]['returns']:
                    targets.append(callee_id)
            if targets:
                callee_use = False
                for use in defining.get('uses', []):
                    if use.get('role') == 'callee':
                        callee_use = use['id']
                        break
                child = self.add_node('operation', function_id, defining_operation, callee_use, call_stack, call_context)
                self.add_edge(node_id, child, 'all_of', 'call')
                summaries = []
                complete = True
                arguments = call_arguments(defining)
                for callee_id in targets:
                    summary = self.summaries.get(callee_id)
                    if summary is None:
                        complete = False
                        break
                    summary_arguments = self.summaries.argument_nodes(summary)
                    for argument in summary_arguments:
                        if argument['index'] not in arguments:
                            complete = False
                            break
                    if not complete:
                        break
                    summaries.append((callee_id, summary, summary_arguments))
                if complete:
                    relation = 'all_of'
                    if len(summaries) > 1:
                        relation = 'one_of'
                    for callee_id, summary, summary_arguments in summaries:
                        instance = self.add_summary_instance(function_id, defining_operation, callee_id, call_stack, call_context)
                        summary_node = self.add_summary(summary)
                        self.add_edge(node_id, instance, relation, 'return_summary')
                        self.add_edge(instance, summary_node, 'all_of', 'summary')
                        for argument in summary_arguments:
                            argument_index = argument['index']
                            caller_argument = arguments[argument_index]
                            if caller_argument['kind'] == 'use':
                                caller_use = caller_argument['id']
                                child = self.add_node('operation', function_id, defining_operation, caller_use, call_stack, call_context)
                            else:
                                child = self.add_constant(function_id, defining_operation, argument_index, caller_argument['operand'], call_stack, call_context)
                            self.add_edge(instance, child, 'all_of', 'summary_argument')
                            binding = {
                                'summary_node': argument['id'],
                                'index': argument_index,
                                'target': child,
                            }
                            if binding not in self.nodes[instance]['argument_bindings']:
                                self.nodes[instance]['argument_bindings'].append(binding)
                    return
                for callee_id in targets:
                    frame = function_id, defining_operation, callee_id
                    # TODO: Use fixed-point SCC summaries to preserve recursive dependencies instead of cutting them off
                    if self.contexts.contains(call_context, frame):
                        child = self.add_cutoff(call_context, frame)
                        self.add_edge(node_id, child, 'one_of', 'return_value')
                        continue
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
            caller_argument = call['arguments'].get(argument_index)
            if not caller_argument:
                continue
            context = next_context
            if not matched_stack:
                frame = call['function'], call['operation'], function_id
                if self.contexts.contains(call_context, frame):
                    component_id = self.summaries.component_by_function[function_id]
                    caller_component = self.summaries.component_by_function[call['function']]
                    if component_id == caller_component and component_id in self.summaries.components['recursive']:
                        context = self.contexts.find(call_context, frame)
                        if caller_argument['kind'] == 'use':
                            child = self.add_node('operation', call['function'], call['operation'], caller_argument['id'], next_stack, context)
                        else:
                            child = self.add_constant(call['function'], call['operation'], argument_index, caller_argument['operand'], next_stack, context)
                        self.add_edge(node_id, child, 'one_of', 'recursive_caller')
                    else:
                        child = self.add_cutoff(call_context, frame)
                        self.add_edge(node_id, child, 'one_of', 'caller')
                    mapped = True
                    continue
                context = self.contexts.extend(call_context, 'prepend', frame)
            if caller_argument['kind'] == 'use':
                child = self.add_node('operation', call['function'], call['operation'], caller_argument['id'], next_stack, context)
            else:
                child = self.add_constant(call['function'], call['operation'], argument_index, caller_argument['operand'], next_stack, context)
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
    assertions_with_unwind = set()
    for edge in function['edges']:
        if edge['kind'] == 'unwind':
            assertions_with_unwind.add(edge['source'])
    for block in function['blocks']:
        block_id = block['id']
        if block['terminator']['kind'] == 'assert' and block_id not in assertions_with_unwind:
            successors[block_id].append('__exit__')
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
                common &= postdominators[target]
            result = {block}
            result |= common
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

    # Examine every CFG edge controlled by a branch or assertion
    for edge in function['edges']:
        source = edge['source']
        target = edge['target']
        if target in postdominators[source]:
            continue
        terminator = blocks[source]['terminator']

        # A switch chooses one successor, while an assertion either continues or panics
        if terminator['kind'] in ['switch', 'assert']:
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
    #                 0: {'kind': 'use', 'id': 'caller_a:bb0:term:use0'},
    #             },
    #         },
    #         {
    #             'function': 'caller_b',
    #             'operation': 'caller_b:bb2:term',
    #             'arguments': {
    #                 0: {'kind': 'use', 'id': 'caller_b:bb2:term:use0'},
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

    resolve_indirect_calls(indexes)
    for function_id, index in indexes.items():
        for operation in index['operations'].values():
            if operation['kind'] != 'call':
                continue
            arguments = call_arguments(operation)
            for callee_id in call_targets(operation):
                if callee_id not in callers:
                    callers[callee_id] = []
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
