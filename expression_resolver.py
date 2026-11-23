import json

BINARY_OPERATIONS = {
    'add',
    'addunchecked',
    'bitand',
    'bitor',
    'bitxor',
    'cmp',
    'div',
    'eq',
    'ge',
    'gt',
    'le',
    'lt',
    'mul',
    'mulunchecked',
    'ne',
    'offset',
    'rem',
    'shl',
    'shlunchecked',
    'shr',
    'shrunchecked',
    'sub',
    'subunchecked',
}

UNARY_OPERATIONS = {
    'neg',
    'not',
}

CHECKED_BINARY_OPERATIONS = {
    'addwithoverflow',
    'mulwithoverflow',
    'subwithoverflow',
}

# Preserve numeric casts, pointer casts, and bit-level transmutations
CAST_OPERATIONS = {
    'IntToInt',
    'PtrToPtr',
    'Transmute',
}

class ExpressionResolver:
    def __init__(self, indexes):
        self.indexes = indexes
        self.cache = {}
        self.visiting = set()
        self.argument_bindings = {}

    def result(self, function_id, use_id):
        expression = self.resolve_use(function_id, use_id)
        unsupported = set()
        self.collect_unsupported(expression, unsupported)
        return {
            'status': expression['status'],
            'expression': expression,
            'unsupported_operations': sorted(unsupported),
        }

    def resolve_use(self, function_id, use_id, context=()):
        key = function_id, use_id, context
        if key in self.cache:
            return self.cache[key]
        if key in self.visiting:
            return {'kind': 'opaque', 'operation': None, 'reason': 'cycle', 'inputs': [], 'status': 'partial'}

        self.visiting.add(key)

        # Determine what expressions may produce the value at use_id
        index = self.indexes[function_id]
        use = index['uses'][use_id]
        values = []
        for definition_id in index['reaching'].get(use_id, []):
            # Resolve the expression that produced this definition
            value = self.resolve_definition(function_id, definition_id, context)
            # Select the part of the defined value read by this use
            # For example, if the definition is (result, overflow) and the use reads .1, select overflow
            value = self.apply_projection(value, index['definitions'][definition_id], use)

            values.append(value)

        if not values:
            expression = {
                'kind': 'opaque',
                'operation': None,
                'reason': 'no_reaching_definition',
                'inputs': [],
                'status': 'partial',
            }
        else:
            unique_values = []
            seen = set()
            for value in values:
                identity = json.dumps(value, sort_keys=True, separators=(',', ':'))
                if identity not in seen:
                    seen.add(identity)
                    unique_values.append(value)
            values = unique_values
            if len(values) == 1:
                expression = values[0]
            else:
                expression = {'kind': 'one_of', 'values': values, 'status': self.combined_status(values)}

        self.visiting.remove(key)
        self.cache[key] = expression

        return expression

    def resolve_definition(self, function_id, definition_id, context):
        index = self.indexes[function_id]
        definition = index['definitions'][definition_id]
        if definition.get('kind') == 'argument':
            binding = self.argument_bindings.get((context, function_id, definition.get('argument_index')))
            if binding is not None:
                return binding
            return {
                'kind': 'argument',
                'function': function_id,
                'index': definition.get('argument_index'),
                'place': definition['place'],
                'status': 'complete',
            }

        operation_id = definition.get('operation')
        if not operation_id:
            return {
                'kind': 'opaque',
                'operation': None,
                'reason': 'missing_defining_operation',
                'inputs': [],
                'status': 'partial',
            }

        operation = index['operations'][operation_id]
        if operation['kind'] == 'call':
            return self.resolve_call(function_id, operation, context)
        # Only assignments with "structured expressions" can be resolved into values
        # Otherwise, treat the assignment as "opaque"
        if operation['kind'] != 'assignment' or 'expression' not in operation:
            return self.opaque_operation(function_id, operation, 'unsupported_definition', context)
        return self.resolve_expression(function_id, operation, context)

    def resolve_call(self, function_id, operation, context):
        data = operation.get('data') or {}
        callee_ids = data.get('callee_ids')
        if callee_ids is None and data.get('callee_id') is not None:
            callee_ids = [data['callee_id']]
        if not callee_ids:
            return self.opaque_operation(function_id, operation, 'unresolved_call', context)
        arguments = {}
        for index, operand in enumerate(data.get('arguments', [])):
            arguments[index] = self.resolve_operand(function_id, operation, operand, f'argument_{index}', context)
        values = []
        for callee_id in callee_ids:
            if callee_id not in self.indexes:
                values.append({
                    'kind': 'opaque',
                    'operation': operation['id'],
                    'operation_kind': 'call',
                    'reason': 'unavailable_callee',
                    'callee_id': callee_id,
                    'inputs': list(arguments.values()),
                    'status': 'partial',
                })
                continue
            if not self.indexes[callee_id]['returns']:
                values.append({
                    'kind': 'opaque',
                    'operation': operation['id'],
                    'operation_kind': 'call',
                    'reason': 'missing_callee_return',
                    'callee_id': callee_id,
                    'inputs': list(arguments.values()),
                    'status': 'partial',
                })
                continue
            recursive = callee_id == function_id
            for caller, _, callee in context:
                if callee_id == caller or callee_id == callee:
                    recursive = True
                    break
            if recursive:
                values.append({
                    'kind': 'opaque',
                    'operation': operation['id'],
                    'operation_kind': 'call',
                    'reason': 'recursive_call',
                    'inputs': list(arguments.values()),
                    'status': 'partial',
                })
                continue
            frame = function_id, operation['id'], callee_id
            callee_context = context + (frame,)
            for index, argument in arguments.items():
                self.argument_bindings[(callee_context, callee_id, index)] = argument
            for _, use_id in self.indexes[callee_id]['returns']:
                values.append(self.resolve_use(callee_id, use_id, callee_context))
        if not values:
            return self.opaque_operation(function_id, operation, 'unresolved_call_return', context)
        unique_values = []
        seen = set()
        for value in values:
            identity = json.dumps(value, sort_keys=True, separators=(',', ':'))
            if identity not in seen:
                seen.add(identity)
                unique_values.append(value)
        if len(unique_values) == 1:
            return unique_values[0]
        return {'kind': 'one_of', 'values': unique_values, 'status': self.combined_status(unique_values)}

    def resolve_expression(self, function_id, operation, context):
        expression = operation['expression']
        kind = expression.get('kind')

        if kind == 'use':
            return self.resolve_operand(function_id, operation, expression['operand'], 'operand', context)

        # Binary operations
        if kind in ['binary', 'checked_binary']:
            supported_operations = BINARY_OPERATIONS if kind == 'binary' else CHECKED_BINARY_OPERATIONS
            if expression.get('operation') not in supported_operations:
                return self.opaque_operation(function_id, operation, 'unsupported_binary_operation', context)

            left = self.resolve_operand(function_id, operation, expression['operands'][0], 'left_operand', context)
            right = self.resolve_operand(function_id, operation, expression['operands'][1], 'right_operand', context)
            operands = [left, right]
            return {
                'kind': kind,
                'operation': expression['operation'],
                'operands': operands,
                'result_projection': expression.get('result_projection'),
                'overflow_projection': expression.get('overflow_projection'),
                'status': self.combined_status(operands),
            }

        # Unary Operations
        if kind == 'unary':
            if expression.get('operation') not in UNARY_OPERATIONS:
                return self.opaque_operation(function_id, operation, 'unsupported_unary_operation', context)
            operand = self.resolve_operand(function_id, operation, expression['operand'], 'operand', context)
            return {
                'kind': 'unary',
                'operation': expression['operation'],
                'operand': operand,
                'status': operand['status'],
            }

        # Type Casting
        # Only integer to integer casting is supported
        if kind == 'cast':
            if expression.get('cast_kind') not in CAST_OPERATIONS:
                return self.opaque_operation(function_id, operation, 'unsupported_cast', context)
            operand = self.resolve_operand(function_id, operation, expression['operand'], 'operand', context)
            source_type = expression['operand'].get('type')
            if source_type is None and 'place' in expression['operand']:
                source_type = expression['operand']['place']['type']
            return {
                'kind': 'cast',
                'cast_kind': expression['cast_kind'],
                'source_type': source_type,
                'type': expression['type'],
                'operand': operand,
                'status': operand['status'],
            }

        if kind == 'reference':
            referent = None
            for use in operation.get('uses', []):
                if use.get('role') == 'place':
                    referent = self.resolve_use(function_id, use['id'], context)
                    break
            if referent is None:
                referent = {
                    'kind': 'opaque',
                    'operation': operation['id'],
                    'reason': 'missing_reference_place',
                    'inputs': [],
                    'status': 'partial',
                }
            return {
                'kind': 'reference',
                'borrow_kind': expression['borrow_kind'],
                'place': expression['place'],
                'referent': referent,
                'status': referent['status'],
            }

        if kind == 'raw_pointer':
            referent = None
            for use in operation.get('uses', []):
                if use.get('role') == 'place':
                    referent = self.resolve_use(function_id, use['id'], context)
                    break
            if referent is None:
                referent = {
                    'kind': 'opaque',
                    'operation': operation['id'],
                    'reason': 'missing_pointer_place',
                    'inputs': [],
                    'status': 'partial',
                }
            return {
                'kind': 'raw_pointer',
                'mutability': expression['mutability'],
                'place': expression['place'],
                'referent': referent,
                'status': referent['status'],
            }

        if kind == 'aggregate':
            operands = []
            for index, operand in enumerate(expression['operands']):
                operands.append(self.resolve_operand(function_id, operation, operand, f'field_{index}', context))
            return {
                'kind': 'aggregate',
                'aggregate_kind': expression['aggregate_kind'],
                'operands': operands,
                'status': self.combined_status(operands),
            }

        # All other operations are treated as "opqaue"
        return self.opaque_operation(function_id, operation, 'unsupported_rvalue', context)

    def resolve_operand(self, function_id, operation, operand, role, context):
        # constant: which are, you know, constants
        if operand['kind'] == 'constant':
            value = {
                'kind': 'constant',
                'type': operand['type'],
                'value': operand['value'],
                'status': 'complete',
            }
            if operand.get('function_id'):
                value['function_id'] = operand['function_id']
            return value

        # runtime_checks: treated as opaque
        if operand['kind'] == 'runtime_checks':
            return {
                'kind': 'opaque',
                'operation': operation['id'],
                'reason': 'unsupported_operand',
                'inputs': [],
                'status': 'partial',
            }

        # move and copy: follow the use to obtain the read value
        for use in operation.get('uses', []):
            if use.get('role') == role:
                return self.resolve_use(function_id, use['id'], context)

        # Reach here when no use has the corresponding role
        # This shouldn't happen assuming that the analyzer output is complete
        # Keep the operand opaque if this happens
        return {
            'kind': 'opaque',
            'operation': operation['id'],
            'reason': 'missing_operand_use',
            'inputs': [],
            'status': 'partial',
        }

    def apply_projection(self, expression, definition, use):

        # Take the full use and only "project" the subpart read by a use
        # e.g.
        #     let checked = a.overflowing_add(b);
        #     let overflow = checked.1;
        # Here the use reads only checked.1, so it will return
        # the overflow part instead of the full checked value

        defined_place = definition['place']
        used_place = use['place']

        # Check that the definition and use refer to the same local variable
        # e.g.
        # definition: _3
        # use: _3.1
        # The _3 must match
        if defined_place['local'] != used_place['local']:
            return {
                'kind': 'opaque',
                'operation': definition.get('operation'),
                'reason': 'incompatible_places',
                'inputs': [expression],
                'status': 'partial',
            }

        # Check that the definition is a prefix of the use
        # e.g.
        # definition: _3.0
        # use: _3.0.1
        # The definition's .0 must match the start of the use's .0.1
        defined = defined_place['projections']
        used = used_place['projections']
        if used[:len(defined)] != defined:
            return {
                'kind': 'opaque',
                'operation': definition.get('operation'),
                'reason': 'partial_place_update',
                'inputs': [expression],
                'status': 'partial',
            }

        # Remove the projections already included in the definition
        # e.g.
        # definition: _3.0
        # use: _3.0.1
        # The remaining projection is .1
        projections = used[len(defined):]

        # Return the original expression if the use does not select a smaller part
        if not projections:
            return expression

        # Select the result or overflow field from checked arithmetic
        # e.g.
        # expression: (result, overflow)
        # use: expression.1
        # The selected value is overflow
        first = projections[0]
        if expression['kind'] == 'checked_binary' and first.get('kind') == 'field':
            if first.get('index') == expression['result_projection']:
                value = {
                    'kind': 'checked_result',
                    'operation': expression['operation'],
                    'operands': expression['operands'],
                    'status': expression['status'],
                }
                projections = projections[1:]

            elif first.get('index') == expression['overflow_projection']:
                value = {
                    'kind': 'overflow',
                    'operation': expression['operation'],
                    'operands': expression['operands'],
                    'status': expression['status'],
                }
                projections = projections[1:]

            else:
                value = expression
        elif expression['kind'] == 'aggregate' and first.get('kind') == 'field':
            index = first.get('index')
            if index is not None and index < len(expression['operands']):
                value = expression['operands'][index]
                projections = projections[1:]
            else:
                value = expression
        else:
            value = expression
        if not projections:
            return value

        # Preserve all remaining data (as a general projection)
        return {
            'kind': 'projection',
            'base': value,
            'projections': projections,
            'status': value['status'],
        }

    def opaque_operation(self, function_id, operation, reason, context):
        inputs = []
        for use in operation.get('uses', []):
            inputs.append(self.resolve_use(function_id, use['id'], context))
        value = {
            'kind': 'opaque',
            'operation': operation['id'],
            'operation_kind': operation['kind'],
            'reason': reason,
            'inputs': inputs,
            'status': 'partial',
        }
        if 'expression' in operation:
            value['original'] = operation['expression']
        return value

    def combined_status(self, values):
        # complete + complete -> complete
        # complete + partial -> partial
        # partial + partial -> partial
        for value in values:
            if value['status'] != 'complete':
                return 'partial'
        return 'complete'

    def collect_unsupported(self, expression, unsupported):
        # Get IDs that become opaque
        if expression['kind'] == 'opaque' and expression['operation']:
            unsupported.add(expression['operation'])
        for key in ['base', 'operand', 'referent']:
            if key in expression:
                self.collect_unsupported(expression[key], unsupported)
        for key in ['inputs', 'operands', 'values']:
            for value in expression.get(key, []):
                self.collect_unsupported(value, unsupported)

def opaque_expressions(expression):
    opaque = []
    if expression['kind'] == 'opaque':
        opaque.append(expression)
    for key in ['base', 'operand', 'referent']:
        if key in expression:
            opaque += opaque_expressions(expression[key])
    for key in ['inputs', 'operands', 'values']:
        for value in expression.get(key, []):
            opaque += opaque_expressions(value)

    return opaque

def expression_impact_report(indexes, targets):
    resolver = ExpressionResolver(indexes)
    status_counts = {'complete': 0, 'partial': 0}
    skipped = []
    reasons = {}
    kinds = {}
    operations = {}
    for target in targets:
        # Find the target assertion condition
        use_id = None
        function_id = target['function_id']
        if function_id in indexes and 'mir_location' in target:
            block = target['mir_location']['basic_block']
            operation_id = f'{function_id}:bb{block}:term'
            operation = indexes[function_id]['operations'].get(operation_id)
            if operation:
                for use in operation.get('uses', []):
                    if use.get('role') == 'condition':
                        use_id = use['id']
                        break
        # Skip if there is no condition use
        if not use_id:
            skipped.append(target['id'])
            continue

        # Resolve the condition and count conditional / partial expressions
        result = resolver.result(target['function_id'], use_id)
        status_counts[result['status']] += 1

        # Find opaque expressions and record reasons kinds and oeprations
        for expression in opaque_expressions(result['expression']):
            reason = expression['reason']
            original = expression.get('original') or {}
            if reason == 'unsupported_cast':
                detail = original.get('cast_kind')
            elif reason in ['unsupported_binary_operation', 'unsupported_unary_operation']:
                detail = original.get('operation')
            elif reason in ['unsupported_definition', 'unresolved_call', 'unresolved_call_return',
                            'unavailable_callee', 'missing_callee_return', 'recursive_call']:
                detail = expression.get('operation_kind')
            else:
                detail = original.get('kind')

            # Count unsupported reason appears and what target it affects
            if reason not in reasons:
                reasons[reason] = {'occurrence_count': 0, 'operations': set(), 'targets': set()}
            reasons[reason]['occurrence_count'] += 1
            reasons[reason]['targets'].add(target['id'])

            kind = reason, detail
            if kind not in kinds:
                kinds[kind] = {'reason': reason, 'detail': detail, 'occurrence_count': 0, 'operations': set(), 'targets': set()}
            kinds[kind]['occurrence_count'] += 1
            kinds[kind]['targets'].add(target['id'])
            
            # Some opaque expressions have an operation ID
            # This happens when there's an actual MIR operation but we don't know how to model it
            # e.g.,
            #     let pointer = value as *const Data;
            # is PtrToPtr, which is unsupported
            # Count the operation ID here
            operation_id = expression.get('operation')
            if operation_id:
                reasons[reason]['operations'].add(operation_id)
                kinds[kind]['operations'].add(operation_id)
                key = operation_id, reason
                if key not in operations:
                    operations[key] = {
                        'operation': operation_id,
                        'reason': reason,
                        'detail': detail,
                        'occurrence_count': 0,
                        'targets': set(),
                    }
                operations[key]['occurrence_count'] += 1
                operations[key]['targets'].add(target['id'])

    reason_records = []
    for reason, record in reasons.items():
        reason_records.append({
            'reason': reason,
            'target_count': len(record['targets']),
            'operation_count': len(record['operations']),
            'occurrence_count': record['occurrence_count'],
            'targets': sorted(record['targets']),
        })
    reason_records.sort(key=lambda record: (-record['target_count'], record['reason']))

    # Summaries grouped by features
    kind_records = []
    for record in kinds.values():
        record['target_count'] = len(record['targets'])
        record['operation_count'] = len(record['operations'])
        record['targets'] = sorted(record['targets'])
        del record['operations']
        kind_records.append(record)
    kind_records.sort(key=lambda record: (-record['target_count'], record['reason'], record['detail'] or ''))

    # Summaries grouped by operations
    operation_records = []
    for record in operations.values():
        record['target_count'] = len(record['targets'])
        record['targets'] = sorted(record['targets'])
        operation_records.append(record)
    operation_records.sort(key=lambda record: (-record['target_count'], -record['occurrence_count'], record['operation']))
    analyzed = status_counts['complete'] + status_counts['partial']

    return {
        'target_count': len(targets),
        'condition_target_count': analyzed,
        'skipped_target_count': len(skipped),
        'skipped_targets': skipped,
        'status_counts': status_counts,
        'unsupported_by_reason': reason_records,
        'unsupported_by_kind': kind_records,
        'unsupported_operations': operation_records,
    }

