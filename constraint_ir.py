# MIR arithmetic operations
ARITHMETIC_OPERATIONS = {
    'add': 'add',
    'addunchecked': 'add',
    'div': 'signed_divide',
    'mul': 'multiply',
    'mulunchecked': 'multiply',
    'rem': 'signed_remainder',
    'sub': 'subtract',
    'subunchecked': 'subtract',
}

# MIR bitwise operations
BIT_OPERATIONS = {
    'bitand': 'bit_and',
    'bitor': 'bit_or',
    'bitxor': 'bit_xor',
    'shl': 'shift_left',
    'shlunchecked': 'shift_left',
    'shr': 'shift_right',
    'shrunchecked': 'shift_right',
    'rotate_left': 'rotate_left',
    'rotate_right': 'rotate_right',
}

# MIR comparison operations
COMPARISON_OPERATIONS = {
    'eq': 'equal',
    'ge': 'greater_or_equal',
    'gt': 'greater_than',
    'le': 'less_or_equal',
    'lt': 'less_than',
    'ne': 'not_equal',
}

# MIR arithmetic operation (where overflow is being tested)
OVERFLOW_OPERATIONS = {
    'addwithoverflow': 'add',
    'mulwithoverflow': 'multiply',
    'subwithoverflow': 'subtract',
}

class ConstraintBuilder:
    def __init__(self):
        self.unsupported = []

    def result(self, resolved):
        self.unsupported = []
        expression = resolved.get('expression', resolved)
        constraint = self.convert(expression)

        status = 'complete'
        if self.unsupported:
            status = 'partial'

        return {
            'version': 1,
            'status': status,
            'expression': constraint,
            'unsupported': self.unsupported,
        }

    def assertion(self, resolved, expected, outcome='failure'):
        result = self.result(resolved)
        condition = result['expression']
        required = expected
        if outcome == 'failure':
            required = not expected

        assertion = {
            'kind': 'assertion',
            'outcome': outcome,
            'expected': expected,
            'required': required,
            'condition': condition,
            'type': {'kind': 'boolean'},
        }
        result['expression'] = assertion

        return result

    def branch(self, resolved, value):
        result = self.result(resolved)
        condition = result['expression']
        expected = self.branch_constant(value, condition['type'])

        result['expression'] = {
            'kind': 'comparison',
            'operation': 'equal',
            'operands': [condition, expected],
            'type': {'kind': 'boolean'},
        }

        return result

    def convert(self, expression):
        kind = expression['kind']

        # Function argument -> symbolic variable
        if kind == 'argument':
            function_expression = expression['function']
            index_expression = expression['index']
            result_type = expression['place']['type']
            type_expression = self.value_type(result_type)

            return {
                'kind': 'variable',
                'name': f'{function_expression}:argument:{index_expression}',
                'source': 'function_argument',
                'function': function_expression,
                'index': index_expression,
                'type': type_expression,
            }

        # Preserve constants
        if kind == 'constant':
            value = expression['value']
            if not isinstance(value, dict):
                return self.unknown(expression, 'unstructured_constant')
            return self.constant(value, expression['type'])

        # References and raw pointers are represented by their addresses
        if kind in ['reference', 'raw_pointer']:
            pointer_type = expression['place']['type']
            return {
                'kind': 'pointer',
                'name': expression['operation'],
                'type': self.value_type(pointer_type),
            }

        if kind == 'intrinsic':
            arguments = []
            for argument in expression['arguments']:
                arguments.append(self.convert(argument))
            return {
                'kind': 'intrinsic',
                'name': expression['name'],
                'arguments': arguments,
                'type': self.value_type(expression['type']),
            }

        if kind == 'opaque':
            return self.unknown(expression, expression['reason'])

        # Normalize unary operations
        if kind == 'unary':
            operand = self.convert(expression['operand'])
            operation = expression['operation']
            if operation == 'neg':
                return {'kind': 'unary', 'operation': 'negate', 'operand': operand, 'type': operand['type']}
            if operation == 'not':
                operand_type = operand['type'] or {}
                operation = 'logical_not' if operand_type.get('kind') == 'boolean' else 'bit_not'
                return {'kind': 'unary', 'operation': operation, 'operand': operand, 'type': operand['type']}

        # Normalize binary operations
        if kind == 'binary':
            return self.binary(expression)

        # Numeric result from checked arithmetics
        if kind == 'checked_result':
            operation = OVERFLOW_OPERATIONS[expression['operation']]
            return self.operation(expression, operation, 'checked_result')

        # Overflow bit
        if kind == 'overflow':
            operation = OVERFLOW_OPERATIONS[expression['operation']]
            value = self.operation(expression, operation, 'overflow')
            value['type'] = {'kind': 'boolean'}
            return value

        # Convert the operand (type casting)
        # But at the same time preserver source & destination types
        if kind == 'cast':
            operand = self.convert(expression['operand'])
            return {
                'kind': 'cast',
                'operation': expression['cast_kind'],
                'operand': operand,
                'source_type': self.value_type(expression['source_type']),
                'type': self.value_type(expression['type']),
            }

        # Keep values that might reach the same use
        if kind == 'one_of':
            values = []
            for value in expression['values']:
                values.append(self.convert(value))
            return {'kind': 'one_of', 'values': values, 'type': self.common_type(values)}

        # Keep a field path as one symbolic value
        if kind == 'projection':
            identity = self.projection_identity(expression)
            result_type = self.projection_type(expression)
            if identity is None or result_type is None:
                return self.unknown(expression, 'unsupported_projection')
            root, projections, _ = identity
            path = []
            for projection in projections:
                if projection['kind'] == 'field':
                    path.append({'kind': 'field', 'index': projection['index']})
                elif projection['kind'] == 'deref':
                    path.append({'kind': 'deref'})
                else:
                    return self.unknown(expression, 'unsupported_projection')
            name = root
            for projection in path:
                if projection['kind'] == 'field':
                    name += f".field-{projection['index']}"
                else:
                    name += '.deref'
            return {
                'kind': 'projection',
                'name': name,
                'root': root,
                'projections': path,
                'type': self.value_type(result_type),
            }

        # Unsupported expressions
        return self.unknown(expression, 'unsupported_expression')

    def projection_identity(self, expression):
        kind = expression['kind']
        if kind == 'argument':
            root = f"{expression['function']}:argument:{expression['index']}"
            value_kind = expression['place']['type']['kind']
            return root, [], value_kind in ['reference', 'raw_pointer']
        if kind == 'projection':
            identity = self.projection_identity(expression['base'])
            if identity is None:
                return None
            root, path, pointer = identity
            projections = list(expression['projections'])
            if pointer and projections and projections[0]['kind'] == 'deref':
                projections = projections[1:]
            path += projections
            return root, path, False
        if kind in ['reference', 'raw_pointer']:
            identity = self.projection_identity(expression['referent'])
            if identity is None:
                return None
            root, path, _ = identity
            return root, path, True
        if kind == 'cast':
            identity = self.projection_identity(expression['operand'])
            if identity is None:
                return None
            root, path, _ = identity
            target_kind = expression['type']['kind']
            return root, path, target_kind in ['reference', 'raw_pointer']
        return None

    def projection_type(self, expression):
        for projection in reversed(expression['projections']):
            if 'type' in projection:
                return projection['type']
        base = expression['base']
        kind = base['kind']
        if kind == 'projection':
            return self.projection_type(base)
        if kind in ['argument', 'reference', 'raw_pointer']:
            return base['place']['type']
        if kind == 'cast':
            return base['type']
        return None

    def binary(self, expression):
        operation = expression['operation']
        operands = []

        for operand in expression['operands']:
            operands.append(self.convert(operand))

        if operation in COMPARISON_OPERATIONS:
            return {
                'kind': 'comparison',
                'operation': COMPARISON_OPERATIONS[operation],
                'operands': operands,
                'signed': self.is_signed(operands),
                'type': {'kind': 'boolean'},
            }

        if operation == 'offset':
            pointer_type = operands[0]['type']
            element_size = self.pointee_size(pointer_type['pointee'])
            if element_size is None:
                unsupported = {'reason': 'unknown_pointee_size', 'pointee': pointer_type['pointee']}
                if unsupported not in self.unsupported:
                    self.unsupported.append(unsupported)
            return {
                'kind': 'pointer_offset',
                'base': operands[0],
                'index': operands[1],
                'element_size': element_size,
                'type': pointer_type,
            }

        if operation in ARITHMETIC_OPERATIONS:
            normalized = ARITHMETIC_OPERATIONS[operation]
            # Division and remainder behave differently in signed & unsigned integers
            # So we handle them differently
            if (operation == 'div' or operation ==  'rem') and not self.is_signed(operands):
                normalized = 'unsigned_divide' if operation == 'div' else 'unsigned_remainder'

            return {
                'kind': 'arithmetic',
                'operation': normalized,
                'operands': operands,
                'type': self.common_type(operands),
            }

        if operation in BIT_OPERATIONS:
            normalized = BIT_OPERATIONS[operation]
            # Determine if the right shift is logical or arithmetic based on the signedness
            if operation == 'shr' or operation == 'shrunchecked':
                normalized = 'arithmetic_shift_right' if self.is_signed(operands) else 'logical_shift_right'

            return {
                'kind': 'bitvector',
                'operation': normalized,
                'operands': operands,
                'type': self.common_type(operands),
            }

        # Unsupported binary operations
        return self.unknown(expression, 'unsupported_binary_operation')

    def operation(self, expression, operation, kind):
        operands = []
        for operand in expression['operands']:
            operands.append(self.convert(operand))

        return {
            'kind': kind,
            'operation': operation,
            'operands': operands,
            'signed': self.is_signed(operands),
            'type': self.common_type(operands),
        }

    def constant(self, value, source_type):
        kind = value['kind']
        if kind == 'boolean':
            return {'kind': 'constant', 'value': value['value'], 'type': {'kind': 'boolean'}}
        if kind == 'integer':
            value_type = {
                'kind': 'bitvector',
                'bits': value['bits'],
                'signed': value['signed'],
            }
            return {'kind': 'constant', 'value': value['value'], 'type': value_type}
        if kind == 'pointer':
            return {'kind': 'constant', 'value': value['value'], 'type': self.value_type(source_type)}
        return self.unknown({'kind': 'constant', 'value': value}, 'opaque_constant')

    def branch_constant(self, value, value_type):
        if value_type is None:
            if isinstance(value, bool):
                value_type = {'kind': 'boolean'}
            else:
                value_type = {'kind': 'untyped_integer'}

        if value_type['kind'] == 'boolean' and isinstance(value, str):
            value = value.lower() == 'true'

        return {'kind': 'constant', 'value': value, 'type': value_type}

    def value_type(self, value):
        if value is None:
            return None

        kind = value['kind']
        if kind == 'boolean':
            return {'kind': 'boolean'}

        if kind == 'integer':
            return {
                'kind': 'bitvector',
                'bits': value['bits'],
                'signed': value['signed'],
            }

        if kind in ['raw_pointer', 'reference']:
            return {
                'kind': 'pointer',
                'bits': value.get('bits', 64),
                'mutable': value['mutable'],
                'pointee': value['pointee'],
                'non_null': value.get('non_null', kind == 'reference'),
            }

        unsupported = {'reason': 'unsupported_type', 'type_kind': kind}
        if unsupported not in self.unsupported:
            self.unsupported.append(unsupported)
        return {'kind': 'unsupported', 'source': value}

    def pointee_size(self, pointee):
        sizes = {
            'bool': 1,
            'i8': 1,
            'u8': 1,
            'i16': 2,
            'u16': 2,
            'i32': 4,
            'u32': 4,
            'i64': 8,
            'u64': 8,
            'isize': 8,
            'usize': 8,
        }
        return sizes.get(pointee)

    def common_type(self, values):
        for value in values:
            if value['type'] is not None:
                return value['type']
        return None

    def is_signed(self, values):
        value_type = self.common_type(values) or {}
        return value_type.get('signed', False)

    def unknown(self, expression, reason):
        record = {'reason': reason, 'expression_kind': expression['kind']}
        operation = expression.get('operation')
        if operation is not None:
            record['operation'] = operation
        for key in ['intrinsic', 'intrinsic_family']:
            if key in expression:
                record[key] = expression[key]
        if record not in self.unsupported:
            self.unsupported.append(record)

        value = {'kind': 'unknown', 'reason': reason, 'source_kind': expression['kind'], 'type': None}
        if operation is not None:
            value['operation'] = operation
        for key in ['intrinsic', 'intrinsic_family']:
            if key in expression:
                value[key] = expression[key]

        return value
