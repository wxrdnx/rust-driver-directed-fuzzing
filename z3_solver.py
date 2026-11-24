import argparse
import json

import z3

class Z3Translator:
    def __init__(self):
        self.variables = {}
        self.variable_types = {}
        self.constraints = []
        self.choice_index = 0
        self.error = None

    def translate(self, expression):
        kind = expression['kind']
        
        if kind == 'constant':
            return self.constant(expression)
        if kind == 'variable':
            return self.variable(expression)
        if kind in ['arithmetic', 'checked_result']:
            return self.arithmetic(expression)
        if kind == 'bitvector':
            return self.bitvector(expression)
        if kind == 'comparison':
            return self.comparison(expression)
        if kind == 'unary':
            return self.unary(expression)
        if kind == 'cast':
            return self.cast(expression)
        if kind == 'overflow':
            return self.overflow(expression)
        if kind == 'one_of':
            return self.one_of(expression)
        if kind == 'assertion':
            condition = self.translate(expression['condition'])
            if condition is None:
                return None
            return condition == z3.BoolVal(expression['required'])

        self.error = f'unsupported expression: {kind}'
        return None

    def constant(self, expression):
        value_type = expression['type']
        if value_type['kind'] == 'boolean':
            return z3.BoolVal(expression['value'])
        if value_type['kind'] == 'bitvector':
            return z3.BitVecVal(int(expression['value'], 0), value_type['bits'])

        var_type = value_type['kind']
        self.error = f'unsupported constant type: {var_type}'
        return None

    def variable(self, expression):
        name = expression['name']
        if name in self.variables:
            return self.variables[name]

        value_type = expression['type']

        if value_type['kind'] == 'boolean':
            variable = z3.Bool(name)
        elif value_type['kind'] == 'bitvector':
            variable = z3.BitVec(name, value_type['bits'])
        else:
            var_type = value_type['kind']
            self.error = f'unsupported variable type: {var_type}'
            return None

        self.variables[name] = variable
        self.variable_types[name] = value_type
        return variable

    def operands(self, expression):
        operands = []
        for operand in expression['operands']:
            translated = self.translate(operand)
            if translated is None:
                return None
            operands.append(translated)
        return operands

    def arithmetic(self, expression):
        operands = self.operands(expression)
        if operands is None:
            return None

        left, right = operands
        operation = expression['operation']
        
        if operation == 'add':
            return left + right
        if operation == 'subtract':
            return left - right
        if operation == 'multiply':
            return left * right
        if operation == 'signed_divide':
            return left / right
        if operation == 'unsigned_divide':
            return z3.UDiv(left, right)
        if operation == 'signed_remainder':
            return z3.SRem(left, right)
        if operation == 'unsigned_remainder':
            return z3.URem(left, right)
        
        self.error = f'unsupported arithmetic operation: {operation}'
        return None

    def bitvector(self, expression):
        operands = self.operands(expression)
        if operands is None:
            return None
        left, right = operands
        operation = expression['operation']
        
        if operation in ['shift_left', 'arithmetic_shift_right', 'logical_shift_right']:
            right = self.resize(right, left.size(), False)
        if operation == 'bit_and':
            return left & right
        if operation == 'bit_or':
            return left | right
        if operation == 'bit_xor':
            return left ^ right
        if operation == 'shift_left':
            return left << right
        if operation == 'arithmetic_shift_right':
            return left >> right
        if operation == 'logical_shift_right':
            return z3.LShR(left, right)
        
        self.error = f'unsupported bit-vector operation: {operation}'
        return None

    def comparison(self, expression):
        operands = self.operands(expression)
        if operands is None:
            return None
        
        left, right = operands
        operation = expression['operation']
        
        if operation == 'equal':
            return left == right
        
        if operation == 'not_equal':
            return left != right
        
        if expression['signed']:
            comparisons = {
                'less_than': left < right,
                'less_or_equal': left <= right,
                'greater_than': left > right,
                'greater_or_equal': left >= right,
            }
        else:
            comparisons = {
                'less_than': z3.ULT(left, right),
                'less_or_equal': z3.ULE(left, right),
                'greater_than': z3.UGT(left, right),
                'greater_or_equal': z3.UGE(left, right),
            }
        
        if operation in comparisons:
            return comparisons[operation]
        
        self.error = f'unsupported comparison: {operation}'
        return None

    def unary(self, expression):
        operand = self.translate(expression['operand'])
        if operand is None:
            return None
        operation = expression['operation']
        if operation == 'negate':
            return -operand
        if operation == 'logical_not':
            return z3.Not(operand)
        if operation == 'bit_not':
            return ~operand
        self.error = f'unsupported unary operation: {operation}'
        return None

    def cast(self, expression):
        operand = self.translate(expression['operand'])
        if operand is None:
            return None

        source_type = expression['source_type']
        target_type = expression['type']
        if source_type['kind'] != 'bitvector' or target_type['kind'] != 'bitvector':
            operation_expression = expression['operation']
            self.error = f'unsupported cast: {operation_expression}'
            return None

        return self.resize(operand, target_type['bits'], source_type['signed'])

    def resize(self, value, bits, signed):
        source_bits = value.size()
        if source_bits == bits:
            return value
        if source_bits > bits:
            return z3.Extract(bits - 1, 0, value)

        extension = bits - source_bits

        if signed:
            return z3.SignExt(extension, value)

        return z3.ZeroExt(extension, value)

    def overflow(self, expression):
        operands = self.operands(expression)
        if operands is None:
            return None

        left, right = operands
        bits = left.size()
        signed = expression['signed']
        if signed:
            wide_left = z3.SignExt(bits, left)
            wide_right = z3.SignExt(bits, right)
        else:
            wide_left = z3.ZeroExt(bits, left)
            wide_right = z3.ZeroExt(bits, right)

        # calculate the wide result and compare it with min/max possible values
        operation = expression['operation']
        if operation == 'add':
            wide_result = wide_left + wide_right
        elif operation == 'subtract':
            wide_result = wide_left - wide_right
        elif operation == 'multiply':
            wide_result = wide_left * wide_right
        else:
            self.error = f'unsupported overflow operation: {operation}'
            return None

        if signed:
            # for signed integers, the valid range is:
            # -2^(B - 1) ~ 2^(B - 1) - 1
            minimum = z3.BitVecVal(-(1 << (bits - 1)), bits * 2)
            maximum = z3.BitVecVal((1 << (bits - 1)) - 1, bits * 2)
            return z3.Or(wide_result < minimum, wide_result > maximum)

        maximum = z3.BitVecVal((1 << bits) - 1, bits * 2)
        return z3.UGT(wide_result, maximum)

    def one_of(self, expression):
        # Z3 does not have a corresponding "one-of" expression
        # So we stack up ORs
        # e.g., one_of(a, b) becomes choice == a or choice == b
        values = []
        for value in expression['values']:
            translated = self.translate(value)
            if translated is None:
                return None
            values.append(translated)

        value_type = expression['type']
        name = f'choice-{self.choice_index}'
        self.choice_index += 1

        if value_type['kind'] == 'boolean':
            choice = z3.Bool(name)
        elif value_type['kind'] == 'bitvector':
            choice = z3.BitVec(name, value_type['bits'])
        else:
            value_type = value_type['kind']
            self.error = f'unsupported choice type: {value_type}'
            return None

        alternatives = []
        for value in values:
            alternatives.append(choice == value)
        self.constraints.append(z3.Or(alternatives))

        return choice

def model_value(model, variable, value_type):
    value = model.eval(variable, model_completion=True)
    if value_type['kind'] == 'boolean':
        return {'value': z3.is_true(value), 'type': value_type}

    unsigned = value.as_long()
    result = {'value': str(unsigned), 'type': value_type}

    # Convert a signed bit vector's unsigned value into a negative decimal value
    if value_type['signed'] and unsigned >= 1 << (value_type['bits'] - 1):
        result['signed_value'] = str(unsigned - (1 << value_type['bits']))

    return result

def solve_constraint(constraint):
    if constraint['status'] != 'complete':
        return {'status': 'partial', 'assignments': {}}

    translator = Z3Translator()
    expression = translator.translate(constraint['expression'])
    if expression is None:
        return {'status': 'unsupported', 'reason': translator.error, 'assignments': {}}

    solver = z3.Solver()
    for side_constraint in translator.constraints:
        solver.add(side_constraint)
    solver.add(expression)

    status = solver.check()

    if status == z3.unsat:
        #print('unsat')
        return {'status': 'unsat', 'assignments': {}}

    if status == z3.unknown:
        #print('unknown')
        return {'status': 'unknown', 'reason': solver.reason_unknown(), 'assignments': {}}

    model = solver.model()
    assignments = {}
    for name, variable in translator.variables.items():
        assignments[name] = model_value(model, variable, translator.variable_types[name])

    return {'status': 'sat', 'assignments': assignments}

def solve_report(input_path, output_path):
    with open(input_path) as file:
        report = json.load(file)

    results = []
    counts = {}
    for record in report['targets']:
        solved = solve_constraint(record['constraint'])
        status = solved['status']
        counts[status] = counts.get(status, 0) + 1
        results.append({'target': record['target'], 'result': solved})
    output = {
        'schema_version': 1,
        'target_count': report['target_count'],
        'condition_count': report['condition_count'],
        'status_counts': counts,
        'targets': results,
    }

    with open(output_path, 'w') as file:
        json.dump(output, file, indent=2)
        file.write('\n')

    return True

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('constraints')
    parser.add_argument('output')
    args = parser.parse_args()
    solve_report(args.constraints, args.output)
