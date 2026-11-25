BINARY_INTRINSICS = {
    'wrapping_add': 'add',
    'wrapping_sub': 'sub',
    'wrapping_mul': 'mul',
    'rotate_left': 'rotate_left',
    'rotate_right': 'rotate_right',
}

CHECKED_INTRINSICS = {
    'add_with_overflow': 'addwithoverflow',
    'sub_with_overflow': 'subwithoverflow',
    'mul_with_overflow': 'mulwithoverflow',
}

INTEGER_INTRINSICS = {
    'bitreverse',
    'bswap',
    'ctlz',
    'ctlz_nonzero',
    'ctpop',
    'cttz',
    'cttz_nonzero',
    'saturating_add',
    'saturating_sub',
}

PASSTHROUGH_INTRINSICS = {'black_box', 'likely', 'rustc_peek', 'unlikely'}

def intrinsic_family(name):
    if name.startswith('atomic_'):
        return 'atomic'

    if name.startswith('simd_') or name.startswith('sve_'):
        return 'simd'

    if name.startswith('volatile_') or name.startswith('unaligned_volatile_'):
        return 'memory'

    if name in ['copy', 'copy_nonoverlapping', 'write_bytes', 'read_via_copy', 'write_via_move']:
        return 'memory'

    if name.startswith('ptr_') or name in ['aggregate_raw_ptr', 'ptr_offset_from', 'ptr_offset_from_unsigned']:
        return 'pointer'

    if name.startswith('f') or name.startswith('sqrt') or name.startswith('sin') or name.startswith('cos'):
        return 'floating_point'
    
    if name.startswith('exp') or name.startswith('log') or name.startswith('pow'):
        return 'floating_point'

    if name in BINARY_INTRINSICS or name in CHECKED_INTRINSICS or name in INTEGER_INTRINSICS:
        return 'integer'

    if name in PASSTHROUGH_INTRINSICS or name in ['select_unpredictable', 'assume', 'abort', 'breakpoint']:
        return 'control'


    if name.startswith('size_of') or name.startswith('align_of') or name.startswith('type_'):
        return 'type_layout'

    if name in ['needs_drop', 'variant_count', 'discriminant_value', 'vtable_size', 'vtable_align']:
        return 'type_layout'

    return 'other'

class IntrinsicResolver:
    def resolve(self, name, arguments, result_type, operation):
        values = []
        for index in range(len(arguments)):
            values.append(arguments[index])

        status = self.combined_status(values)

        if name in PASSTHROUGH_INTRINSICS:
            return values[0]

        if name == 'select_unpredictable':
            return {
                'kind': 'intrinsic',
                'name': name,
                'arguments': values,
                'type': result_type,
                'status': status,
            }

        if name in BINARY_INTRINSICS:
            return {
                'kind': 'binary',
                'operation': BINARY_INTRINSICS[name],
                'operands': values,
                'result_projection': None,
                'overflow_projection': None,
                'status': status,
            }

        if name in CHECKED_INTRINSICS:
            return {
                'kind': 'checked_binary',
                'operation': CHECKED_INTRINSICS[name],
                'operands': values,
                'result_projection': 0,
                'overflow_projection': 1,
                'status': status,
            }

        if name in INTEGER_INTRINSICS:
            return {
                'kind': 'intrinsic',
                'name': name,
                'arguments': values,
                'type': result_type,
                'status': status,
            }

        return {
            'kind': 'opaque',
            'operation': operation,
            'operation_kind': 'intrinsic',
            'reason': 'unsupported_intrinsic',
            'intrinsic': name,
            'intrinsic_family': intrinsic_family(name),
            'inputs': values,
            'status': 'partial',
        }

    def combined_status(self, values):
        for value in values:
            if value['status'] != 'complete':
                return 'partial'
        return 'complete'
