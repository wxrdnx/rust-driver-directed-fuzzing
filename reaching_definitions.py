import argparse
import json

def read_cfgs(path):
    with open(path) as file:
        for line in file:
            if line.strip():
                yield json.loads(line)

def place_key(place):
    projections = []
    for projection in place['projections']:
        projections.append(json.dumps(projection, sort_keys=True, separators=(',', ':')))
    return place['local'], tuple(projections)

def places_overlap(left, right):
    if left[0] != right[0]:
        return False
    left_path = left[1]
    right_path = right[1]
    length = min(len(left_path), len(right_path))
    return left_path[:length] == right_path[:length]

def is_weak_update(place):

    # When a variable is written, we have to decide whether the write
    # "definintely" replaces the old value (a "strong update")
    # or "might" replace the old value (a "weak update")
    #
    # Strong update: we know exactly which memory is written, so the old value is
    # gone
    # Example: x.a = 5 always overwrites x.a with 100% certainty,
    # so the previous value of x.a is overwritten with a new one
    #
    # Weak update: we can't be certain which memory is written,
    # or we don't know whether the memory address is still the same,
    # so the old value might still be there
    # Example: *p = 5 could write to any of the variables depending on what p points to
    # In this case we keep the old value and add a new one
    # and later if *p is read its value is set with all possible values
    # 
    # Doing so may result in some redundant values, but it never misses a real one

    # The following projections make a write weak:
    #   - deref (write through pointer deference like *p)
    #   - index (write through array indexing like a[i])
    #   - constant_index (write through constant array indexing like a[3])
    #   - subslice (writing a range of elements like a[1..4])

    weak_projections = {'deref', 'index', 'constant_index', 'subslice'}
    for projection in place['projections']:
        if projection['kind'] in weak_projections:
            return True
    return False

def copy_state(state):
    copied = {}
    for place, definitions in state.items():
        copied[place] = set(definitions)
    return copied

def argument_definitions(function):
    definitions = []
    for local in function['locals']:
        if local['kind'] != 'argument':
            continue
        function_id = function['function']['id']
        argument = local['argument_index']
        definitions.append({
            'id': f'{function_id}:argument:{argument}',
            'kind': 'argument',
            'argument_index': argument,
            'place': {'kind': 'place', 'local': local['id'], 'projections': [], 'type': local['type']},
        })
    return definitions

def apply_definition(state, definition):
    key = place_key(definition['place'])
    if is_weak_update(definition['place']):
        # Weak update: we aren't sure whether the old value will be replaced
        # so keep the existing values and add the new value alongside them
        if key not in state:
            state[key] = set()
        state[key].add(definition['id'])
        return

    # Strong update: the old value is definitely replaced
    # First remove the old value and also anything "inside it"
    # e.g. writing x kills x.a, x.a.a, x.b, x.b.a, x.b.a.a, x.c, ...
    # e.g. writing x.b kills x.b, x.b.a, x.b.a.a, ... but not x.a, x.a.a, or x.c
    keys = []
    for current in state:
        if current[0] != key[0]:
            continue
        if current[1][:len(key[1])] == key[1]:
            keys.append(current)
    for current in keys:
        del state[current]
    # Now this write is the only definition that can reach later reads
    state[key] = {definition['id']}

def apply_operation(state, operation):
    # Update def-use state after one MIR operation

    # StorageLive -> storage for a local variable begins
    # StorageDead -> storage for a local variaable ends
    # Both do not correspond to assignments
    # e.g. StorageLive(_2) means storage for _2 is available,
    # but _2 does not cotain a valid value
    # e.g. StorageDead(_2) means lifetime of _2 has ended,
    # _2 must not be used until another StorageLive starts a new lifetime
    if operation['kind'] in {'storage_live', 'storage_dead'}:
        keys = []
        for key in state:
            if key[0] == operation['local']:
                keys.append(key)
        for key in keys:
            del state[key]
        return
    for definition in operation.get('defines', []):
        apply_definition(state, definition)

def fixed_point(function, arguments):
    # Determine which definitions can reach the beginning of every bb
    # e.g.
    # bb0:
    #     _1 = 10
    #     goto bb1
    # bb1:
    #     _2 = _1 + 1
    # It determines that the definition of _1 in bb0 reaches the beginning of bb1

    # build predecessors
    # e.g.
    # bb0 -> bb1
    # bb0 -> bb2
    # bb1 -> bb3
    # bb2 -> bb3
    #
    # the predecessor map will be
    # {
    #     'bb0': [],
    #     'bb1': ['bb0'],
    #     'bb2': ['bb0'],
    #     'bb3': ['bb1', 'bb2'],
    # }
    predecessors = {}
    for block in function['blocks']:
        predecessors[block['id']] = []
    for edge in function['edges']:
        predecessors[edge['target']].append(edge['source'])

    blocks = {block['id']: block for block in function['blocks']}
    inputs = {block: {} for block in blocks}
    outputs = {block: {} for block in blocks}

    entry = function['function']['entry_block']

    # Create the entry def-use state for function arguments
    # e.g., 
    # fn add_one(value: usize) -> usize {
    #     value + 1
    # }
    # corresponding mir:
    # _0 = Add(_1, 1)
    # There is no local assignment that defines _1, the value comes from the caller
    # So we need to create a pseudo-definition and associate it with _1:
    # 
    entry_state = {}
    for definition in arguments:
        entry_state[place_key(definition['place'])] = {definition['id']}

    changed = True
    while changed:
        changed = False
        for block_id, block in blocks.items():

            # Collect all blocks that can flow into the current block
            states = []
            for predecessor in predecessors[block_id]:
                states.append(outputs[predecessor])

            # If the current block is an entry block, include the entry state
            if block_id == entry:
                states.append(entry_state)

            # Merge defs that can enter the current block
            # e.g. if bb1 has {'_2': {'def1'}} and bb2 has {'_2': {'def2'}} and both flow into bb3
            # then bb3 receives {'_2': {'def1', 'def2'}}
            incoming = {}
            for state in states:
                for place, definitions in state.items():
                    if place not in incoming:
                        incoming[place] = set()
                    incoming[place] |= definitions

            # Update def-use state, determine which defs leave the block
            outgoing = copy_state(incoming)

            # A MIR basic block has two parts: statements and a terminator
            # e.g.
            # bb0:
            #    StorageLive(_1) // statement
            #    _1 = 10         // statement
            #    goto -> bb1     // terminator
            # both need to be processed in order
            for statement in block['statements']:
                apply_operation(outgoing, statement)
            apply_operation(outgoing, block['terminator'])

            if incoming != inputs[block_id] or outgoing != outputs[block_id]:
                inputs[block_id] = incoming
                outputs[block_id] = outgoing
                changed = True
    return inputs

def reaching_for_use(state, use):
    key = place_key(use['place'])
    definitions = set()
    for current, current_definitions in state.items():
        if places_overlap(current, key):
            definitions |= current_definitions
    return definitions

def resolve_uses(function, inputs):
    edges = []
    unresolved = []
    seen = set()
    for block in function['blocks']:
        state = copy_state(inputs[block['id']])

        # A MIR basic block has two parts: statements and a terminator
        # e.g.
        # bb0:
        #    StorageLive(_1) // statement
        #    _1 = 10         // statement
        #    goto -> bb1     // terminator
        # both need to be processed in order
        operations = block['statements'] + [block['terminator']]
        for operation in operations:
            for use in operation.get('uses', []):
                definitions = reaching_for_use(state, use)
                if not definitions:
                    unresolved.append(use)
                for definition in definitions:
                    edge = definition, use['id']
                    if edge in seen:
                        continue
                    seen.add(edge)
                    edges.append({'source': definition, 'target': use['id'], 'kind': 'def_use'})
            apply_operation(state, operation)
    return edges, unresolved

def analyze_function(function):
    arguments = argument_definitions(function)
    inputs = fixed_point(function, arguments)
    edges, unresolved = resolve_uses(function, inputs)
    return {
        'record': 'function_dataflow',
        'schema_version': 1,
        'function': function['function'],
        'argument_definitions': arguments,
        'edges': edges,
        'unresolved_uses': unresolved,
    }

def analyze(input_path, output_path):
    with open(output_path, 'w') as output:
        for function in read_cfgs(input_path):
            dataflow = analyze_function(function)
            output.write(json.dumps(dataflow, separators=(',', ':')) + '\n')
    return True

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('input')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.input, args.output)
