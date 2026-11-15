import unittest

from rust_kernel_analyzer.analysis.reaching_definitions import analyze_function


def place(local):
    return {'kind': 'place', 'local': local, 'projections': [], 'type': {'kind': 'integer', 'bits': 64}}


def function(blocks, edges):
    return {
        'function': {'id': 'rust:test:loop', 'name': 'loop', 'entry_block': 'bb0'},
        'locals': [
            {'id': '_0', 'kind': 'return', 'argument_index': None, 'type': {'kind': 'other'}},
            {'id': '_1', 'kind': 'argument', 'argument_index': 0, 'type': {'kind': 'integer', 'bits': 64}},
        ],
        'blocks': blocks,
        'edges': edges,
    }


class ReachingDefinitionsTest(unittest.TestCase):
    def test_definition_replaces_earlier_definition(self):
        definition = {'id': 'def-new', 'place': place('_1')}
        use = {'id': 'use-after', 'place': place('_1')}
        blocks = [{
            'id': 'bb0',
            'statements': [
                {'id': 'assign', 'kind': 'assignment', 'defines': [definition], 'uses': []},
                {'id': 'read', 'kind': 'assignment', 'defines': [], 'uses': [use]},
            ],
            'terminator': {'id': 'return', 'kind': 'return', 'defines': [], 'uses': []},
        }]
        result = analyze_function(function(blocks, []))
        self.assertEqual(result['edges'], [{'source': 'def-new', 'target': 'use-after', 'kind': 'def_use'}])

    def test_definition_reaches_next_loop_iteration(self):
        definition = {'id': 'def-loop', 'place': place('_1')}
        use = {'id': 'use-loop', 'place': place('_1')}
        blocks = [{
            'id': 'bb0',
            'statements': [
                {'id': 'update', 'kind': 'assignment', 'defines': [definition], 'uses': [use]},
            ],
            'terminator': {'id': 'goto', 'kind': 'goto', 'defines': [], 'uses': []},
        }]
        edges = [{'source': 'bb0', 'target': 'bb0', 'kind': 'goto'}]
        result = analyze_function(function(blocks, edges))
        sources = {edge['source'] for edge in result['edges']}
        self.assertEqual(sources, {'rust:test:loop:argument:0', 'def-loop'})


if __name__ == '__main__':
    unittest.main()
