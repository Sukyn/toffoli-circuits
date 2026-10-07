"""Independent finite-field and JSON/TikZiT integration checks.

Run from the repository root: python -m pytest python_algorithms/test_circuits.py
"""

import copy
from itertools import pairwise, product
import json
from math import prod
from pathlib import Path
import random
import re
import subprocess
import sys

import pytest

from python_algorithms.main import main
from python_algorithms.algorithms_count import compute_counts, construction, count_tables
from python_algorithms.utils import ALGORITHMS
from python_algorithms.algorithms_to_circuits import generate_circuit
from python_algorithms.circuits_to_tikz import circuit_to_tikz


def simulate(circuit, values):
    """Interpret gate definitions directly, independently of their construction."""
    p = circuit.get('q', circuit.get('p'))
    state = list(values)
    for gate in circuit['operations']:
        kind = gate['op']
        if kind == 'add':
            state[gate['target']] += gate['coefficient'] * prod(state[c] for c in gate['controls'])
        elif kind == 'scale':
            state[gate['wire']] *= gate['coefficient']
        elif kind == 'swap':
            wire, a, b = gate['wire'], gate['a'], gate['b']
            if state[wire] == a:
                state[wire] = b
            elif state[wire] == b:
                state[wire] = a
        else:
            raise AssertionError(f'Unknown operation {kind}')
        state = [value % p for value in state]
    return state


def is_sum(gate):
    """A one-control addition is a primitive SUM, not a recursive shortcut."""
    return gate['op'] == 'add' and len(gate['controls']) == 1


def assert_product_addition(circuit, values, d):
    expected = list(values)
    expected[d] = (expected[d] + prod(expected[:d])) % circuit['q']
    assert simulate(circuit, values) == expected, values


@pytest.mark.parametrize('p', (5, 7, 11, 13, 17, 19, 23))
def test_polarization_across_fields(p):
    # Vary power degrees and multiplier orders through the public generator.
    # The oracle is direct product addition, including nonzero targets.
    rng = random.Random(p)
    for d in range(2, min(p - 2, 8) + 1):
        circuit = generate_circuit(p, d, 'simple_polarization')
        controls = [[value] * d for value in (0, 1, p // 2, p - 1)]
        controls += [[0 if index == zero else 1 for index in range(d)] for zero in range(d)]
        controls += [[rng.randrange(1, p) for _ in range(d)] for _ in range(3)]
        for values, target in product(controls, (0, p - 1)):
            assert_product_addition(circuit, values + [target], d)


@pytest.mark.parametrize('algorithm, d', tuple(product(ALGORITHMS, (1, 2, 3))))
def test_small_circuits_exhaustively(algorithm, d):
    # Every input, including nonzero targets and zeros among the controls.
    circuit = generate_circuit(5, d, algorithm)
    assert all(is_sum(g) or g['op'] in {'scale', 'swap'} for g in circuit['operations'])
    for values in product(range(5), repeat=d + 1):
        assert_product_addition(circuit, values, d)


def test_deeper_circuits_restore_arbitrary_borrowed_wires():
    rng = random.Random(20260921)
    cases = [(5, 7, a, b) for a in ALGORITHMS[1:] for b in (0, 2)]
    cases += [(7, 5, 'simple_polarization', 1), (11, 7, 'simple_polarization', 0), (11, 6, 'simple_polarization', 1),
              (5, 14, 'borrow-and-conquer', 0), (7, 10, 'borrow-and-conquer', 3)]
    for p, d, algorithm, borrowed in cases:
        for depth in (0, 1, 2, None):
            circuit = generate_circuit(p, d, algorithm, depth, borrowed)
            for _ in range(20):
                assert_product_addition(circuit, [rng.randrange(p) for _ in range(circuit['wire_count'])], d)
            # Nonzero controls prevent large-d cases from degenerating into identity checks.
            for _ in range(12):
                values = [rng.randrange(1, p) for _ in range(d)]
                values += [rng.randrange(p) for _ in range(1 + borrowed)]
                assert_product_addition(circuit, values, d)
            # The accumulator is a SUM receiver and is never used as workspace.
            for gate in circuit['operations']:
                assert gate.get('wire') != d
                assert d not in gate.get('controls', [])


@pytest.mark.parametrize('p', (5, 7, 11))
def test_count_table_matches_published_values(p):
    # Fixed rows from sections/count_tables.tex as included by core.tex.
    # Each tuple is (d, Divide, Borrow, Borrow-and-conquer); these values
    # are independent of the recurrence code shared by both programs.
    published = {
        5: [(2, 6, 6, 6), (3, 8, 42, 8), (4, 26, 66, 26),
            (5, 32, 120, 32), (6, 56, 192, 56), (7, 64, 264, 64),
            (8, 118, 360, 118), (16, 618, 1032, 496),
            (32, 3686, 2376, 1352), (64, 23840, 5064, 3048)],
        7: [(2, 8, 8, 8), (3, 12, 56, 12), (4, 32, 88, 32),
            (5, 48, 160, 48), (6, 68, 256, 68), (7, 84, 352, 84),
            (8, 116, 480, 116), (16, 492, 1376, 492),
            (32, 1992, 3168, 1664), (64, 8564, 6752, 4200)],
        11: [(2, 16, 16, 16), (3, 20, 112, 20), (4, 64, 176, 64),
             (5, 80, 320, 80), (6, 124, 512, 124), (7, 140, 704, 140),
             (8, 204, 960, 204), (16, 852, 2752, 852),
             (32, 3164, 6336, 2816), (64, 12988, 13504, 6944)],
    }
    rows = {row[0]: row for row in compute_counts(p, 64)}
    assert rows[1] == (1, 0, 0, 0)
    for expected in published[p]:
        assert rows[expected[0]] == expected


def test_count_table_reuse_across_degrees_and_families():
    table = count_tables(5, 16)
    # Reuse the same table in arbitrary degree/family order. Expected
    # costs are published values, not recomputed recurrence expressions.
    for d, algorithm, expected in (
        (16, 'divide-and-conquer', 618), (3, 'borrow', 42),
        (16, 'borrow-and-conquer', 496), (2, 'divide-and-conquer', 6),
        (3, 'simple_polarization', 8), (16, 'borrow', 1032),
    ):
        assert construction(table, d, 0, algorithm)[0] == expected


@pytest.mark.parametrize('p', (5, 7, 11))
def test_emitted_transpositions_match_shared_count_table(p):
    # Integration/accounting check: the independent count references are
    # the fixed paper fixtures above, since both APIs share recurrences.
    # Abstract products intentionally contain no decomposition or cost.
    counts = count_tables(p, 14)
    for d, algorithm in product(range(1, 15), ALGORITHMS[1:]):
        circuit = generate_circuit(p, d, algorithm)
        assert all(is_sum(g) or g['op'] in {'scale', 'swap'} for g in circuit['operations'])
        assert sum(g['op'] == 'swap' for g in circuit['operations']) == construction(counts, d, 0, algorithm)[0]


def test_sum_combination_preserves_behavior():
    circuit = generate_circuit(7, 10, 'borrow-and-conquer')
    assert len(circuit['operations']) == 549
    assert sum(g['op'] == 'swap' for g in circuit['operations']) == 180

    rng = random.Random(20260922)
    for borrowed, depth in product((0, 3), (0, 1, 2, None)):
        circuit = generate_circuit(7, 10, max_rec=depth, borrowed=borrowed)
        for first, second in pairwise(circuit['operations']):
            assert not (is_sum(first) and is_sum(second)
                        and first['controls'] == second['controls']
                        and first['target'] == second['target'])
        for _ in range(12):
            # Nonzero controls and dirty workspace exercise actual product addition.
            values = [rng.randrange(1, 7) for _ in range(10)]
            values += [rng.randrange(7)] + [rng.randrange(1, 7) for _ in range(borrowed)]
            assert_product_addition(circuit, values, 10)


@pytest.mark.parametrize('algorithm', ALGORITHMS[1:])
def test_cutoff_and_default_expansion(algorithm):
    root = generate_circuit(5, 8, algorithm, 0)
    assert len(root['operations']) == 1
    assert root['operations'][0] == {'op': 'add', 'controls': list(range(8)), 'target': 8, 'coefficient': 1}
    shallow = generate_circuit(5, 8, algorithm, 1)
    assert len(shallow['operations']) > 1
    shortcuts = [g for g in shallow['operations'] if g['op'] == 'add' and not is_sum(g)]
    assert shortcuts
    assert all(1 < len(g['controls']) < 8 for g in shortcuts)
    full = generate_circuit(5, 8, algorithm)
    assert all(is_sum(g) or g['op'] in {'scale', 'swap'} for g in full['operations'])
    assert generate_circuit(5, 8, algorithm, 100)['operations'] == full['operations']
    # Generation is reproducible, including tied DP partitions.
    assert generate_circuit(5, 8, algorithm, 1) == shallow


@pytest.mark.parametrize('algorithm, depth', tuple(product(ALGORITHMS, (0, 1, None))))
def test_algorithm_independent_json_contract(algorithm, depth):
    gate_fields = {
        'add': {'op', 'controls', 'target', 'coefficient'}, 'scale': {'op', 'wire', 'coefficient'},
        'swap': {'op', 'wire', 'a', 'b'},
    }
    circuit = generate_circuit(7, 3, algorithm, depth, borrowed=2)
    assert set(circuit) == {'q', 'wire_count', 'operations'}
    assert circuit['wire_count'] == 6
    controls = [gate['controls'] for gate in circuit['operations'] if gate['op'] == 'add']
    assert len({id(wires) for wires in controls}) == len(controls)
    for gate in circuit['operations']:
        assert set(gate) == gate_fields[gate['op']]
        references = [gate[key] for key in ('target', 'wire') if key in gate]
        references += gate.get('controls', [])
        assert all(type(index) is int and 0 <= index < circuit['wire_count']
                            for index in references)
    if depth == 0:
        assert circuit['operations'] == [
            {'op': 'add', 'controls': [0, 1, 2], 'target': 3, 'coefficient': 1}]


@pytest.mark.parametrize('algorithm', ALGORITHMS)
def test_one_control_at_zero_depth(algorithm):
    circuit = generate_circuit(5, 1, algorithm, max_rec=0, borrowed=2)
    assert circuit['operations'] == [{'op': 'add', 'controls': [0], 'target': 1, 'coefficient': 1}]
    for values in product(range(5), repeat=4):
        assert_product_addition(circuit, values, 1)


@pytest.mark.parametrize('args', ((3, 2), (9, 2), (15, 2), (True, 2), (5, 0), (5, 2.5)))
def test_invalid_parameters(args, tmp_path):
    assert_cli_error('circuit', *args, '-o', tmp_path / 'circuit.json')


@pytest.mark.parametrize('options', (
    ('--algorithm', 'unknown'), ('--algorithm', 'simple_polarization'),
    ('--max-rec', '-1'), ('--max-rec', 'True'), ('--max-rec', '1.5'),
    ('--max-rec', 'inf'), ('--max-rec', 'infinity'), ('--max-rec', 'unlimited'),
    ('--max-rec', 'none'), ('--borrowed', '-1'),
))
def test_invalid_generation_options(options, tmp_path):
    assert_cli_error('circuit', 5, 4, *options, '-o', tmp_path / 'circuit.json')


def test_layers_shortcuts_and_gate_order():
    circuit = generate_circuit(5, 8, 'borrow', 1)
    rendered = circuit_to_tikz(circuit)
    assert r'\begin{pgfonlayer}{nodelayer}' in rendered
    assert r'\begin{pgfonlayer}{edgelayer}' in rendered
    assert r'\vdots' in rendered
    nodes = re.findall(r'\\node \[style=[^]]+\] \((\d+)\)', rendered)
    assert len(nodes) == len(set(nodes))
    assert rendered.count(r'\begin{tikzpicture}') == 1
    assert rendered.count(r'\node [style=cinput]') == circuit['wire_count']
    labels = re.findall(r'\\node .*\{(.*)\};', rendered)
    assert not any(text in label for label in labels
                   for text in ('Panel', 'steps', 'controls', 'dirty', 'Identity circuit'))
    # One target or unary node per operation, ordered across the whole circuit.
    gates = re.findall(r'\\node \[style=(cplus|cbox)\] \(\d+\) at \(([^,]+),', rendered)
    expected_styles = [
        'cplus' if gate['op'] == 'add' else 'cbox'
        for gate in circuit['operations']
    ]
    assert [style for style, x in gates] == expected_styles
    assert [float(x) for style, x in gates] == [.75 * column for column in range(len(gates))]
    expected_swaps = [f"{gate['a']},{gate['b']}" for gate in circuit['operations'] if gate['op'] == 'swap']
    assert re.findall(r'X_\{([0-9]+,[0-9]+)\}', rendered) == expected_swaps
    assert 'cshortcut' in rendered
    signs = re.findall(r'\\node \[style=cplus\].*\{\$([+-])\$\};', rendered)
    assert signs == ['-' if gate['coefficient'] % circuit['q'] == circuit['q'] - 1 else '+'
                     for gate in circuit['operations'] if gate['op'] == 'add']


def test_no_fictitious_controls_on_intervening_wires():
    circuit = generate_circuit(5, 7, 'borrow', 0, borrowed=2)
    circuit['operations'][0]['controls'] = [0, 2, 4, 6]
    rendered = circuit_to_tikz(circuit)
    assert rendered.count(r'\node [style=ccontrol]') == 4
    assert r'\vdots' not in rendered


def test_manual_circuit_without_mutation():
    # This circuit is not produced by any generator and has no metadata.
    circuit = {
        'p': 5, 'wire_count': 4,
        'operations': [
            {'op': 'add', 'controls': [0], 'target': 1, 'coefficient': 1},
            {'op': 'scale', 'wire': 1, 'coefficient': 1},
            {'op': 'swap', 'wire': 2, 'a': 0, 'b': 1},
            {'op': 'add', 'controls': [0, 1], 'target': 3, 'coefficient': 1},
        ],
    }
    original = copy.deepcopy(circuit)
    circuit_to_tikz(circuit)
    assert circuit == original
    for a, b, c, t in product(range(5), repeat=4):
        updated_b = (b + a) % 5
        updated_c = 1 - c if c in (0, 1) else c
        expected = [a, updated_b, updated_c, (t + a * updated_b) % 5]
        assert simulate(circuit, [a, b, c, t]) == expected


def test_wire_count_preserves_idle_rows_and_empty_circuits():
    for operations in ([], [{'op': 'add', 'controls': [0], 'target': 1, 'coefficient': 1}]):
        circuit = {'p': 5, 'wire_count': 4, 'operations': operations}
        rendered = circuit_to_tikz(circuit)
        assert rendered.count(r'\node [style=cinput]') == 4
        assert rendered.count(r'\node [style=coutput]') == 4
        assert r'\texttt{3}' in rendered
        expected = [2, 4 if operations else 2, 3, 4]
        assert simulate(circuit, [2, 2, 3, 4]) == expected
    generated = generate_circuit(5, 1, borrowed=2)
    assert generated['wire_count'] == 4
    assert generated['operations'] == [{'op': 'add', 'controls': [0], 'target': 1, 'coefficient': 1}]
    assert circuit_to_tikz(generated).count(r'\node [style=cinput]') == 4


def assert_cli_error(*args):
    with pytest.raises(SystemExit) as error:
        main(list(map(str, args)))
    assert error.value.code == 2


def run_cli(command, *args):
    return subprocess.run(
        [sys.executable, str(Path(__file__).resolve().with_name('main.py')), command, *map(str, args)],
        check=True, capture_output=True, text=True,
    )


def test_cli_json_to_tikz(tmp_path):
    for q, algorithm in product((7, 25), ALGORITHMS):
        generated = run_cli('circuit', q, 4, '--algorithm', algorithm,
                            '--max-rec', 1, '-o', tmp_path / 'circuit.json')
        assert generated.stdout == ''
        circuit = json.loads((tmp_path / 'circuit.json').read_text())
        assert circuit == generate_circuit(q, 4, algorithm, max_rec=1)
        run_cli('tikz', tmp_path / 'circuit.json', '-o', tmp_path / 'circuit.tikz')
        assert r'\tikzstyle{ccontrol}' in (tmp_path / 'circuit.tikzstyles').read_text()
        figure = (tmp_path / 'circuit.tikz').read_text()
        assert r'\begin{tikzpicture}' in figure
        assert r'\tikzstyle' not in figure
        assert r'\documentclass' not in figure
    run_cli('circuit', 7, 10, '--algorithm', 'borrow-and-conquer',
            '-o', tmp_path / 'circuit.json')
    circuit = json.loads((tmp_path / 'circuit.json').read_text())
    assert len(circuit['operations']) == 549


def test_count_cli_csv():
    assert run_cli('count', 5, '--max-d', 3).stdout == 'd,Cd,Cd_b,Cd_m\n1,0,0,0\n2,6,6,6\n3,8,42,8\n'
    assert run_cli('count', 25, '--max-d', 3).stdout == 'd,Cd,Cd_b,Cd_m\n1,0,0,0\n2,32,32,32\n3,48,224,48\n'


@pytest.mark.parametrize('args', (('count', '9'), ('count', '15'), ('count', '5', '--max-d', '0')))
def test_invalid_count_parameters(args):
    assert_cli_error(*args)


def test_invalid_json_syntax_is_rejected_before_output(tmp_path):
    source, output = tmp_path / 'input.json', tmp_path / 'output.tikz'
    source.write_text('{', encoding='utf-8')
    assert_cli_error('tikz', source, '-o', output)
    assert not output.exists()
    assert not output.with_suffix('.tikzstyles').exists()


def test_tikz_cli_accepts_bom_and_writes_companion_styles(tmp_path):
    source, output = tmp_path / 'input.json', tmp_path / 'circuit.tikz'
    source.write_text(json.dumps(generate_circuit(5, 4, max_rec=0)), encoding='utf-8-sig')
    result = run_cli('tikz', source, '-o', output)
    assert result.stdout == ''
    assert r'\begin{tikzpicture}' in output.read_text()
    assert r'\vdots' in output.read_text()
    assert r'\tikzstyle{ccontrol}' in output.with_suffix('.tikzstyles').read_text()


@pytest.mark.parametrize('command', ('circuit', 'tikz'))
def test_cli_requires_output(command, tmp_path, capsys):
    source = tmp_path / 'input.json'
    source.write_text(json.dumps(generate_circuit(5, 1)), encoding='utf-8')
    args = (5, 4) if command == 'circuit' else (source,)
    assert_cli_error(command, *args)
    assert '-o/--output' in capsys.readouterr().err
    assert list(tmp_path.iterdir()) == [source]


@pytest.mark.parametrize('source_name, output_name', (
    ('input.json', 'input.json'),
    ('input.tikzstyles', 'input.tikz'),
    ('input.json', 'output.tikzstyles'),
))
def test_tikz_cli_rejects_output_collisions(tmp_path, source_name, output_name):
    source, output = tmp_path / source_name, tmp_path / output_name
    contents = json.dumps(generate_circuit(5, 1))
    source.write_text(contents, encoding='utf-8')
    assert_cli_error('tikz', source, '-o', output)
    assert source.read_text() == contents
    assert list(tmp_path.iterdir()) == [source]
