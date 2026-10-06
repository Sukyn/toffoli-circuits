# Toffoli circuits

Python scripts for counting transpositions, constructing reversible product-addition circuits, and exporting editable TikZiT diagrams over prime fields `p >= 5`.

Implements divide-and-conquer, borrowed-wire, and borrow-and-conquer constructions. Requires Python 3.10 or newer.

## Usage

Run these commands from the repository directory. First install the dependencies:

```sh
python -m pip install -r requirements.txt
```

`python -m python_algorithms.main` starts the command-line tool. Choose one of its three commands below.

### 1. Compare transposition counts

```sh
python -m python_algorithms.main count 5 --max-d 8
```

Here `5` is the field size (all arithmetic is modulo 5), and `--max-d 8` asks for circuits with 1 through 8 control wires. The command prints a CSV table in the terminal, comparing the number of one-wire transpositions needed by the three constructions.

The columns are `d` (number of controls), `Cd` (divide-and-conquer), `Cd_b` (borrowed-wire), and `Cd_m` (borrow-and-conquer). Append `> counts.csv` to save the table to a file.

### 2. Generate a circuit

```sh
python -m python_algorithms.main circuit 5 4 --max-rec 1 -o circuit.json
```

This writes `circuit.json`, a list of circuit operations implementing `t <- t + c1*c2*c3*c4 (mod 5)`. The `5` selects arithmetic modulo 5; the `4` selects four control wires, plus one target wire: **five wires total**. The default construction is borrow-and-conquer, with no extra wires. `-o` chooses the output filename.

`--max-rec 1` expands the first product decomposition and keeps deeper product subcircuits as shortcut blocks. Omit this option for full expansion into elementary gates; the number of wires stays the same.

### 3. Export the circuit diagram

```sh
python -m python_algorithms.main tikz circuit.json -o circuit.tikz
```

This reads the JSON from the previous step and creates `circuit.tikz` (the diagram) and `circuit.tikzstyles` (its gate styles). Use these files in TikZiT to view and edit the circuit. Shortcut blocks from a limited recursion depth appear with dashed connectors.

## Tests

```sh
python -m pip install pytest
python -m pytest python_algorithms/test_circuits.py
```
