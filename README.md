# Toffoli circuits

Python scripts for counting transpositions, constructing reversible product-addition circuits, and exporting editable TikZiT diagrams over prime fields `p >= 5`.

Implements divide-and-conquer, borrowed-wire, and borrow-and-conquer constructions. Requires Python 3.10 or newer.

## Usage

From the repository directory:

```sh
python -m pip install -r requirements.txt
python -m python_algorithms.main count 5 --max-d 8
python -m python_algorithms.main circuit 5 4 --max-rec 1 -o circuit.json
python -m python_algorithms.main tikz circuit.json -o circuit.tikz
```

Counts are CSV: `d` is the number of controls; `Cd`, `Cd_b`, and `Cd_m` are the counts for divide-and-conquer, borrowed-wire, and borrow-and-conquer.

The circuit command defaults to borrow-and-conquer. `--max-rec 1` limits recursion expansion; omit it for full expansion. TikZ export also creates `circuit.tikzstyles`.

## Tests

```sh
python -m pip install pytest
python -m pytest python_algorithms/test_circuits.py
```
