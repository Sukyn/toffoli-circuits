"""Count, construct, and render product-addition circuits."""

import argparse
import csv
import json
from pathlib import Path
import sys

from sympy import isprime

if not __package__:
    # Direct script execution needs the repository root for package imports.
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from python_algorithms.algorithms_count import compute_counts
from python_algorithms.algorithms_to_circuits import generate_circuit
from python_algorithms.circuits_to_tikz import STYLES, circuit_to_tikz
from python_algorithms.utils import ALGORITHMS


def main(argv=None):
    """Check command arguments, then run the count, circuit, or TikZiT export.

    A count run parses the strings "5" and "3" as integers, checks that
    5 is prime and at least 5 and that max_d is positive, then calls
    compute_counts(5, 3). Its three rows are written to standard output:

    >>> main(["count", "5", "--max-d", "3"])
    d,Cd,Cd_b,Cd_m
    1,0,0,0
    2,6,6,6
    3,8,42,8

    Here is a complete file export, using a temporary directory so the
    example leaves no files behind. The circuit command checks p = 5,
    d = 2 and max_rec = 0, then calls generate_circuit with the default
    borrow-and-conquer algorithm and no extra wires. Depth zero retains
    the whole two-control gate as a shortcut:

    >>> from tempfile import TemporaryDirectory
    >>> with TemporaryDirectory() as directory:
    ...     source = Path(directory) / "circuit.json"
    ...     figure = Path(directory) / "circuit.tikz"
    ...     main(["circuit", "5", "2", "--max-rec", "0", "-o", str(source)])
    ...     print(json.loads(source.read_text(encoding="utf-8")))
    ...     main(["tikz", str(source), "-o", str(figure)])
    ...     print(figure.exists(), figure.with_suffix(".tikzstyles").exists())
    ...     print("style=cshortcut" in figure.read_text(encoding="utf-8"))
    {'p': 5, 'wire_count': 3, 'operations': [{'op': 'add', 'controls': [0, 1], 'target': 2, 'coefficient': 1}]}
    True True
    True

    The tikz command reads that JSON, checks that neither output path
    overwrites it, and writes the picture plus circuit.tikzstyles. The
    last True confirms that the two-control gate uses a dashed connector.
    Omitting --max-rec from the circuit command would expand it fully.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    count = commands.add_parser("count", help="write transposition counts as CSV")
    circuit = commands.add_parser("circuit", help="construct a circuit as JSON")
    tikz = commands.add_parser("tikz", help="render circuit JSON as editable TikZiT")
    for command in (count, circuit):
        command.add_argument("p", type=int, help="prime field size, at least 5")
    count.add_argument("--max-d", type=int, default=128, help="maximum controls (default: 128)")
    circuit.add_argument("d", type=int, help="number of controls")
    circuit.add_argument("--algorithm", choices=ALGORITHMS, default="borrow-and-conquer")
    circuit.add_argument("--max-rec", type=int, help="product recursion depth; omit for full expansion")
    circuit.add_argument("--borrowed", type=int, default=0, help="extra restored dirty workspace wires")
    tikz.add_argument("input", type=Path, help="circuit JSON file")
    for command in (circuit, tikz):
        command.add_argument("-o", "--output", type=Path, required=True, help="destination file")
    args = parser.parse_args(argv)
    try:
        if args.command != "tikz" and (args.p < 5 or not isprime(args.p)):
            raise ValueError("p must be a prime >= 5")
        for name, minimum in (("max_d", 1), ("d", 1), ("borrowed", 0), ("max_rec", 0)):
            value = getattr(args, name, None)
            if value is not None and value < minimum:
                raise ValueError(f"{name} must be at least {minimum}")
        if args.command == "count":
            writer = csv.writer(sys.stdout, lineterminator="\n")
            writer.writerow(("d", "Cd", "Cd_b", "Cd_m"))
            writer.writerows(compute_counts(args.p, args.max_d))
            return
        if args.command == "circuit":
            if args.algorithm == "simple_polarization" and args.d > args.p - 2:
                raise ValueError("simple_polarization requires d <= p-2")
            result = generate_circuit(args.p, args.d, args.algorithm, args.max_rec, args.borrowed)
            output = json.dumps(result, indent=2) + "\n"
        else:
            result = json.loads(args.input.read_text(encoding="utf-8-sig"))
            styles_path = args.output.with_suffix(".tikzstyles")
            destinations = [args.output.resolve(), styles_path.resolve()]
            if args.input.resolve() in destinations:
                raise ValueError("output paths must not overwrite the input JSON")
            if destinations[0] == destinations[1]:
                raise ValueError("TikZ and style outputs must be different files")
            output = circuit_to_tikz(result)
            styles_path.write_text(STYLES, encoding="utf-8")
        args.output.write_text(output, encoding="utf-8")
    except (OSError, ValueError, TypeError, OverflowError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
