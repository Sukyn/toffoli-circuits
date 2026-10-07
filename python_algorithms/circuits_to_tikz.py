"""Render circuit JSON as editable TikZiT diagrams."""

from itertools import pairwise

from more_itertools import consecutive_groups
from sympy import Poly, Symbol, latex

from .utils import field


STYLES = r"""% TikZiT styles;
\tikzstyle{none}=[inner sep=0pt,outer sep=0pt]
\tikzstyle{ccontrol}=[shape=circle,draw=black,fill=black,inner sep=0pt,outer sep=0pt,minimum size=1.5mm]
\tikzstyle{cplus}=[shape=circle,draw=black,fill=white,inner sep=0pt,outer sep=0pt,minimum size=4mm,font={\footnotesize}]
\tikzstyle{cbox}=[shape=rectangle,draw=black,fill=white,rounded corners=.7mm,inner sep=1mm,outer sep=0pt,minimum height=5mm,font={\scriptsize}]
\tikzstyle{cinput}=[anchor=east,inner sep=1mm,outer sep=0pt,font={\footnotesize}]
\tikzstyle{coutput}=[anchor=west,inner sep=1mm,outer sep=0pt,font={\footnotesize}]
\tikzstyle{ccoeff}=[anchor=north,inner sep=.4mm,outer sep=0pt,font={\scriptsize},fill=white]
\tikzstyle{ccoeffabove}=[anchor=south,inner sep=.4mm,outer sep=0pt,font={\scriptsize},fill=white]
\tikzstyle{cellipsis}=[fill=white,inner sep=0pt,outer sep=0pt,font={\footnotesize}]
\tikzstyle{cwire}=[-,draw=black,line width=.45pt,line cap=round]
\tikzstyle{cshortcut}=[-,draw=black,line width=.45pt,densely dashed]
"""


def _signed(value, p):
    """Choose the field representative closest to zero for a gate label.

    In F_5, reduce 8 modulo 5 to get 3. Since 3 exceeds p // 2 = 2,
    subtract 5 and display -2. Values 0, 1 and 2 keep their signs:

    >>> [_signed(value, 5) for value in range(5)]
    [0, 1, 2, -2, -1]
    >>> _signed(8, 5)
    -2
    >>> _signed(-2, 5)
    -2
    >>> _signed(3, 5)
    -2

    All three inputs in the last examples have residue 3, so all produce
    the same label. This changes the displayed number, not the field value.
    """
    value %= p
    return value if value <= p // 2 else value - p


def circuit_to_tikz(circuit):
    r"""Return one editable TikZiT picture for a circuit in the README format.

    Wire indices are row labels. An add with several controls is a product
    shortcut: multiply the values on its control wires.
    The picture uses STYLES and retains idle wires and empty circuits.

    For a complete small example, draw t <- t + 3*c over F_5. With input
    (c, t) = (2, 4), this gate would give (2, 0), since 4 + 3*2 = 10 = 0
    modulo 5. The renderer displays 3 as -2; it does not simulate the gate.

    >>> circuit = {
    ...     "q": 5, "wire_count": 2,
    ...     "operations": [
    ...         {"op": "add", "controls": [0], "target": 1, "coefficient": 3}
    ...     ],
    ... }
    >>> picture = circuit_to_tikz(circuit)

    The two rows have y coordinates 0 and -0.7. The single gate is at
    x = 0; the wire endpoints are at x = -0.6 and x = 0.65.
    Each row first gets a left endpoint and two labels: node IDs 0, 1, 2
    for row 0, then 3, 4, 5 for row 1. The gate adds control node 6,
    target node 7 and coefficient node 8. The control is above the target,
    so the -2 label goes below it, at -0.7 - 0.24 = -0.94:

    >>> for line in picture.splitlines():
    ...     if any(f"style={style}]" in line
    ...            for style in ("ccontrol", "cplus", "ccoeff")):
    ...         print(line)
      \node [style=ccontrol] (6) at (0.00000, 0.00000) {};
      \node [style=cplus] (7) at (0.00000, -0.70000) {$+$};
      \node [style=ccoeff] (8) at (0.00000, -0.94000) {$-2$};

    Right endpoints get IDs 9 and 10. The vertical edge joins control 6
    to target 7. Row 0 follows 0 -> 6 -> 9 and row 1 follows 3 -> 7 -> 10.
    Labels are separate nodes and do not enter these wire paths:

    >>> for line in picture.splitlines():
    ...     if r"\draw" in line:
    ...         print(line)
      \draw [style=cwire] (6) to (7);
      \draw [style=cwire] (0) to (6);
      \draw [style=cwire] (6) to (9);
      \draw [style=cwire] (3) to (7);
      \draw [style=cwire] (7) to (10);

    The returned text wraps all 11 nodes in nodelayer and these five edges
    in edgelayer, inside one tikzpicture. Load STYLES to draw that picture.
    """
    nodes, edges = [], []

    def node(style, x, y, label=""):
        r"""Append one node and return its ID, starting at zero.

        In the example above, node("ccontrol", 0, 0) sees six existing
        nodes, appends the \node line numbered (6), and returns 6.
        """
        index = len(nodes)
        nodes.append(f"  \\node [style={style}] ({index}) at ({x:.5f}, {y:.5f}) {{{label}}};")
        return index

    def chain(points, style="cwire"):
        """Join consecutive IDs; [0, 6, 9] adds edges 0 -> 6 and 6 -> 9.

        The first call in the example is chain([6, 7]), which adds only
        the vertical gate edge. Later calls connect each horizontal wire.
        """
        edges.extend(
            f"  \\draw [style={style}] ({start}) to ({end});"
            for start, end in pairwise(points)
        )

    K = field(circuit.get("q", circuit.get("p")))
    p = K.characteristic

    def element_label(value):
        if K.degree == 1:
            return str(_signed(value, p))
        # Base-p digits are coefficients of 1, alpha, ... in the JSON basis.
        coefficients = [_signed(int(c), p) for c in K(value).vector()]
        return latex(Poly.from_list(coefficients, Symbol("alpha")).as_expr())

    wire_count = circuit["wire_count"]
    gates = circuit["operations"]
    y_of = [-row * .7 for row in range(wire_count)]
    x_end = (max(len(gates), 1) - 1) * .75 + .65
    wire_nodes = []
    for row in range(wire_count):
        wire_nodes.append([node("none", -.6, y_of[row])])
        label = rf"\texttt{{{row}}}"
        node("cinput", -.6, y_of[row], label)
        node("coutput", x_end, y_of[row], label)
    for column, gate in enumerate(gates):
        x = column * .75
        kind = gate["op"]
        if kind in {"scale", "swap"}:
            wire = gate["wire"]
            if kind == "scale":
                coefficient = element_label(gate["coefficient"])
                text = rf"$\times ({coefficient})$" if K.degree > 1 else rf"$\times {coefficient}$"
            else:
                a, b = (str(gate[key] % p) if K.degree == 1 else element_label(gate[key])
                        for key in ("a", "b"))
                text = rf"$X_{{{a},{b}}}$"
            wire_nodes[wire].append(node("cbox", x, y_of[wire], text))
            continue
        target_row = gate["target"]
        coefficient = element_label(gate["coefficient"])
        controls = sorted(gate["controls"])
        shortcut = len(controls) > 1
        markers = {row: node("ccontrol", x, y_of[row]) for row in controls}
        # Keep every dot; the ellipsis annotates a gap, never an unrelated wire.
        for group in consecutive_groups(controls):
            run = list(group)
            if len(run) > 3:
                gap_y = (y_of[run[1]] + y_of[run[2]]) / 2
                node("cellipsis", x, gap_y, r"$\vdots$")
        target = node("cplus", x, y_of[target_row], "$-$" if coefficient == "-1" else "$+$")
        if coefficient not in {"1", "-1"}:
            # When controls straddle the target, use the side with more
            # clearance by placing the label away from the nearest one.
            nearest = min(controls, key=lambda row: (abs(row - target_row), row))
            above = nearest > target_row
            node("ccoeffabove" if above else "ccoeff", x,
                 y_of[target_row] + (.24 if above else -.24), f"${coefficient}$")
        # Explicitly join the full control span; crossing an unrelated wire
        # has no dot and consequently does not add a control.
        markers[target_row] = target
        for row, marker in markers.items():
            wire_nodes[row].append(marker)
        connected_nodes = [markers[row] for row in sorted(markers)]
        chain(connected_nodes, "cshortcut" if shortcut else "cwire")
    # Gates arrive in chronological (left-to-right) order on each wire.
    for row, points in enumerate(wire_nodes):
        points.append(node("none", x_end, y_of[row]))
        chain(points)

    return "\n".join([
        r"\begin{tikzpicture}", r"\begin{pgfonlayer}{nodelayer}",
        *nodes, r"\end{pgfonlayer}", r"\begin{pgfonlayer}{edgelayer}",
        *edges, r"\end{pgfonlayer}", r"\end{tikzpicture}", "",
    ])
