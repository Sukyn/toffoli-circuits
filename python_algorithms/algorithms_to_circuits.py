"""Construct circuits for parameters checked by main.py."""

from functools import lru_cache
from itertools import accumulate
from math import factorial

from more_itertools import split_into
from sympy import primitive_root
from sympy.combinatorics import GrayCode, Permutation

from .algorithms_count import construction, count_tables
from .utils import power_order


@lru_cache(maxsize=128)
def _power_cycles(p, order):
    """Share immutable multiplier cycles across circuit constructions.

    For p=5 and order=4, the primitive root is 2. The multiplier is
    2**((5-1)//4) % 5 = 2, so the permutation sends [0, 1, 2, 3, 4]
    to [0, 2, 4, 1, 3]. Starting at 1 visits 1 -> 2 -> 4 -> 3 -> 1.
    Zero is fixed and SymPy omits it from cyclic_form. Converting the
    remaining cycle to tuples makes the cached result immutable.

    >>> _power_cycles(5, 4)
    (2, ((1, 2, 4, 3),))
    """
    multiplier = pow(int(primitive_root(p)), (p - 1) // order, p)
    cycles = Permutation([multiplier * x % p for x in range(p)]).cyclic_form
    return multiplier, tuple(tuple(cycle) for cycle in cycles)


def generate_circuit(p, d, algorithm="borrow-and-conquer", max_rec=None, borrowed=0):
    """Build t += c_1 ... c_d over F_p, restoring controls and borrowed wires.

    Controls occupy wires 0 through d-1, the target is d, and borrowed
    wires follow it. Borrowed values can be arbitrary; they need not be zero.
    Operations run in list order. Adjacent SUMs on one wire pair combine.

    max_rec=0 keeps the whole product; 1 expands its first decomposition.
    Omit max_rec for full expansion. Unary powers always expand completely.
    simple_polarization requires d <= p-2.

    First keep a two-control product as one operation:

    >>> circuit = generate_circuit(5, 2, max_rec=0)
    >>> circuit["operations"]
    [{'op': 'add', 'controls': [0, 1], 'target': 2, 'coefficient': 1}]

    Now expand the same product. The controls are [0, 1], the target is 2,
    and the chosen polarization partition is (1,). It prepares two signed
    sums and applies a square addition to each, with coefficients 4 and 1.

    >>> circuit = generate_circuit(5, 2)
    >>> circuit["wire_count"], len(circuit["operations"])
    (3, 19)
    >>> sum(gate["op"] == "swap" for gate in circuit["operations"])
    6

    A complete run starts with wire values (u, v, t) = (1, 2, 0).
    Every value below is reduced modulo 5. X(a,b) exchanges the values
    a and b on u; it leaves other values of u unchanged.

        Step   Emitted operation     State (u, v, t)
         0     input                 (1, 2, 0)
         1     u += v                (3, 2, 0)
         2     t += u                (3, 2, 3)
         3     X(1,2) on u           (3, 2, 3)
         4     t += 4*u              (3, 2, 0)
         5     X(1,4) on u           (3, 2, 0)
         6     t += 3*u              (3, 2, 4)
         7     X(1,3) on u           (1, 2, 4)
         8     t += 2*u              (1, 2, 1)
         9     u *= 3                (3, 2, 1)
        10     u += 3*v              (4, 2, 1)
        11     t += 4*u              (4, 2, 2)
        12     X(1,2) on u           (4, 2, 2)
        13     t += u                (4, 2, 1)
        14     X(1,4) on u           (1, 2, 1)
        15     t += 2*u              (1, 2, 3)
        16     X(1,3) on u           (3, 2, 3)
        17     t += 3*u              (3, 2, 2)
        18     u *= 3                (4, 2, 2)
        19     u += v                (1, 2, 2)

    Both controls return to their inputs; the target gains 1*2 = 2.
    Steps 2-9 and 11-18 are the two complete square additions.

    For a recursive example, Divide with four controls chooses (2, 1).
    At depth one, its three calls on the two-control group remain shortcuts:

    >>> shallow = generate_circuit(5, 4, "divide-and-conquer", max_rec=1)
    >>> [len(g["controls"]) for g in shallow["operations"]
    ...  if g["op"] == "add" and len(g["controls"]) > 1]
    [2, 2, 2]
    >>> full = generate_circuit(5, 4, "divide-and-conquer", max_rec=2)
    >>> all(g["op"] != "add" or len(g["controls"]) == 1
    ...     for g in full["operations"])
    True
    """
    tables = count_tables(p, d, borrowed, algorithm)
    operations = []

    def add(controls, target, coefficient):
        """Append an addition, combining adjacent SUMs on the same wire pair.

        With p=5 and an empty operations list, add([0], 2, 2) appends
        {'op': 'add', 'controls': [0], 'target': 2, 'coefficient': 2}.
        Calling add([0], 2, 4) next replaces it with coefficient
        (2+4) % 5 = 1. Calling add([0], 2, -1) then gives
        (1+4) % 5 = 0 and removes the gate, leaving an empty list.
        A nonzero addition on a different wire pair, or with multiple
        controls, starts a separate operation. Only adjacent matching SUMs
        combine.
        """
        coefficient %= p
        # Two consecutive t += a*c updates add their coefficients modulo p.
        # For p=5, coefficients 2 and 3 cancel and leave no gate.
        if coefficient and len(controls) == 1 and operations:
            previous = operations[-1]
            if previous.get("controls") == controls and previous["target"] == target:
                coefficient = (coefficient + operations.pop()["coefficient"]) % p
        if coefficient:
            operations.append({"op": "add", "controls": controls.copy(), "target": target,
                               "coefficient": coefficient})

    def power(source, target, degree, coefficient):
        """Build Algorithm 1's power addition with star transpositions.

        Take p=5, degree=2, coefficient=1. The multiplier is 2 and its
        nonzero cycle is (1, 2, 4, 3). Fix a=1. The powers modulo 5
        are (1, 4, 1, 4), giving the following transfer calculations:

            b   prefix   inverse of b-a   -prefix/(b-a) modulo 5
            2      1            1                    4
            4      5            2                    0
            3      6            3                    2

        Each prefix stops just before b in the cycle. A zero transfer
        emits no SUMs, but its swap remains. Starting with values
        (source, target) = (2, 1), the complete emitted sequence gives:

            t += 4*s       (2, 4)
            X(1,2) on s    (1, 4)
            t += s         (1, 0)
            X(1,4) on s    (4, 0)
            t += 2*s       (4, 3)
            X(1,3) on s    (4, 3)
            t += 3*s       (4, 0)
            s *= 3         (2, 0)

        The last scaling is the inverse of multiplication by 2.
        The source is restored and the target is 1 + 2**2 = 0 modulo 5.
        degree is at least 2 and coefficient is nonzero modulo p.
        """
        order = power_order(p, degree)
        multiplier, cycles = _power_cycles(p, order)
        # SymPy omits fixed points; the only one here is zero, with increment zero.
        for cycle in cycles:
            a = cycle[0]
            # At b = cycle[j], prefix sums x**degree over cycle[:j].
            prefixes = accumulate(pow(x, degree, p) for x in cycle)
            for b, prefix in zip(cycle[1:], prefixes):
                transfer = -coefficient * prefix * pow(b - a, -1, p) % p
                add([source], target, transfer)
                operations.append({"op": "swap", "wire": source, "a": a, "b": b})
                add([source], target, -transfer)
        # The swaps implement the multiplier; its inverse restores the source.
        operations.append({"op": "scale", "wire": source, "coefficient": pow(multiplier, -1, p)})

    def split(wires, sizes):
        """Split wire indices into the chosen ordered groups.

        split([1, 2, 3, 4], (3, 1)) checks 3+1 = 4, takes the first
        three wires, then the remaining wire: [[1, 2, 3], [4]].
        """
        assert sum(sizes) == len(wires)
        return list(split_into(wires, sizes))

    def product(controls, target, borrowed, algorithm, coefficient=1, depth=0):
        """Expand one product call or emit it at the recursion limit.

        For p=5 and max_rec=1, a Divide call on controls [0, 1, 2, 3]
        and target 4 enters at depth=0. The table gives sizes (2, 1).
        Their sum is d-1 = 3, so polarization uses source 0 and groups
        [[1, 2], [3]]. Subcalls enter at depth=1: the three calls on
        [1, 2] remain two-control shortcuts and calls on [3] are SUMs.
        With max_rec=2, those two-control calls also expand; all remaining
        additions have one control. With max_rec=0, the initial call
        itself is one four-control shortcut.
        """
        d = len(controls)
        if d == 1 or (max_rec is not None and depth >= max_rec):
            add(controls, target, coefficient)
            return
        _, sizes = construction(tables, d, len(borrowed), algorithm)
        # Binary ladders use the same ladder construction with Divide subcalls.
        if algorithm == "binary-borrowed-ladder":
            algorithm = "divide-and-conquer"
        if algorithm == "borrow" and d > 2:
            borrow(controls, target, coefficient, depth)
        elif sum(sizes) == d:  # Ladders partition d controls; polarization partitions d-1.
            ladder(controls, target, borrowed, sizes, algorithm, coefficient, depth)
        else:
            polarization(controls, target, borrowed, sizes, algorithm, coefficient, depth)

    def subproduct(controls, target, available, algorithm, coefficient, depth):
        # The available pool excludes every protected parent target.
        """Choose the subcall's workspace and advance its recursion depth.

        In Borrow-and-conquer, take controls=[1, 2], target=0,
        available=[0, 1, 2, 3, 5], and depth=0. Removing the target
        and controls leaves workspace=[3, 5]; product enters at depth=1.
        Parent target 4 was absent from available, so it remains protected.
        For Divide, the same call passes an empty workspace list.
        """
        workspace = ([wire for wire in available
                      if wire != target and wire not in controls]
                     if algorithm == "borrow-and-conquer" else [])
        product(controls, target, workspace, algorithm, coefficient, depth + 1)

    def polarization(controls, target, borrowed, sizes, algorithm, coefficient, depth):
        """Add a product through signed powers, then restore the source.

        For p=5, controls=[0, 1, 2], sizes=(1, 1), and coefficient=1,
        take source value u=1, group values F_0=2 and F_1=3, and t=0.
        There are k=3 factors, so weights = inverse(4*6) modulo 5 = 4.
        Preparing both groups sets u = 1+2+3 = 1 modulo 5.

            Gray   Update before power   u   Power coefficient   New t
             00    already prepared      1           4             4
             01    u -= 2*3              0           1             4
             11    u -= 2*2              1           4             3
             10    u += 2*3              2           1             1

        Each row adds its coefficient times u**3 modulo 5. The last
        signed sum is u_original-F_0+F_1; restoring it adds F_0 and
        subtracts F_1, giving u = 2+2-3 = 1. The target finishes at
        1*2*3 = 1 modulo 5, with every control restored.
        """
        source = controls[0]
        groups = split(controls[1:], sizes)
        available = controls + borrowed
        k = len(groups) + 1
        # Fischer's identity cancels every term except the k-factor product.
        weights = coefficient * pow(2 ** (k - 1) * factorial(k), -1, p) % p

        def prepare(index, scale):
            """Add a scaled group product to the source.

            In the example above, prepare(1, -2) adds -2*3 to source
            value 1, giving (1-6) % 5 = 0. The group controls stay fixed.
            """
            subproduct(groups[index], source, available, algorithm, scale, depth)

        for i in range(len(groups)):
            prepare(i, 1)
        # For group product F_i, bit 0 means +F_i and bit 1 means -F_i.
        # Flipping its sign adds +/-2*F_i to source.
        # Two groups follow 00 -> 01 -> 11 -> 10; group 0 flips least often.
        previous = "0" * len(groups)
        for gray in GrayCode(len(groups)).generate_gray():
            for i, (before, after) in enumerate(zip(previous, gray)):
                if before != after:
                    prepare(i, 2 if after == "0" else -2)
            power(source, target, k, weights * (-1) ** gray.count("1"))
            previous = gray
        for i, bit in enumerate(previous):
            prepare(i, -1 if bit == "0" else 1)

    def ladder(controls, target, borrowed, sizes, algorithm, coefficient, depth):
        """Use two passes to cancel the borrowed wires' initial values.

        For p=5, controls=[0, 1, 2], target=3, borrowed=[4],
        sizes=(2, 1), and coefficient=1, the groups are [[0, 1], [2]].
        Start with values (c0, c1, c2, t, b) = (2, 3, 4, 1, 4).
        At the product-subcall boundaries the full run is:

            start=0: b += c0*c1    (2, 3, 4, 1, 0)
                     t += b*c2     (2, 3, 4, 1, 0)
                     b -= c0*c1    (2, 3, 4, 1, 4)
            start=1: t -= b*c2     (2, 3, 4, 0, 4)

        The second pass has no preparation to undo. The target becomes
        1 + 2*3*4 = 0 modulo 5, and the borrowed wire returns to 4.
        """
        groups = split(controls, sizes)
        ladder_wires = borrowed[:len(groups) - 1]
        if len(ladder_wires) != len(groups) - 1:
            raise ValueError("a borrowed ladder does not have enough workspace")
        available = controls + borrowed

        def update(index, scale):
            """Apply one ladder update to its borrowed wire or final target.

            In the example above, update(0, 1) uses controls [0, 1]
            and target 4, changing b from 4 to 0. update(1, 1) uses
            controls [4, 2] and target 3, so it adds 0*4 to t.
            """
            subcontrols = groups[index] if index == 0 else [ladder_wires[index - 1]] + groups[index]
            subtarget = target if index == len(groups) - 1 else ladder_wires[index]
            # A final update may borrow every other available wire.
            subproduct(subcontrols, subtarget, available, algorithm, scale, depth)

        last = len(groups) - 1
        # Two compute/update/uncompute passes cancel the dirty-wire terms.
        # The second pass omits the first preparation and negates the update.
        # With one borrowed value b: (b + F_1)*F_2 - b*F_2 = F_1*F_2.
        for start, sign in ((0, 1), (1, -1)):
            for i in range(start, last):
                update(i, 1)
            update(last, sign * coefficient)
            for i in reversed(range(start, last)):
                update(i, -1)

    def borrow(controls, target, coefficient, depth):
        """Use ((y+F)**2*H - (y-F)**2*H)/4 = y*F*H.

        F and H are the products of f_controls and h_controls;
        H is 1 when h_controls is empty. Take p=5, controls=[0, 1, 2],
        target=3, and coefficient=1. Then midpoint=2 gives f_controls=[0, 1]
        and h_controls=[]. The y wire has index 2 and the z wire has index 0.
        Starting with wire values (z, c1, y, t) = (2, 3, 4, 1) gives
        F=2*3=1, H=1, and quarter=1/4=4 modulo 5.

            prepare_f(1):    y = 4+1 = 0; t stays 1.
            square(4):       add 4*0**2 = 0; t stays 1.
            prepare_f(-2):   y = 0-2*1 = 3; t stays 1.
            square(-4):      add (-4)*3**2 = 4; t becomes 0.
            prepare_f(1):    y = 3+1 = 4; t stays 0.

        All calculations are modulo 5. The final state is (2, 3, 4, 0),
        so the target gains 2*3*4 = 4 and all controls are restored.
        Each square temporarily borrows z, restoring it before the next
        preparation; F describes the group product at those boundaries.
        """
        midpoint = (len(controls) + 1) // 2
        f_controls = controls[:midpoint]
        y, h_controls = controls[midpoint], controls[midpoint + 1:]
        z = f_controls[0]
        quarter = coefficient * pow(4, -1, p) % p

        def prepare_f(scale):
            """Add scale*F to y using the other group's controls as workspace.

            In the example above, F=1 and prepare_f(-2) changes y=0
            to 3 modulo 5. The call has controls [0, 1], target 2,
            no borrowed wires, and enters one product level deeper.
            """
            product(f_controls, y, h_controls,
                    "binary-borrowed-ladder", scale, depth + 1)

        def square(scale):
            # Borrow z from F: y*(z + y*H) - y*z = y**2*H.
            """Add scale*y**2*H while restoring the borrowed control z.

            In the second square above, y=3, H=1, and scale=-4=1 modulo 5.
            Starting with (z, t)=(2, 1), the four subcalls give:

                z += y*H         z=0, t=1
                t += scale*y*z   z=0, t=1
                z -= y*H         z=2, t=1
                t -= scale*y*z   z=2, t=0

            Thus z returns to 2 and t gains 3**2 = 4 modulo 5.
            """
            for sign in (1, -1):
                product([y] + h_controls, z, f_controls[1:],
                        "binary-borrowed-ladder", sign, depth + 1)
                product([y, z], target, [], "divide-and-conquer", sign * scale, depth + 1)

        prepare_f(1)
        square(quarter)
        prepare_f(-2)
        square(-quarter)
        prepare_f(1)

    controls = list(range(d))
    borrowed_wires = list(range(d + 1, d + 1 + borrowed))
    product(controls, d, borrowed_wires, algorithm)
    return {"p": p, "wire_count": d + 1 + borrowed, "operations": operations}
