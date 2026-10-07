"""Product-addition counts and group sizes for parameters checked by main.py."""

from math import inf

from .utils import max_degree, power_cost


def add_group(previous, costs):
    """Append a nonempty group; retain the minimum cost and its group sizes.

    previous[n] is (cost, sizes) for n controls; costs[s] prices the
    new group of size s. The returned table has the same length as previous.
    Equal costs choose lexicographically smaller sizes.

    Example: start with one-group partitions, using illustrative costs.
    previous[2] = (5, (2,)) means that one group of two controls costs 5.
    previous[0] has infinite cost because a nonempty group cannot cover
    zero controls. Appending another group gives two-group partitions.

    >>> previous = [(inf, ()), (2, (1,)), (5, (2,)), (9, (3,))]
    >>> costs = [inf, 2, 5, 9]
    >>> add_group(previous, costs)
    [(inf, ()), (inf, (1,)), (4, (1, 1)), (7, (1, 2))]

    For each total, try every new group size s from 1 to total. The old
    groups cover total-s controls, so each candidate has:

        cost = previous[total-s][0] + costs[s]
        sizes = previous[total-s][1] + (s,)

    The entries are computed as follows:

    total=1: only s=1 is possible. Its cost is previous[0][0] + costs[1]
    = inf + 2, so the stored entry is (inf, (1,)). The infinite cost marks
    this total as impossible; its stored sizes are unused.

    total=2:
        s=1: previous[1][0] + costs[1] = 2 + 2 = 4, sizes (1, 1).
        s=2: previous[0][0] + costs[2] = inf + 5, so it is impossible.
    The minimum is (4, (1, 1)).

    total=3:
        s=1: previous[2][0] + costs[1] = 5 + 2 = 7, sizes (2, 1).
        s=2: previous[1][0] + costs[2] = 2 + 5 = 7, sizes (1, 2).
        s=3: previous[0][0] + costs[3] = inf + 9, so it is impossible.
    The finite candidates tie. We don't really care which one is chosen,
    so we do it lexicographically.

    There is no total=4 entry: len(previous) is 4, so the largest total
    is 3. previous[3] is unused here because adding a nonempty group to
    those three controls would exceed that limit.
    """
    return [(inf, ())] + [
        min((previous[total - size][0] + costs[size],
             previous[total - size][1] + (size,))
            for size in range(1, total + 1))
        for total in range(1, len(previous))
    ]


def count_tables(q, max_d=128, borrowed=0, algorithm=None):
    """Build tables of (transposition count, group sizes).

    Divide entries use table[d]; Borrow-and-conquer uses table[d + b][d]
    for d controls and b borrowed wires. An infinite cost is unreachable.
    Omit algorithm to build both recursive tables.

    Example: build both tables over F_5 (because it's the simplest one), through four controls. 
    A degree-2 polarization costs 6 in powers alone; degree 3 costs 8. These are the
    only possible polarization degrees because max_degree(5) = 3.

    Divide starts with C_1 = 0 and C_2 = 6. For d=3, partition d-1=2:
        (2,):   6 + 3*C_2 = 24.
        (1, 1): 8 + 3*C_1 + 4*C_1 = 8.
    Thus C_3 = 8. For d=4, partition d-1=3:
        (3,):   6 + 3*C_3 = 30.
        (1, 2): 8 + 3*C_1 + 4*C_2 = 32.
        (2, 1): 8 + 3*C_2 + 4*C_1 = 26.
    Thus C_4 = 26, with groups (2, 1).

    >>> tables = count_tables(5, 4)
    >>> tables["divide-and-conquer"]
    [(inf, ()), (0, ()), (6, (1,)), (8, (1, 1)), (26, (2, 1))]

    The mixed table grows one diagonal N=d+b at a time:
        N=1: only d=1, so its cost is 0.
        N=2: the previous diagonal supplies C_1=0; d=2 costs 6.
        N=3: the previous costs 0 and 6 give d=3 a cost of 8, as above.
        N=4: the previous costs 0, 6, 8 give d=4 a cost of 26.
    At N=4, d=3 has one borrowed wire, so also try a ladder. Its first
    group uses two controls: preparation costs 2*6=12 on diagonal N=3.
    The final update has 3-2+1=2 controls and costs 2*6=12 on diagonal
    N=4. The total 24 exceeds polarization's 8, so that entry stays put.
    There are no other ladder candidates through N=4.

    >>> [[cost for cost, _ in row]
    ...  for row in tables["borrow-and-conquer"][1:]]
    [[inf, 0], [inf, 0, 6], [inf, 0, 6, 8], [inf, 0, 6, 8, 26]]

    A larger example shows a ladder winning. For d=8, b=1, N=9, the best
    polarization costs 118, with groups (4, 3). A first group of four
    controls costs 26 on diagonal N=8; the final update has 8-4+1=5
    controls and costs 32 on N=9. The ladder therefore costs
    2*26 + 2*32 = 116, with groups (4, 4) covering all eight controls.
    Trying first-group sizes 2, 3, 4, 5, 6, 7 gives costs
    140, 128, 116, 116, 128, 140. Size 4 is kept when size 5 ties it.

    >>> tables = count_tables(5, 8, borrowed=1, algorithm="borrow-and-conquer")
    >>> tables["borrow-and-conquer"][9][8]
    (116, (4, 4))
    """
    def polarization(costs):
        """Price every parent using the supplied preparation costs.

        With q=5 and costs=[inf, 0, 6], start from partitions[0]=(0, ()).
        Adding group 1, with weight 3, gives partition costs 0 at size 1
        and 18 at size 2. Add the degree-2 power cost 6: the candidates
        for d=2 and d=3 are 6 and 24.

        Adding group 2, with weight 4, can only form (1, 1) within this
        table. Its cost is 3*0 + 4*0 = 0. The degree-3 powers cost 8,
        so replace the d=3 candidate 24 with 8. The result is
        [(inf, ()), (inf, ()), (6, (1,)), (8, (1, 1))]. Degree 1 stays
        infinite here because it is a SUM base case, not polarization.
        """
        best = [(inf, ())] * (len(costs) + 1)
        partitions = [(0, ())] + [(inf, ())] * (len(costs) - 1)
        for groups in range(1, min(max_degree(q) - 1, len(costs) - 1) + 1):
            # The new group pays for preparation, Gray flips, and restoration:
            # group 1 has weight 3, group 2 has weight 4, group 3 has weight 6.
            weight = 2 + 2 ** (groups - 1)
            partitions = add_group(partitions, [weight * c for c in costs])
            powers = power_cost(q, groups + 1)
            for d in range(groups + 1, len(best)):
                cost, sizes = partitions[d - 1]
                cost += powers
                # Keep the earlier construction when the counts tie.
                if cost < best[d][0]:
                    best[d] = cost, sizes
        return best

    # Degree two is polarization for every construction.
    divide = [(inf, ()), (0, ()), (power_cost(q, 2), (1,))]
    if algorithm in (None, "divide-and-conquer"):
        for d in range(3, max_d + 1):
            divide.append(polarization([cost for cost, _ in divide])[d])

    tables = {"q": q, "divide-and-conquer": divide}
    if algorithm in (None, "borrow-and-conquer"):
        # On diagonal N=d+b, preparations use N-1; final ladder updates use N.
        previous = [inf]
        mixed = [None]
        for total in range(1, max_d + borrowed + 1):
            current = polarization(previous)
            current[1] = (0, ())
            prefixes = [None, [(2 * c, (s,)) for s, c in enumerate(previous)]]
            # Later groups also use the preceding borrowed wire as a control.
            middle = [4 * c for c in previous[1:]] + [inf]
            for groups in range(2, (total - 1) // 2 + 1):
                prefixes.append(add_group(prefixes[-1], middle))
            for d in range(3, total + 1):
                for groups in range(1, min(total - d, d - 1) + 1):
                    # At least two controls precede the final, smaller subcall.
                    for used in range(max(groups, 2), d):
                        prefix_cost, sizes = prefixes[groups][used]
                        cost = prefix_cost + 2 * current[d - used + 1][0]
                        if cost < current[d][0]:
                            current[d] = cost, sizes + (d - used,)
            mixed.append(current)
            previous = [cost for cost, _ in current]
        tables["borrow-and-conquer"] = mixed
    return tables


def construction(tables, d, borrowed, algorithm):
    """Return the transposition count and group sizes for one product call.

    Polarization groups cover d-1 controls; ladder groups cover all d.
    Borrow's outer square wrapper and the SUM base case need no partition.

    Example: over F_5, a two-control product costs 6 transpositions.
    A one-control product is a SUM and costs none. All algorithms use
    these same two base entries.

    >>> tables = count_tables(5, 5, borrowed=1)
    >>> construction(tables, 1, 0, "borrow")
    (0, ())
    >>> construction(tables, 2, 0, "borrow")
    (6, (1,))

    Simple polarization of three controls uses two singleton groups.
    Its four signed cubic powers each cost 2, giving 4*2 = 8.

    >>> construction(tables, 3, 0, "simple_polarization")
    (8, (1, 1))

    Divide reads the entry already computed for d=5. Its possible
    polarization partitions of four controls have these costs:
        (4,):   6 + 3*26 = 84.
        (1, 3): 8 + 3*0 + 4*8 = 40.
        (2, 2): 8 + 3*6 + 4*6 = 50.
        (3, 1): 8 + 3*8 + 4*0 = 32.

    >>> construction(tables, 5, 0, "divide-and-conquer")
    (32, (3, 1))

    For mixed d=4, b=1, look up diagonal N=5, entry d=4. The chosen
    polarization costs 26. The one-borrowed-wire ladder alternatives
    cost 2*6 + 2*8 = 28 or 2*8 + 2*6 = 28, so neither replaces it.

    >>> construction(tables, 4, 1, "borrow-and-conquer")
    (26, (2, 1))

    A binary ladder on three controls costs L_3 = 4*(3-2)*6 = 24.
    It starts with a two-control group, then appends one control.

    >>> construction(tables, 3, 1, "binary-borrowed-ladder")
    (24, (2, 1))

    Borrow on five controls splits them into sizes 3 and 2. Its square
    wrapper calls the first ladder three times, the second four times,
    and the two-control construction four times. Since L_3=24 and
    L_2=6, the cost is 3*24 + 4*6 + 4*6 = 120. The empty size tuple
    means that the wrapper supplies its own split.

    >>> construction(tables, 5, 0, "borrow")
    (120, ())
    """
    toffoli = tables["divide-and-conquer"][2][0]

    def ladder(s):
        """Price the binary ladder used inside Borrow.

        With toffoli=6, L_1=0 (a SUM) and L_2=6 (one two-control call).
        For s=3, four such calls cost 4*(3-2)*6 = 24; for s=4, eight
        calls cost 4*(4-2)*6 = 48. The separate s=2 case matters:
        applying the general formula there would incorrectly give 0.
        """
        if s == 1:
            return 0
        return toffoli if s == 2 else 4 * (s - 2) * toffoli

    if d <= 2:
        return tables["divide-and-conquer"][d]
    if algorithm == "simple_polarization":
        return power_cost(tables["q"], d), (1,) * (d - 1)
    if algorithm == "binary-borrowed-ladder":
        return ladder(d), (2,) + (1,) * (d - 2)
    if algorithm == "borrow":
        return 3 * ladder((d + 1) // 2) + 4 * ladder(d // 2) + 4 * toffoli, ()
    table = tables[algorithm]
    return table[d + borrowed][d] if algorithm == "borrow-and-conquer" else table[d]


def compute_counts(q, max_d=128):
    """Return rows (d, C_d, C_d^b, C_d^m), with no extra wires.

    Example: for q=5 through d=4, Divide costs 0, 6, 8, 26. The mixed
    entries on diagonals N=d have the same costs. Borrow also starts
    at 0 and 6, then uses its wrapper with ladder costs L_1=0, L_2=6:
        d=3: 3*L_2 + 4*L_1 + 4*6 = 18 + 0 + 24 = 42.
        d=4: 3*L_2 + 4*L_2 + 4*6 = 18 + 24 + 24 = 66.
    Reading the three counts at each d gives the following rows.

    >>> compute_counts(5, 4)
    [(1, 0, 0, 0), (2, 6, 6, 6), (3, 8, 42, 8), (4, 26, 66, 26)]
    """
    tables = count_tables(q, max_d)
    divide, mixed = tables["divide-and-conquer"], tables["borrow-and-conquer"]
    return [(d, divide[d][0], construction(tables, d, 0, "borrow")[0], mixed[d][d][0])
            for d in range(1, max_d + 1)]

