"""Shared circuit names and finite-field power formulas."""

from functools import lru_cache

from sympy import divisors


ALGORITHMS = (
    "simple_polarization", "divide-and-conquer", "borrow", "borrow-and-conquer"
)


@lru_cache(maxsize=128)
def power_order(p, degree):
    """Return the smallest divisor of p-1 that does not divide degree.

    For 2 <= degree <= p-2, a multiplier of this order makes the powers
    sum to zero on each cycle, as required by the cycle-addition construction.

    Example: for p=7 and degree=2, the divisors of p-1=6 are 1, 2, 3, 6.
    Both 1 and 2 divide degree=2, so skip them. The next divisor is 3;
    2 % 3 = 2, so return 3 without trying 6.

    >>> power_order(7, 2)
    3

    For degree=3, skip 1 but stop at 2 because 3 % 2 = 1.

    >>> power_order(7, 3)
    2
    """
    return next(r for r in divisors(p - 1) if degree % r)


def power_cost(p, degree):
    """Count transpositions in all signed powers of one polarization step.

    Each of the 2**(degree-1) powers uses (p-1)//r nonzero cycles,
    with r-1 transpositions per cycle.

    Example: squares over F_5 use r=4, since 1 and 2 divide degree=2
    but 4 does not. Each power addition has (5-1)//4 = 1 nonzero cycle,
    requiring 4-1 = 3 transpositions. Polarization has 2**(2-1) = 2
    signed powers, so the total is 2*1*3 = 6.

    >>> power_cost(5, 2)
    6

    Over F_7 the same degree uses r=3. There are (7-1)//3 = 2 cycles,
    each costing 3-1 = 2 transpositions. With two powers, the total
    becomes 2*2*2 = 8.

    >>> power_cost(7, 2)
    8
    """
    r = power_order(p, degree)
    return 2 ** (degree - 1) * ((p - 1) // r) * (r - 1)
