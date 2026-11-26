#!/usr/bin/env python3
"""Check magic positivity through dimension five as polynomial identities."""

from collections import Counter, defaultdict
from itertools import combinations_with_replacement
from math import comb, factorial, prod


def has_distinct_representatives(masks):
    """Each mask is a set of available representatives for one occurrence."""
    states = {0}
    for allowed in sorted(masks, key=int.bit_count):
        following = set()
        for used in states:
            free = allowed & ~used
            while free:
                bit = free & -free
                following.add(used | bit)
                free -= bit
        if not following:
            return False
        states = following
    return True


def draconian_profiles(n):
    """Group the admissible multisets by (subset size, multiplicity)."""
    profiles = Counter()
    for size in range(n + 1):
        for masks in combinations_with_replacement(range(1, 1 << n), size):
            if has_distinct_representatives(masks):
                profile = tuple(sorted(
                    (mask.bit_count(), count) for mask, count in Counter(masks).items()
                ))
                profiles[profile] += 1
    return profiles


def multiply(left, right):
    """Multiply sparse polynomials stored as exponent tuples and integers."""
    result = defaultdict(int)
    for a, coefficient in left.items():
        for b, other in right.items():
            result[tuple(i + j for i, j in zip(a, b))] += coefficient * other
    return {exponents: value for exponents, value in result.items() if value}


def weight_polynomial(n, size):
    """Return t*w_size under b_i = 1+x_i, with t the first variable."""
    result = defaultdict(int)
    for j in range(max(0, size - 2) + 1):
        exponent = [1] + [0] * n
        exponent[size - j] = 1
        coefficient = (-1) ** j * comb(max(0, size - 2), j)
        result[tuple(exponent)] += coefficient
        if size >= 2:
            result[(1,) + (0,) * n] += coefficient
    return result


def scaled_magic_polynomial(n, profiles):
    """Compute n! times the magic transform of the Ehrhart polynomial."""
    constant = (0,) * (n + 1)
    rising = {}
    for size in range(1, n + 1):
        weight = weight_polynomial(n, size)
        factor = {constant: 1}
        for copies in range(1, size + 1):
            factor = multiply(factor, weight | {constant: copies - 1})
            rising[size, copies] = factor

    # The denominator of each draconian term divides n! because the sum
    # of that term's multiplicities is at most n.
    ehrhart = defaultdict(int)
    for profile, count in profiles.items():
        divisor = prod(factorial(copies) for _, copies in profile)
        scale, remainder = divmod(factorial(n), divisor)
        assert remainder == 0
        term = {constant: count * scale}
        for key in profile:
            term = multiply(term, rising[key])
        for exponents, coefficient in term.items():
            ehrhart[exponents] += coefficient

    # (1-u)^n E(u/(1-u)) replaces t^d by u^d(1-u)^(n-d).
    magic = defaultdict(int)
    for (degree, *parameters), coefficient in ehrhart.items():
        for j in range(n - degree + 1):
            magic[(degree + j, *parameters)] += coefficient * (-1) ** j * comb(n - degree, j)
    return {exponents: value for exponents, value in magic.items() if value}


if __name__ == "__main__":
    expected = {3: (84, 24, 34), 4: (2726, 108, 126), 5: (289022, 510, 462)}
    for n, target in expected.items():
        profiles = draconian_profiles(n)
        coefficients = scaled_magic_polynomial(n, profiles)
        counts = (sum(profiles.values()), len(profiles), len(coefficients))
        assert counts == target
        assert coefficients[(0,) * (n + 1)] == factorial(n)
        assert all(value > 0 for value in coefficients.values())
        print(f"dimension {n}: {counts[0]} sequences, {counts[1]} profiles, {counts[2]} positive terms")
