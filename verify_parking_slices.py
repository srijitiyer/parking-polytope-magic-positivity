#!/usr/bin/env python3
"""Prove magic positivity through dimension ten by exact lattice-slice algebra."""

from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, factorial, prod


@lru_cache(maxsize=None)
def power_sum(k):
    """Coefficients of sum_{r=1}^B r^k as a polynomial in B."""
    coefficients = [Fraction(0)] + [Fraction(comb(k + 1, j), k + 1) for j in range(1, k + 2)]
    for i in range(k):
        scale = Fraction(comb(k + 1, i), k + 1)
        for j, coefficient in enumerate(power_sum(i)):
            coefficients[j] -= coefficient * scale
    return coefficients


@lru_cache(maxsize=None)
def slice_sum(a, b):
    """Expand sum_{r=1}^B (A+B-r)^a (C+r)^b in A, B, C."""
    result = defaultdict(Fraction)
    for p in range(a + 1):
        for i in range(a - p + 1):
            scale = (-1) ** p * comb(a, p) * comb(a - p, i)
            for q in range(b + 1):
                for j, coefficient in enumerate(power_sum(p + q)):
                    result[i, a - p - i + j, b - q] += scale * comb(b, q) * coefficient
    return [(exponents, coefficient) for exponents, coefficient in result.items() if coefficient]


def next_dimension(previous, n):
    """Apply Theorem 4.1 to the polynomial in the preceding dimension."""
    result = defaultdict(Fraction)
    for exponents, coefficient in previous.items():
        a = exponents[0]
        for j in range(a + 1):
            result[(j + 1, a - j) + exponents[1:]] += coefficient * comb(a, j)
        for i in range(n - 2):
            for powers, factor in slice_sum(exponents[i], exponents[i + 1]):
                result[exponents[:i] + powers + exponents[i + 2:]] += coefficient * factor
        for (i, j, _), factor in slice_sum(exponents[-1], 0):
            result[exponents[:-1] + (i, j)] += coefficient * factor
    return {exponents: coefficient for exponents, coefficient in result.items() if coefficient}


def magic_transform(lattice_polynomial, n):
    """Apply Corollary 5.6 and convert to the magic basis."""
    ehrhart = defaultdict(Fraction)
    for exponents, coefficient in lattice_polynomial.items():
        # The substitutions are b_1 = 1 + t*x_1 and b_i = t*(1+x_i) for i>1.
        t_degree = sum(exponents[1:])
        binomials = [[comb(a, j) for j in range(a + 1)] for a in exponents]
        for powers in product(*(range(a + 1) for a in exponents)):
            scale = prod(row[j] for row, j in zip(binomials, powers))
            ehrhart[(t_degree + powers[0], *powers)] += coefficient * scale

    result = defaultdict(Fraction)
    for (degree, *parameters), coefficient in ehrhart.items():
        if coefficient:
            for j in range(n - degree + 1):
                result[degree + j, *parameters] += coefficient * (-1) ** j * comb(n - degree, j)
    return {exponents: coefficient for exponents, coefficient in result.items() if coefficient}


def verify_first_coefficient(magic, n):
    harmonic = [Fraction(0)]
    for k in range(1, n + 1):
        harmonic.append(harmonic[-1] + Fraction(1, k))

    observed = {e[1:]: c for e, c in magic.items() if e[0] == 1}
    expected = {(0,) * n: Fraction(n * (3 * n - 7), 4)}
    for j in range(1, n + 1):
        exponents = [0] * n
        exponents[j - 1] = 1
        k = n - j + 1
        expected[tuple(exponents)] = n if j == 1 else k * (1 + harmonic[n] - harmonic[k])
    assert observed == expected


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=10, help="largest dimension to check")
    args = parser.parse_args()

    lattice = {(1,): Fraction(1)}
    for n in range(2, args.through + 1):
        lattice = next_dimension(lattice, n)
        if n < 3:
            continue
        magic = magic_transform(lattice, n)
        assert len(magic) == comb(2 * n + 1, n) - (n == 3)
        assert magic[(0,) * (n + 1)] == 1
        assert min(magic.values()) == Fraction(1, factorial(n))
        verify_first_coefficient(magic, n)
        print(f"dimension {n}: {len(magic)} nonzero monomials, all positive", flush=True)


if __name__ == "__main__":
    main()
