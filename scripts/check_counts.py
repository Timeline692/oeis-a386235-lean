"""Exact arithmetic checks accompanying the A386235 counting formulas.

Run with Python 3.8 or later: python3 scripts/check_counts.py
No external packages or network connection are needed.
The finite computations are not used as a proof of the asymptotic theorem.
"""

import json
from decimal import Decimal, localcontext
from math import isqrt


def count_exact(n):
    if n < 3:
        return 0
    lower_square = n + 22
    upper_square = 13 * n - 14
    lower_root = isqrt(lower_square)
    if lower_root * lower_root < lower_square:
        lower_root += 1
    if (lower_root - n) % 2:
        lower_root += 1
    total = 0
    for m in range(lower_root, isqrt(upper_square) + 1, 2):
        s = (m * m - lower_square) // 2
        total += max(0, min(n - 3, s // 5) + 1 - (s + 5) // 6)
    return total


def count_direct(n):
    return sum(
        isqrt(n + 10 * q + 12 * r) ** 2 == n + 10 * q + 12 * r
        for q in range(1, n - 1)
        for r in range(1, n - q)
    )


def main():
    for n in range(3, 301):
        exact = count_exact(n)
        direct = count_direct(n)
        if exact != direct:
            raise AssertionError((n, exact, direct))

    # Values visible in the OEIS entry and its linked table.
    expected = {3: 1, 12: 2, 100: 85, 10000: 91413, 20000: 258667}
    for n, value in expected.items():
        if count_exact(n) != value:
            raise AssertionError((n, count_exact(n), value))

    with localcontext() as context:
        context.prec = 60
        constant = (1 - 66 * Decimal(11).sqrt() + 65 * Decimal(13).sqrt()) / 180
        table = []
        for n in [3, 12, 100, 10000, 20000, 1000000]:
            value = count_exact(n)
            radius = Decimal(n).sqrt()
            scaled_error = (Decimal(value) - constant * Decimal(n) * radius) / radius
            table.append({"n": n, "a(n)": value, "scaled_error": str(scaled_error)})
        result = {
            "direct_enumeration_range": [3, 300],
            "direct_enumeration_cases": 298,
            "oeis_sample_checks": len(expected),
            "K_decimal": str(constant),
            "table": table,
            "status": "all finite checks passed",
        }
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
