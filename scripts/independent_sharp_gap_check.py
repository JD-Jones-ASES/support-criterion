"""Independent exact replay of the proposed sharp t^8 certificate.

Adapted from the internal GPT-6 Pro consultation dated 2026-10-10.
No imports from the repository or parent certificate generator.  Uses stdlib
Fractions, reconstructs the transformed polynomial twice, obtains its global
Bernstein controls by exact interpolation, and bisects them with de Casteljau.
Every resulting cell identity is checked on a full unisolvent tensor grid.
"""
from fractions import Fraction as F
from math import comb, factorial
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(*terms):
    out = {}
    for poly in terms:
        for key, value in poly.items():
            out[key] = out.get(key, F(0)) + value
    return {key: value for key, value in out.items() if value}


def scale(poly, c):
    return {key: value * c for key, value in poly.items() if value * c}


def mul(left, right):
    out = {}
    for (i, j), x in left.items():
        for (k, l), y in right.items():
            key = i + k, j + l
            out[key] = out.get(key, F(0)) + x * y
    return {key: value for key, value in out.items() if value}


def power(poly, n):
    out = {(0, 0): F(1)}
    for _ in range(n):
        out = mul(out, poly)
    return out


def val(poly, w, r):
    wp = [w ** i for i in range(1 + max(i for i, _ in poly))]
    rp = [r ** j for j in range(1 + max(j for _, j in poly))]
    return sum((c * wp[i] * rp[j] for (i, j), c in poly.items()), F(0))


one = {(0, 0): F(1)}
wpoly = {(1, 0): F(1)}
rpoly = {(0, 1): F(1)}
vpoly = add(one, scale(wpoly, -1))
one_minus_r = add(one, scale(rpoly, -1))

# Compute endpoint moments by multiplication of y modulo y^2-6y+3.
# A remainder c0+c1*y has expectation c0+c1*v.
remainders = [(F(1), F(0))]
for n in range(6):
    c0, c1 = remainders[-1]
    remainders.append((-3 * c1, c0 + 6 * c1))
require(remainders == [
    (1, 0), (0, 1), (-3, 6), (-18, 33),
    (-99, 180), (-540, 981), (-2943, 5346),
], "Endpoint moments do not match direct polynomial reduction")

f = {}
odd_factorial = 1
for n in range(1, 7):
    odd_factorial *= 2 * n - 1
    c0, c1 = remainders[n]
    s_n = add(scale(one, c0), scale(vpoly, c1))
    f[n] = add(power(vpoly, n), scale(s_n, -F(1, odd_factorial)))

# Direct numerator: (1-r)^4 * [P6(1-w, (15/2)wr/(1-r)) - z^2/1575].
kappa = F(15, 2)
numerator = {}
for n in range(2, 7):
    term = mul(f[n], power(wpoly, n - 2))
    term = mul(term, power(rpoly, n - 2))
    term = mul(term, power(one_minus_r, 6 - n))
    numerator = add(numerator, scale(term, kappa ** (n - 2) / factorial(n)))
shift = mul(power(wpoly, 2), mul(power(rpoly, 2), power(one_minus_r, 2)))
numerator = add(numerator, scale(shift, -kappa ** 2 / 1575))
require(all(i >= 2 for i, _ in numerator), "w^2 does not cancel")
R = {(i - 2, j): c for (i, j), c in numerator.items()}
require(max(i for i, _ in R) == 8, "Unexpected w degree")
require(max(j for _, j in R) == 4, "Unexpected r degree")

# Independent hand-factored reconstruction.
f3_over_w = {(0, 0): -F(4, 5), (1, 0): F(3), (2, 0): -F(1)}
factored = scale(power(one_minus_r, 4), F(1, 2))
factored = add(factored, scale(mul(f3_over_w, mul(rpoly, power(one_minus_r, 3))), F(5, 4)))
factored = add(factored, mul(add(scale(f[4], F(75, 32)), scale(one, -F(1, 28))),
                             mul(power(rpoly, 2), power(one_minus_r, 2))))
factored = add(factored, scale(mul(wpoly, mul(f[5], mul(power(rpoly, 3), one_minus_r))), F(225, 64)))
factored = add(factored, scale(mul(power(wpoly, 2), mul(f[6], power(rpoly, 4))), F(1125, 256)))
require(R == factored, "Independent transformed-polynomial identities differ")
R_at_zero = {(0, j): c for (i, j), c in R.items() if i == 0}
boundary_factor = scale(mul(power(one_minus_r, 2), power(add(one, scale(rpoly, -2)), 2)), F(1, 2))
require(R_at_zero == boundary_factor, "w=0 boundary factorization failed")


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def matmul(left, right):
    cols = transpose(right)
    return [[sum((x * y for x, y in zip(row, col)), F(0)) for col in cols] for row in left]


def inverse(matrix):
    n = len(matrix)
    aug = [row[:] + [F(int(i == j)) for j in range(n)] for i, row in enumerate(matrix)]
    for k in range(n):
        pivot = next(i for i in range(k, n) if aug[i][k])
        aug[k], aug[pivot] = aug[pivot], aug[k]
        a = aug[k][k]
        aug[k] = [x / a for x in aug[k]]
        for i in range(n):
            if i != k and aug[i][k]:
                a = aug[i][k]
                aug[i] = [x - a * y for x, y in zip(aug[i], aug[k])]
    return [row[n:] for row in aug]


def bernstein_values(n):
    return [[F(comb(n, k)) * F(i, n) ** k * (1 - F(i, n)) ** (n - k)
             for k in range(n + 1)] for i in range(n + 1)]


N, M = 8, 4
Bw, Br = bernstein_values(N), bernstein_values(M)
values = [[val(R, F(9, 20) * F(i, N), F(j, M)) for j in range(M + 1)]
          for i in range(N + 1)]
controls = matmul(matmul(inverse(Bw), values), transpose(inverse(Br)))
require(matmul(matmul(Bw, controls), transpose(Br)) == values,
        "Global exact Bernstein interpolation failed")


def bisect_row(row):
    layers = [list(row)]
    while len(layers[-1]) > 1:
        old = layers[-1]
        layers.append([(old[k] + old[k + 1]) / 2 for k in range(len(old) - 1)])
    left = [layer[0] for layer in layers]
    right = [layer[-1] for layer in reversed(layers)]
    return left, right


def bisect_w(matrix):
    split = [bisect_row(col) for col in transpose(matrix)]
    return transpose([pair[0] for pair in split]), transpose([pair[1] for pair in split])


def bisect_r(matrix):
    split = [bisect_row(row) for row in matrix]
    return [pair[0] for pair in split], [pair[1] for pair in split]


cells = {(0, 0): controls}
for level in range(3):
    subdivided = {}
    for (i, j), coeff in cells.items():
        for wi, wpart in enumerate(bisect_w(coeff)):
            for rj, part in enumerate(bisect_r(wpart)):
                subdivided[2 * i + wi, 2 * j + rj] = part
    cells = subdivided

# Every identity is replayed at 9 x 5 distinct tensor nodes.  Because both
# sides have bidegree <=(8,4), these exact evaluations prove the cell identity.
checks = 0
all_coeffs = []
zero_locations = []
for (i, j), coeff in sorted(cells.items()):
    got = matmul(matmul(Bw, coeff), transpose(Br))
    want = [[val(R, F(9, 160) * (i + F(k, N)), F(1, 8) * (j + F(l, M)))
             for l in range(M + 1)] for k in range(N + 1)]
    require(got == want, f"Cell {(i, j)} identity failed")
    checks += (N + 1) * (M + 1)
    for k, row in enumerate(coeff):
        for l, c in enumerate(row):
            require(c >= 0, f"Negative coefficient at {(i, j, k, l)}: {c}")
            all_coeffs.append(c)
            if c == 0:
                zero_locations.append((i, j, k, l))

require(len(all_coeffs) == 2880, "Incorrect total number of coefficients")
require(len(zero_locations) == 7, "Incorrect zero-coefficient count")
strings = [str(c) for c in all_coeffs]
report = {
    "status": "PASS",
    "method": "exact interpolation, de Casteljau subdivision, unisolvent cell replay",
    "bidegree": [N, M],
    "cells": len(cells),
    "coefficients": len(all_coeffs),
    "negative_coefficients": 0,
    "zero_coefficients": len(zero_locations),
    "zero_locations": zero_locations,
    "minimum_positive_coefficient": str(min(c for c in all_coeffs if c)),
    "exact_cell_evaluations": checks,
    "coefficient_sha256": hashlib.sha256("\n".join(strings).encode()).hexdigest(),
    "w_zero_boundary": "(1-r)^2*(1-2*r)^2/2",
    "parent_or_repository_imports": False,
}
require(report["coefficient_sha256"] == "e94c6c378471cf27f639f7aef4de4a114683a37136d6ebd98a84eda1edfded61",
        "Unexpected coefficient digest")
require(report["minimum_positive_coefficient"] == "27/1835008", "Unexpected positive minimum")
out = Path(__file__).resolve().parents[1] / "verification" / "sharp_gap_independent.json"
out.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
