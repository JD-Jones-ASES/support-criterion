"""Independent reconstruction by exact tensor interpolation.

This standalone checker imports no main-probe code. It obtains moments from
the two algebraic endpoints in Q(sqrt(6)), constructs the scalar expression
from explicit deficit polynomials, and solves two rational Bernstein systems.
It never uses the power-to-Bernstein conversion in generate_certificate.py.
"""

from fractions import Fraction as Q
from hashlib import sha256
from math import comb, factorial
from pathlib import Path
import json


EXPECTED = "4410a76573ec77f2d30013cfc0d8553cfeb96d18175a453a10962ce1d89c32ac"
SHIFT_EXPECTED = "93bb378759a066ecee34980c00e7a4a1cb518cd0044f658fddc48a216b8e3523"


def ensure(condition, message):
    if not condition:
        raise ValueError(message)


def field_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def field_multiply(a, b):
    return a[0]*b[0] + 6*a[1]*b[1], a[0]*b[1] + a[1]*b[0]


def field_divide(a, b):
    norm = b[0]*b[0] - 6*b[1]*b[1]
    ensure(norm != 0, "zero algebraic denominator")
    return field_multiply(a, (b[0]/norm, -b[1]/norm))


def explicit_deficits():
    """Derive each affine moment from ((B-v)A^n+(v-A)B^n)/(B-A)."""
    A, B = (Q(3), Q(-1)), (Q(3), Q(1))
    difference = (Q(0), Q(2))
    ensure(field_add(A, B) == (Q(6), Q(0)), "endpoint sum")
    ensure(field_multiply(A, B) == (Q(3), Q(0)), "endpoint product")
    ensure(field_divide(B, A) == (Q(5), Q(2)), "squared support ratio")
    apow, bpow = (Q(1), Q(0)), (Q(1), Q(0))
    deficits = {}
    critical_moments = [Q(1)]
    odd = 1
    expected = {
        2: [Q(1), Q(-2), Q(1)],
        3: [Q(6, 5), -Q(11, 5), Q(0), Q(1)],
        4: [Q(33, 35), -Q(12, 7), Q(0), Q(0), Q(1)],
        5: [Q(4, 7), -Q(109, 105), Q(0), Q(0), Q(0), Q(1)],
    }
    for n in range(1, 6):
        apow, bpow = field_multiply(apow, A), field_multiply(bpow, B)
        odd *= 2*n - 1
        slope = field_divide(field_add(bpow, (-apow[0], -apow[1])), difference)
        ba, ab = field_multiply(B, apow), field_multiply(A, bpow)
        constant = field_divide(field_add(ba, (-ab[0], -ab[1])), difference)
        ensure(slope[1] == constant[1] == 0, "moment failed to become rational-affine")
        critical_moments.append(slope[0] + constant[0])
        for endpoint, endpoint_power in ((A, apow), (B, bpow)):
            value = field_add((constant[0], Q(0)), field_multiply((slope[0], Q(0)), endpoint))
            ensure(value == endpoint_power, "pure endpoint mixture boundary")
        if n >= 2:
            polynomial = [-constant[0]/odd, -slope[0]/odd] + [Q(0)]*(n-1)
            polynomial[n] += 1
            ensure(polynomial == expected[n], "explicit moment deficit changed")
            deficits[n] = polynomial
    ensure(critical_moments[:5] == [1, 1, 3, 15, 81], "critical-law moment control")
    # At v=1 the fourth and sixth moments match Gaussian moments; the eighth
    # is 81 rather than 105. This is the exact order-eight deficit coefficient.
    ensure((105 - critical_moments[4])/factorial(8) == Q(1, 1680), "critical eighth-order deficit")
    return deficits


def polynomial_value(coefficients, x):
    out = Q(0)
    for coefficient in reversed(coefficients):
        out = out*x + coefficient
    return out


def scalar_value(deficits, w, r, shifted=False):
    """Evaluate compactified P directly, with both singular edges removed."""
    if w == 0:
        value = (Q(1, 2)*(1-r)**3 - Q(14, 15)*r*(1-r)**2
                 + Q(7, 15)*r*r*(1-r))
    elif r == 1:
        value = Q(343, 120)*w*polynomial_value(deficits[5], 1-w)
    else:
        z = 7*w*r/(1-r)
        p = sum((polynomial_value(deficits[n], 1-w)*z**(n-2)/factorial(n)
                 for n in range(2, 6)), Q(0))
        value = (1-r)**3*p/(w*w)
    if shifted:
        value -= ((1-r)**3 + 49*r*r*(1-r))/4000
    return value


def verify_degree_and_edges(deficits):
    """Algebraically establish the bidegree needed for exact interpolation."""
    degree_w = degree_r = 0
    edge_terms = []
    for n, coefficients in deficits.items():
        # Coefficients of f_n(1-w), independently expanded by the binomial rule.
        in_w = [sum((coefficients[m]*comb(m, k)*(-1)**k for m in range(k, n+1)), Q(0))
                for k in range(n+1)]
        for k, coefficient in enumerate(in_w):
            if not coefficient:
                continue
            ensure(k+n-4 >= 0, "uncancelled w denominator")
            degree_w = max(degree_w, k+n-4)
            degree_r = max(degree_r, (n-2)+(5-n))
            if k+n-4 == 0:
                edge_terms.append((coefficient*Q(7**(n-2), factorial(n)), n-2, 5-n))
    ensure((degree_w, degree_r) == (6, 3), "bidegree proof failed")
    for r in (Q(0), Q(1, 3), Q(2, 3), Q(1)):
        # These values include the critical corner where R vanishes.
        derived_edge = sum((c*r**a*(1-r)**b for c, a, b in edge_terms), Q(0))
        ensure(scalar_value(deficits, Q(0), r) == derived_edge, "w=0 cancellation identity")
        ensure(scalar_value(deficits, Q(0), r) >= 0, "compactified critical edge")
    ensure(polynomial_value(deficits[4], Q(1))/24 == Q(1, 105)
           and polynomial_value(deficits[5], Q(1))/120 == Q(1, 225), "excluded w=0 P boundary")


def basis(n, index, point):
    return comb(n, index)*point**index*(1-point)**(n-index)


def inverse(matrix):
    """Exact Gauss-Jordan elimination, separately for degrees six and three."""
    size = len(matrix)
    work = [list(row) + [Q(int(i == j)) for j in range(size)] for i, row in enumerate(matrix)]
    for column in range(size):
        pivot = next((row for row in range(column, size) if work[row][column]), None)
        ensure(pivot is not None, "singular interpolation matrix")
        work[column], work[pivot] = work[pivot], work[column]
        divisor = work[column][column]
        work[column] = [entry/divisor for entry in work[column]]
        for row in range(size):
            if row == column:
                continue
            multiplier = work[row][column]
            work[row] = [a-multiplier*b for a, b in zip(work[row], work[column])]
    ensure(all(work[i][j] == int(i == j) for i in range(size) for j in range(size)),
           "matrix inverse identity")
    return [row[size:] for row in work]


def interpolate(deficits, shifted=False):
    grids = [[Q(k, degree) for k in range(degree+1)] for degree in (6, 3)]
    matrices = [[[basis(degree, k, point) for k in range(degree+1)] for point in grid]
                for degree, grid in zip((6, 3), grids)]
    left, right = map(inverse, matrices)
    out = []
    for i in range(8):
        for j in range(8):
            values = [[scalar_value(deficits, Q(9, 160)*(i+x), Q(1, 8)*(j+y), shifted)
                       for y in grids[1]] for x in grids[0]]
            intermediate = [[sum((left[k][a]*values[a][b] for a in range(7)), Q(0))
                             for b in range(4)] for k in range(7)]
            coefficients = [[sum((intermediate[k][b]*right[ell][b] for b in range(4)), Q(0))
                             for ell in range(4)] for k in range(7)]
            for a in range(7):
                for b in range(4):
                    reconstructed = sum((matrices[0][a][k]*coefficients[k][ell]*matrices[1][b][ell]
                                         for k in range(7) for ell in range(4)), Q(0))
                    ensure(reconstructed == values[a][b], "interpolation reconstruction")
            out.extend(entry for row in coefficients for entry in row)
    return out


def validate(actual, expected):
    ensure(len(actual) == len(expected) == 1792, "incomplete certificate")
    ensure(all(value >= 0 for value in actual), "negative certificate coefficient")
    ensure(actual == expected, "certificate does not equal independent interpolant")


def expect_failure(callback, label):
    try:
        callback()
    except ValueError:
        return label
    raise ValueError("corruption accepted: " + label)


def check_one(deficits, filename, digest, shifted=False):
    generated = interpolate(deficits, shifted)
    retained_bytes = Path(__file__).with_name(filename).read_bytes()
    retained = [Q(line) for line in retained_bytes.decode("ascii").splitlines()]
    validate(retained, generated)
    canonical = "\n".join(str(value) for value in generated).encode("ascii")
    ensure(retained_bytes == canonical, "noncanonical retained certificate")
    ensure(sha256(canonical).hexdigest() == digest, "independent digest changed")
    changed = list(retained)
    changed[733] += Q(1, 107)
    negative = list(retained)
    negative[733] = Q(-1)
    controls = [expect_failure(lambda: validate(changed, generated), "positive coefficient perturbation"),
                expect_failure(lambda: validate(negative, generated), "negative coefficient"),
                expect_failure(lambda: validate(retained[:-28], generated), "omitted rectangle")]
    return {"sha256": digest, "coefficients": len(generated), "zero_coefficients": generated.count(Q(0)),
            "minimum_positive": str(min(value for value in generated if value > 0)),
            "rejected_corruptions": controls}


def main():
    deficits = explicit_deficits()
    verify_degree_and_edges(deficits)
    report = {"status": "INDEPENDENT_EXACT_CHECKS_PASS", "method": "endpoint algebra and inverse Bernstein matrices",
              "quantitative_certificate": check_one(deficits, "shifted_certificate.txt", SHIFT_EXPECTED, True),
              "scope": "finite exact certificate; no import from generate_certificate.py and no analytic proof-assistant claim"}
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
