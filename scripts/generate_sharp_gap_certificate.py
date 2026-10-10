"""Generate the optimal eighth-order rational Bernstein proof; Lean verifies every identity.

Uses exact Fraction arithmetic. The generated source, not this program's
execution status, is the mathematical input checked by Lean.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
from hashlib import sha256
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(left, right):
    out = dict(left)
    for key, value in right.items():
        out[key] = out.get(key, F(0)) + value
    return {key: value for key, value in out.items() if value}


def scale(poly, scalar):
    return {key: value * scalar for key, value in poly.items() if value * scalar}


def multiply(left, right):
    out = {}
    for (a, b), u in left.items():
        for (c, d), v in right.items():
            key = a + c, b + d
            out[key] = out.get(key, F(0)) + u * v
    return {key: value for key, value in out.items() if value}


def power(poly, exponent):
    out = {(0, 0): F(1)}
    for _ in range(exponent):
        out = multiply(out, poly)
    return out


def evaluate(poly, x, y=F(0)):
    return sum((c * x**a * y**b for (a, b), c in poly.items()), F(0))


def moments_and_deficits(variable):
    moments = [{(0, 0): F(1)}, variable]
    for _ in range(2, 7):
        moments.append(add(scale(moments[-1], 6), scale(moments[-2], -3)))
    deficits = {}
    odd_factorial = 1
    for n in range(1, 7):
        odd_factorial *= 2 * n - 1
        deficits[n] = add(power(variable, n), scale(moments[n], -F(1, odd_factorial)))
    return moments, deficits


def derive_polynomial():
    """Derive R from s_n=6s_(n-1)-3s_(n-2), not entered R coefficients."""
    _, deficits = moments_and_deficits({(0, 0): F(1), (1, 0): F(-1)})
    require(deficits[2] == {(2, 0): F(1)}, "fourth-moment deficit changed")
    out = {}
    for n in range(2, 7):
        for (k, _), value in deficits[n].items():
            require(k + n - 4 >= 0, "compactification quotient is not polynomial")
            term = {(k + n - 4, n - 2): value * F(15, 2) ** (n - 2) / factorial(n)}
            out = add(out, multiply(term, power({(0, 0): F(1), (0, 1): F(-1)}, 6 - n)))
    require(max(a for a, _ in out) == 8 and max(b for _, b in out) == 4,
            "wrong bidegree")
    return out


def quantitative_polynomial(poly):
    one_minus_r = {(0, 0): F(1), (0, 1): F(-1)}
    correction = multiply({(0, 2): F(1, 28)}, power(one_minus_r, 2))
    return add(poly, scale(correction, -1))


def cell_power_coefficients(poly, i, j):
    w0, h, r0, step = F(9 * i, 160), F(9, 160), F(j, 8), F(1, 8)
    out = {}
    for (a, b), value in poly.items():
        for x in range(a + 1):
            for y in range(b + 1):
                key = x, y
                out[key] = out.get(key, F(0)) + (
                    value * comb(a, x) * w0 ** (a - x) * h**x
                    * comb(b, y) * r0 ** (b - y) * step**y
                )
    return out


def generate_certificate(poly):
    result = []
    for i in range(8):
        for j in range(8):
            cell = cell_power_coefficients(poly, i, j)
            for x in range(9):
                for y in range(5):
                    result.append(sum((
                        value * F(comb(x, a), comb(8, a)) * F(comb(y, b), comb(4, b))
                        for (a, b), value in cell.items() if a <= x and b <= y
                    ), F(0)))
    return result


def bernstein(n, k, x):
    return comb(n, k) * x**k * (1 - x)**(n - k)


def verify_cell(poly, i, j, coefficients):
    """A 9 by 5 unisolvent grid proves equality of bidegree (8,4) polynomials."""
    require(len(coefficients) == 45, "cell coefficient count changed")
    require(all(value >= 0 for value in coefficients), "negative Bernstein coefficient")
    for a in range(9):
        for b in range(5):
            x, y = F(a, 8), F(b, 4)
            expected = evaluate(poly, F(9, 160) * (i + x), F(1, 8) * (j + y))
            actual = sum((coefficients[5 * k + ell] * bernstein(8, k, x) * bernstein(4, ell, y)
                          for k in range(9) for ell in range(5)), F(0))
            require(actual == expected, f"cell identity failed: {i},{j} at {a},{b}")


def verify_certificate(poly, coefficients):
    require(len(coefficients) == 2880, "certificate coefficient count changed")
    for i in range(8):
        for j in range(8):
            offset = 45 * (8 * i + j)
            verify_cell(poly, i, j, coefficients[offset:offset + 45])


def canonical_bytes(coefficients):
    return "\n".join(str(value) for value in coefficients).encode("ascii")



def lean_fraction(q):
    if q.denominator == 1:
        return str(q.numerator)
    return f"({q.numerator} / {q.denominator} : ℝ)"


def main():
    root = Path(__file__).resolve().parents[1]
    poly = quantitative_polynomial(derive_polynomial())
    cert = generate_certificate(poly)
    verify_certificate(poly, cert)
    digest = sha256(canonical_bytes(cert)).hexdigest()
    require(digest == "e94c6c378471cf27f639f7aef4de4a114683a37136d6ebd98a84eda1edfded61",
            "sharp gap certificate differs")
    for i in range(8):
        lines = ["module", "", "public import SupportCriterion.SharpGapDefs", "",
            "@[expose] public section", "",
            "/-! Exact sharp gap Bernstein certificates on one row of eight closed cells. -/",
            "set_option maxRecDepth 8192", "set_option maxHeartbeats 8000000",
            "namespace SupportCriterion", ""]
        for j in range(8):
            terms = []
            for k in range(9):
                for l in range(5):
                    q = cert[45*(8*i+j)+5*k+l] * comb(8,k) * comb(4,l)
                    if q:
                        terms.append(f"{lean_fraction(q)} * x^{k} * (1-x)^{8-k} * y^{l} * (1-y)^{4-l}")
            expr = " +\n      ".join(terms)
            lines += [f"theorem sharp_gap_cell_{i}_{j} (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)",
                "    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :",
                f"    0 ≤ sharpCompactPolynomial (9*({i}+x)/160) (({j}+y)/8) := by",
                "  have hxm : 0 ≤ 1-x := sub_nonneg.mpr hx1",
                "  have hym : 0 ≤ 1-y := sub_nonneg.mpr hy1",
                f"  have hid : sharpCompactPolynomial (9*({i}+x)/160) (({j}+y)/8) =",
                "      "+expr+" := by",
                "    unfold sharpCompactPolynomial",
                "    ring",
                "  rw [hid]", "  positivity", ""]
        lines += ["end SupportCriterion", ""]
        target = root.joinpath(f"SupportCriterion/SharpGapRow{i}.lean")
        content = "\n".join(lines)
        if "--check" in sys.argv:
            require(target.read_text() == content, f"generated source differs: {target.name}")
        else:
            target.write_text(content)
    print(f"Verified and generated 64 cells, {len(cert)} rational coefficients; SHA256 {digest}")


if __name__ == "__main__":
    main()
