"""Generate the shifted rational Bernstein proof; Lean verifies every identity.

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
    for _ in range(2, 6):
        moments.append(add(scale(moments[-1], 6), scale(moments[-2], -3)))
    deficits = {}
    odd_factorial = 1
    for n in range(1, 6):
        odd_factorial *= 2 * n - 1
        deficits[n] = add(power(variable, n), scale(moments[n], -F(1, odd_factorial)))
    return moments, deficits


def derive_polynomial():
    """Derive R from s_n=6s_(n-1)-3s_(n-2), not entered R coefficients."""
    _, deficits = moments_and_deficits({(0, 0): F(1), (1, 0): F(-1)})
    require(deficits[2] == {(2, 0): F(1)}, "fourth-moment deficit changed")
    out = {}
    for n in range(2, 6):
        for (k, _), value in deficits[n].items():
            require(k + n - 4 >= 0, "compactification quotient is not polynomial")
            term = {(k + n - 4, n - 2): value * F(7 ** (n - 2), factorial(n))}
            out = add(out, multiply(term, power({(0, 0): F(1), (0, 1): F(-1)}, 5 - n)))
    require(max(a for a, _ in out) == 6 and max(b for _, b in out) == 3,
            "wrong bidegree")
    return out


def quantitative_polynomial(poly):
    one_minus_r = {(0, 0): F(1), (0, 1): F(-1)}
    correction = add(power(one_minus_r, 3), multiply({(0, 2): F(49)}, one_minus_r))
    return add(poly, scale(correction, -F(1, 4000)))


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
            for x in range(7):
                for y in range(4):
                    result.append(sum((
                        value * F(comb(x, a), comb(6, a)) * F(comb(y, b), comb(3, b))
                        for (a, b), value in cell.items() if a <= x and b <= y
                    ), F(0)))
    return result


def bernstein(n, k, x):
    return comb(n, k) * x**k * (1 - x)**(n - k)


def verify_cell(poly, i, j, coefficients):
    """A 7 by 4 unisolvent grid proves equality of bidegree (6,3) polynomials."""
    require(len(coefficients) == 28, "cell coefficient count changed")
    require(all(value >= 0 for value in coefficients), "negative Bernstein coefficient")
    for a in range(7):
        for b in range(4):
            x, y = F(a, 6), F(b, 3)
            expected = evaluate(poly, F(9, 160) * (i + x), F(1, 8) * (j + y))
            actual = sum((coefficients[4 * k + ell] * bernstein(6, k, x) * bernstein(3, ell, y)
                          for k in range(7) for ell in range(4)), F(0))
            require(actual == expected, f"cell identity failed: {i},{j} at {a},{b}")


def verify_certificate(poly, coefficients):
    require(len(coefficients) == 1792, "certificate coefficient count changed")
    for i in range(8):
        for j in range(8):
            offset = 28 * (8 * i + j)
            verify_cell(poly, i, j, coefficients[offset:offset + 28])


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
    require(digest == "93bb378759a066ecee34980c00e7a4a1cb518cd0044f658fddc48a216b8e3523",
            "shifted certificate differs")
    for i in range(8):
        lines = ["module", "", "public import SupportCriterion.CertificateDefs", "",
            "@[expose] public section", "",
            "/-! Exact shifted Bernstein certificates on one row of eight closed cells. -/",
            "set_option maxRecDepth 8192", "set_option maxHeartbeats 8000000",
            "namespace SupportCriterion", ""]
        for j in range(8):
            terms = []
            for k in range(7):
                for l in range(4):
                    q = cert[28*(8*i+j)+4*k+l] * comb(6,k) * comb(3,l)
                    if q:
                        terms.append(f"{lean_fraction(q)} * x^{k} * (1-x)^{6-k} * y^{l} * (1-y)^{3-l}")
            expr = " +\n      ".join(terms)
            lines += [f"theorem shifted_cell_{i}_{j} (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)",
                "    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :",
                f"    0 ≤ shiftedPolynomial (9*({i}+x)/160) (({j}+y)/8) := by",
                "  have hxm : 0 ≤ 1-x := sub_nonneg.mpr hx1",
                "  have hym : 0 ≤ 1-y := sub_nonneg.mpr hy1",
                f"  have hid : shiftedPolynomial (9*({i}+x)/160) (({j}+y)/8) =",
                "      "+expr+" := by",
                "    unfold shiftedPolynomial compactPolynomial",
                "    ring",
                "  rw [hid]", "  positivity", ""]
        lines += ["end SupportCriterion", ""]
        target = root.joinpath(f"SupportCriterion/CertificateRow{i}.lean")
        content = "\n".join(lines)
        if "--check" in sys.argv:
            require(target.read_text() == content, f"generated source differs: {target.name}")
        else:
            target.write_text(content)
    print(f"Verified and generated 64 cells, {len(cert)} rational coefficients; SHA256 {digest}")


if __name__ == "__main__":
    main()
