#!/usr/bin/env python3
"""Exact check: Conjecture 6.1 of K. Banerjee and N. A. Smoot, "On a Problem of Gordon and Hughes: The 11-adic
Properties of Meromorphic Modular Functions on X0(22)", arXiv:2611.09681, is false in both parts.

For a in Z:  sum p1_a(n) q^n = (-q;q)^a / (q;q),   sum p2_a(n) q^n = (-q;q)^a / (q;q)^5.
Claim (1): if a = 3, 5, 7 (mod 11), then p1_a(11^alpha n + delta) = 0 mod 11^ceil(alpha/2), 24 delta = 1 - a (mod 11^alpha).
Claim (2): if a != 1, 3, 5 (mod 11), then p2_a(11^alpha n + delta) = 0 mod 11^ceil(alpha/2), 24 delta = 5 - a (mod 11^alpha).

Run: python3 verify.py      (Python 3.8+, standard library only, exact integers)
"""
import sys
from math import comb


def series(a, b, N):
    """Exact coefficients of (-q;q)^a / (q;q)^b up to q^N (a >= 0). Factors with n > N do not affect them."""
    f = [0] * (N + 1)
    f[0] = 1
    for n in range(1, N + 1):
        g = [0] * (N + 1)
        for j in range(0, min(a, N // n) + 1):  # (1 + q^n)^a = sum_j C(a, j) q^(nj)
            c, s = comb(a, j), j * n
            for k in range(0, N + 1 - s):
                if f[k]:
                    g[k + s] += c * f[k]
        f = g
        for _ in range(b):  # 1 / (1 - q^n)
            for k in range(n, N + 1):
                f[k] += f[k - n]
    return f


def v11(x):
    v = 0
    while x and x % 11 == 0:
        x //= 11
        v += 1
    return v


def delta(c, alpha):
    M = 11 ** alpha
    return (c * pow(24, -1, M)) % M


ok = True
print("counterexamples (alpha = 3, n = 0, so the coefficient must be divisible by 11^2 = 121):")
for part, a, b, c in [(1, 36, 1, 1 - 36), (2, 40, 5, 5 - 40)]:
    d = delta(c, 3)
    x = series(a, b, d)[d]
    fails = v11(x) < 2
    ok &= fails
    print(f"  part ({part}), a = {a} (a mod 11 = {a % 11}): delta = {d}, p{part}_{a}({d}) = {x}")
    print(f"      = 11^{v11(x)} * {x // 11 ** v11(x)}  -> {'not divisible by 121: claim FALSE' if fails else 'divisible'}")

print("control: the case the paper proves (part (2), a = 2, its Theorem 1.1) passes here:")
f = series(2, 5, 1400)
for alpha in (1, 2, 3):
    d, need = delta(5 - 2, alpha), -(-alpha // 2)
    worst = min(v11(f[i]) for i in range(d, 1401, 11 ** alpha))
    ok &= worst >= need
    print(f"  alpha = {alpha}: all indices {d} + {11 ** alpha} n up to 1400 have 11-adic valuation >= {worst} (needs {need})")
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
