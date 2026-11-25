#!/usr/bin/env python3
"""Rigorous check: five more inequalities marked "ouverte" (open) in the archive of T. Cazenave,
"Lemmas and Conjectures in Spectral Graph Theory", arXiv:2611.03879 (archive index_conjectures.csv, 31 Oct 2026),
are false. These are ordinary entries of his automatically generated corpus, not the paper's highlighted ones.

Notation: lambda_i = i-th largest adjacency eigenvalue, mu_i = i-th largest Laplacian eigenvalue,
R = Randic index (sum over edges of 1/sqrt(d_u d_v)), rad = radius, rk = rank of the adjacency matrix,
log = natural logarithm.

Eigenvalues: rational brackets from exact inertia counts. Square roots, log and exp: Python's Decimal at
60 digits (correctly rounded), with a safety margin of 1e-40 on every side.

Run: python3 verify.py      (Python 3.8+, standard library only)
"""
import os
import sys
from decimal import Decimal, getcontext
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lib"))
from exact import graph6, degrees, laplacian, distances, kth_largest, rank

getcontext().prec = 60
EPS = Decimal("1e-40")


def dec(q):
    return Decimal(q.numerator) / Decimal(q.denominator)


def invariants(s):
    A = graph6(s)
    n, d = len(A), degrees(A)
    R = sum(1 / (Decimal(d[i] * d[j])).sqrt() for i in range(n) for j in range(i + 1, n) if A[i][j])
    lam1, lam2 = kth_largest(A, 1), kth_largest(A, 2)
    mu2 = kth_largest(laplacian(A), 2)
    rad = min(max(row) for row in distances(A))
    return dict(n=n, R=(R - EPS, R + EPS), l1=tuple(map(dec, lam1)), l2=tuple(map(dec, lam2)),
                mu2=tuple(map(dec, mu2)), rad=rad, rk=rank(A))


CASES = []


def case(ids, text, g6, lhs_lo, rhs_hi):
    v = invariants(g6)
    lo, hi = lhs_lo(v), rhs_hi(v)
    CASES.append(lo > hi)
    print(f"{ids:28s} {text:30s} graph6 {g6:22s} n={v['n']:2d}:  left >= {float(lo):.6f} > right <= {float(hi):.6f}"
          f"  -> {'FALSE' if lo > hi else 'not certified'}")


case("#861166", "rad <= 2 (R - lambda_2)", "I^}??KF@w",
     lambda v: Decimal(v["rad"]), lambda v: 2 * (v["R"][1] - v["l2"][0]))
case("#1053490", "lambda_2 <= R - rad/2", "I^}??KF@w",
     lambda v: v["l2"][0], lambda v: v["R"][1] - Decimal(v["rad"]) / 2)
case("#2632674", "lambda_2 <= R - sqrt(rad - 1)", "K^~{??B?wF_^",
     lambda v: v["l2"][0], lambda v: v["R"][1] - (Decimal(v["rad"] - 1).sqrt() - EPS))
case("#753029", "mu_2 <= 1 + 2^lambda_1", "N?B{?C@?G????????Bw",
     lambda v: v["mu2"][0], lambda v: 1 + (v["l1"][1] * Decimal(2).ln()).exp() + EPS)
# #121183, #123215, #715458 are the same inequality written three ways: (sqrt(log rk))^R = sqrt((log rk)^R) = (log rk)^(R/2)
case("#121183 #123215 #715458", "lambda_2 <= (log rk)^(R/2)", "J?{G?????N_",
     lambda v: v["l2"][0], lambda v: ((v["R"][1] / 2) * Decimal(v["rk"]).ln().ln()).exp() + EPS)

ok = all(CASES)
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
