#!/usr/bin/env python3
"""Exact check: Conjecture 4 of Caporossi, Chasset, Furtula (GERAD G-2009-64), restated as open as
Conjecture 8.13 in Aouchiche & Hansen, "Distance spectra of graphs: a survey" (LAA 458, 2014), is false.

Claim: among connected graphs with n vertices and m <= (n-2)(n-3)/2 edges, distance energy
E_D = sum |eigenvalues of the distance matrix| is maximised by a path-complete graph PK(n, m):
a clique K_k with a path appended, the path vertex next to the clique joined to j clique vertices.

Run: python3 verify.py      (Python 3.8+, standard library only)
"""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lib"))
from exact import graph6, from_edges, distances, eigen_brackets, fmt

COUNTEREXAMPLES = [  # (n, m, graph6)
    (12, 44, "K]Nxnsor}^^R"),
    (12, 45, "K}ktb|y]e^x}"),
    (13, 54, "LNzq|snwyzdzmn"),
    (13, 55, "L^vimjjyp~|XN|"),
]


def path_complete(n, m):
    """All path-complete graphs PK with n vertices and m edges (there is at most one)."""
    out = []
    for k in range(2, n):
        j = m - k * (k - 1) // 2 - (n - k - 1)
        if 1 <= j <= k - 1:
            edges = [(a, b) for a in range(k) for b in range(a + 1, k)]
            edges += [(t, t + 1) for t in range(k, n - 1)]
            edges += [(a, k) for a in range(j)]
            out.append((k, j, from_edges(n, edges)))
    return out


def energy_bounds(A):
    """Rational lo <= E_D <= hi. trace(D) = 0, so E_D = 2 * (sum of positive eigenvalues)."""
    lo = hi = 0
    for a, b, k in eigen_brackets(distances(A)):
        lo += k * max(a, 0)
        hi += k * max(b, 0)
    return 2 * lo, 2 * hi


ok = True
for n, m, s in COUNTEREXAMPLES:
    G = graph6(s)
    assert len(G) == n and sum(map(sum, G)) // 2 == m, "wrong order or size"
    assert m <= (n - 2) * (n - 3) // 2, "outside the conjecture's range"
    pks = path_complete(n, m)
    assert len(pks) == 1, "PK(n, m) should be unique"
    k, j, P = pks[0]
    g_lo, g_hi = energy_bounds(G)
    p_lo, p_hi = energy_bounds(P)
    broken = g_lo > p_hi
    ok &= broken
    print(f"n={n} m={m} (limit {(n - 2) * (n - 3) // 2}):  E_D(counterexample) >= {fmt(g_lo)}   "
          f"E_D(PK = K{k} + path, j={j}) <= {fmt(p_hi)}   -> {'conjecture FALSE' if broken else 'not certified'}")
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
