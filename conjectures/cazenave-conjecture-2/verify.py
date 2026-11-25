#!/usr/bin/env python3
"""Exact check: Conjecture 2 (#20829) of T. Cazenave, "Lemmas and Conjectures in Spectral Graph Theory",
arXiv:2611.03879, Section 7, is false.

Claim: for every connected graph, lambda_2(A) <= mu_1(L) - 2, where lambda_2 is the second largest
adjacency eigenvalue (with multiplicity) and mu_1 the largest Laplacian eigenvalue.

Counterexample G(4,3): two diamonds K4 - e joined tip to tip by a path with 3 inner vertices (n = 11).
Also checks the family G(k, L): two copies of K_k - e joined at their missing-edge endpoints by a path
with L inner vertices.

Run: python3 verify.py      (Python 3.8+, standard library only)
"""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lib"))
from exact import graph6, from_edges, laplacian, kth_largest, fmt


def G(k, L):
    """Two K_k - e, tips (endpoints of the missing edges) joined by a path with L inner vertices."""
    edges = []
    for off in (0, k):
        edges += [(off + a, off + b) for a in range(k) for b in range(a + 1, k) if (a, b) != (0, k - 1)]
    path = [k - 1] + [2 * k + i for i in range(L)] + [k]  # tip of copy 1 ... tip of copy 2
    edges += list(zip(path, path[1:]))
    return from_edges(2 * k + L, edges)


def check(A, name):
    l2_lo, _ = kth_largest(A, 2)
    _, m1_hi = kth_largest(laplacian(A), 1)
    broken = l2_lo > m1_hi - 2
    print(f"{name:28s} n={len(A):2d}:  lambda_2 >= {fmt(l2_lo)}   mu_1 - 2 <= {fmt(m1_hi - 2)}   "
          f"-> {'conjecture FALSE' if broken else 'holds here'}")
    return broken


ok = check(G(4, 3), "G(4,3) built from scratch")
ok &= check(graph6("J^_GGC??WB_"), "graph6 J^_GGC??WB_")
print("family G(k, L), small cases:")
expected = {(4, 2): False, (4, 3): True, (4, 4): True, (5, 1): False, (5, 2): True, (6, 1): True, (7, 1): True}
for (k, L), want in expected.items():
    ok &= check(G(k, L), f"G({k},{L})") == want
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
