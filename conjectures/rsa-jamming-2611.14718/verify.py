#!/usr/bin/env python3
"""Exact check: Conjecture 5.2 of Higuita-Diaz, Lopez, Roldan-Correa, "Random Sequential Adsorption versus
the Uniform Ensemble of Jammed Configurations: Stochastic Dominance on Graphs", arXiv:2611.14718, is false.

Claim: on every finite simple graph with maximum degree <= 3, N_stat <=_st N_seq, i.e.
P[N_seq <= k] <= P[N_stat <= k] for every k (Definition 2.1 of the paper), where
  N_seq  = size of the jammed set reached by random sequential adsorption: repeatedly occupy a vertex chosen
           uniformly among the available ones and block its neighbours, until none is available;
  N_stat = size of a maximal independent set chosen uniformly at random.

Run: python3 verify.py      (Python 3.8+, standard library only; about 2 seconds)
"""
import sys
from fractions import Fraction
from functools import lru_cache

EDGES = [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 7), (5, 8),
         (7, 9), (7, 10), (8, 11), (8, 12), (9, 13), (11, 14)]
n = 15
nb = [0] * n
for a, b in EDGES:
    nb[a] |= 1 << b
    nb[b] |= 1 << a
assert max(bin(x).count("1") for x in nb) == 3 and len(EDGES) == n - 1, "should be a tree of max degree 3"

# static model: all maximal independent sets, by brute force over all 2^15 vertex subsets
sizes = {}
for S in range(1 << n):
    if any((S >> v) & 1 and nb[v] & S for v in range(n)):
        continue
    if any(not (S >> v) & 1 and not nb[v] & S for v in range(n)):
        continue
    k = bin(S).count("1")
    sizes[k] = sizes.get(k, 0) + 1
M = sum(sizes.values())


# sequential model: exact law of the final size, by recursion over the set of available vertices
@lru_cache(maxsize=None)
def law(avail):
    if avail == 0:
        return {0: Fraction(1)}
    vs = [v for v in range(n) if (avail >> v) & 1]
    out = {}
    for v in vs:
        for k, p in law(avail & ~(1 << v) & ~nb[v]).items():
            out[k + 1] = out.get(k + 1, 0) + p / len(vs)
    return out


seq = law((1 << n) - 1)
print(f"maximal independent sets by size: {dict(sorted(sizes.items()))} (total {M})")
cs = cst = Fraction(0)
violated = []
for k in sorted(set(seq) | set(sizes)):
    cs += seq.get(k, 0)
    cst += Fraction(sizes.get(k, 0), M)
    flag = "" if cs <= cst else "   <-- violates the conjecture"
    if flag:
        violated.append(k)
    print(f"k={k}:  P[N_seq <= k] = {cs} ({float(cs):.6f})   P[N_stat <= k] = {cst} ({float(cst):.6f}){flag}")
print("PASS" if violated else "FAIL")
sys.exit(0 if violated else 1)
