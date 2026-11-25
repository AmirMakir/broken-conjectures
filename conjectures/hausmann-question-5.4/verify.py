#!/usr/bin/env python3
"""Exact check: the answer to Question 5.4 of W. Hausmann, "Weighted Max Cut in Subcubic Graphs",
arXiv:2611.05178, is "no".

Question 5.4: does every subcubic graph G of odd girth exactly five admit a partition V(G) = L u R such that
L is independent and every component of G[R] has order at most three?

Counterexample: the Wagner graph V8 (8-cycle plus its 4 long diagonals). It is cubic with odd girth 5, and
every independent set L leaves a component of order at least 4.

Run: python3 verify.py      (Python 3.8+, standard library only)
"""
import sys
from itertools import combinations

n = 8
E = {frozenset((i, (i + 1) % 8)) for i in range(8)} | {frozenset((i, i + 4)) for i in range(4)}
adj = {v: {w for e in E if v in e for w in e if w != v} for v in range(n)}
assert all(len(adj[v]) == 3 for v in range(n)), "not cubic"


def odd_girth():
    best = None
    for s in range(n):
        dist = {s: 0}
        queue = [s]
        for v in queue:
            for w in adj[v]:
                if w not in dist:
                    dist[w] = dist[v] + 1
                    queue.append(w)
        for e in E:
            a, b = tuple(e)
            if dist[a] == dist[b]:  # an odd closed walk of length 2d+1 through s
                c = 2 * dist[a] + 1
                best = c if best is None else min(best, c)
    return best


def largest_component(R):
    R, big = set(R), 0
    while R:
        stack = [R.pop()]
        size = 1
        while stack:
            v = stack.pop()
            for w in adj[v] & R:
                R.remove(w)
                stack.append(w)
                size += 1
        big = max(big, size)
    return big


g = odd_girth()
best = min((largest_component(set(range(n)) - set(L)), L)
           for k in range(n + 1) for L in combinations(range(n), k)
           if not any(frozenset(p) in E for p in combinations(L, 2)))
print(f"Wagner graph: cubic, odd girth {g}")
print(f"over all independent sets L, the smallest possible largest component of G - L is {best[0]} (e.g. L = {set(best[1])})")
ok = g == 5 and best[0] > 3
print("answer to Question 5.4: NO" if ok else "not a counterexample")
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
