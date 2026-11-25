"""Exact tools shared by every verifier. Python standard library only.

Eigenvalues are never computed in floating point. Instead, for a symmetric integer matrix M and a rational t,
Sylvester's law of inertia gives the exact number of eigenvalues of M greater than t: run an LDL^T
factorisation of M - tI over the rationals and count the positive pivots. Bisection with such counts brackets
any eigenvalue in a rational interval as narrow as we like.
"""
from fractions import Fraction


def graph6(s):
    """Decode a graph6 string (n < 63) into an adjacency matrix (list of lists of 0/1)."""
    n = ord(s[0]) - 63
    bits = "".join(format(ord(c) - 63, "06b") for c in s[1:])
    A = [[0] * n for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k] == "1":
                A[i][j] = A[j][i] = 1
            k += 1
    return A


def from_edges(n, edges):
    A = [[0] * n for _ in range(n)]
    for a, b in edges:
        A[a][b] = A[b][a] = 1
    return A


def degrees(A):
    return [sum(r) for r in A]


def laplacian(A):
    d = degrees(A)
    return [[(d[i] if i == j else 0) - A[i][j] for j in range(len(A))] for i in range(len(A))]


def distances(A):
    """All-pairs shortest-path distances (BFS); raises if the graph is disconnected."""
    n = len(A)
    D = []
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        queue = [s]
        for v in queue:
            for w in range(n):
                if A[v][w] and dist[w] < 0:
                    dist[w] = dist[v] + 1
                    queue.append(w)
        if min(dist) < 0:
            raise ValueError("graph is disconnected")
        D.append(dist)
    return D


def count_above(M, t):
    """Exact number of eigenvalues of the symmetric matrix M that are > t, or None if t hits a zero pivot."""
    n = len(M)
    t = Fraction(t)
    X = [[Fraction(M[i][j]) - (t if i == j else 0) for j in range(n)] for i in range(n)]
    pos = 0
    for p in range(n):
        piv = X[p][p]
        if piv == 0:
            return None
        if piv > 0:
            pos += 1
        for i in range(p + 1, n):
            f = X[i][p] / piv
            if f:
                row_p, row_i = X[p], X[i]
                for j in range(p + 1, n):
                    row_i[j] -= f * row_p[j]
    return pos


def safe_count(M, t):
    """count_above, nudging t by a tiny rational if it lands exactly on a zero pivot."""
    t = Fraction(t)
    k = 0
    while True:
        c = count_above(M, t)
        if c is not None:
            return c, t
        k += 1
        t += Fraction(1, 10 ** (12 + k))


def eigen_brackets(M, tol=Fraction(1, 10 ** 9)):
    """Rational intervals (lo, hi, multiplicity) that contain all eigenvalues of M, each of width < tol.
    Every eigenvalue lies in exactly one interval; the multiplicity is the number of eigenvalues inside."""
    n = len(M)
    bound = max(sum(abs(x) for x in row) for row in M) + 1  # Gershgorin
    lo, hi = Fraction(-bound), Fraction(bound)
    stack = [(lo, n, hi, 0)]  # (lo, #eigs > lo, hi, #eigs > hi)
    out = []
    while stack:
        a, ca, b, cb = stack.pop()
        k = ca - cb
        if k == 0:
            continue
        if b - a < tol:
            out.append((a, b, k))
            continue
        cm, m = safe_count(M, (a + b) / 2)
        if m <= a or m >= b:
            raise RuntimeError("bisection failed")
        stack.append((a, ca, m, cm))
        stack.append((m, cm, b, cb))
    return sorted(out, key=lambda x: -x[0])  # largest first


def kth_largest(M, k, tol=Fraction(1, 10 ** 9)):
    """Rational interval (lo, hi) that contains the k-th largest eigenvalue of M (counted with multiplicity)."""
    seen = 0
    for lo, hi, mult in eigen_brackets(M, tol):
        seen += mult
        if seen >= k:
            return lo, hi
    raise ValueError("k too large")


def rank(M):
    """Exact rank over the rationals."""
    X = [[Fraction(x) for x in row] for row in M]
    r, rows, cols = 0, len(X), len(X[0])
    for c in range(cols):
        p = next((i for i in range(r, rows) if X[i][c] != 0), None)
        if p is None:
            continue
        X[r], X[p] = X[p], X[r]
        for i in range(rows):
            if i != r and X[i][c] != 0:
                f = X[i][c] / X[r][c]
                X[i] = [a - f * b for a, b in zip(X[i], X[r])]
        r += 1
    return r


def fmt(x, digits=6):
    return f"{float(x):.{digits}f}"
