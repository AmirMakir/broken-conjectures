# Five more open statements from Cazenave's corpus are false

These statements come from the archive accompanying T. Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*, [arXiv:2611.03879](https://arxiv.org/abs/2611.03879). The archive's `index_conjectures.csv` (31 Oct 2026) marks each of them "ouverte" (open), with no counterexample. They are ordinary entries of the automatically generated corpus, not the conjectures the paper highlights.

Notation:
- λᵢ and μᵢ are the i-th largest adjacency and Laplacian eigenvalues.
- R is the Randić index.
- rad is the radius.
- rk is the rank of the adjacency matrix.
- log is the natural logarithm, as in the archive's definitions.

| ids | statement | graph6 | n | left side | right side |
|---|---|---|---|---|---|
| #861166 | rad ≤ 2(R − λ₂) | `I^}??KF@w` | 10 | 3 | 2.929875 |
| #1053490 | λ₂ ≤ R − rad/2 | `I^}??KF@w` | 10 | 3.517113 | 3.482051 |
| #2632674 | λ₂ ≤ R − √(rad − 1) | `K^~{??B?wF_^` | 12 | 4.587741 | 4.574641 |
| #753029 | μ₂ ≤ 1 + 2^λ₁ | `N?B{?C@?G????????Bw` | 15 | 6.054084 | 6.017074 |
| #121183, #123215, #715458 | λ₂ ≤ (log rk)^(R/2), written three ways | `J?{G?????N_` | 11 | 2 | 1.988920 |

The graphs:
- The 10-vertex graph is two copies of K₅ − e joined by an edge between endpoints of the missing edges.
- The 12-vertex graph is the same construction with K₆ − e.
- The 11- and 15-vertex graphs are trees, each made of two copies of a small tree joined by a path.

All 115,229 statements the archive marks as proved hold on each of these graphs, so none of them implies a statement refuted here. We did not check whether a statement the archive marks as refuted is weaker than one of these.

**Verify.** Run `python3 verify.py`. It uses the standard library only.
- Eigenvalues are bracketed exactly with Sylvester inertia over the rationals.
- Square roots, logarithms and exponentials use 60-digit `Decimal`, with a 10⁻⁴⁰ safety margin.
