# Lean 4 proofs

Machine-checked refutations of the conjectures in this repository, in Lean 4 with Mathlib.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain (`lean-toolchain`) and the Mathlib release (`lakefile.toml`) are pinned:
Lean `v4.36.0`, Mathlib `v4.36.0` (commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).

```
cd lean
lake exe cache get    # prebuilt Mathlib, about 0.5 GB download, 7 GB unpacked
lake build
```

`lake build` compiles the files below and prints the axioms of every main theorem (`#print axioms`).

## Results

Every statement is general (for all graphs, every `k`, …), written as close to the source's wording as we could, and the counterexample appears only inside the proof.
No proof uses `sorry`, `native_decide` or any new axiom.
`propext`, `Classical.choice` and `Quot.sound` are Lean's three standard axioms, used throughout Mathlib.
Finite checks use `decide` (elaborator) or `decide +kernel` (evaluated by the kernel); both are kernel-checked and add no axiom.

| Result | Lean theorem | Status |
|---|---|---|
| [Distance energy, 2009](../conjectures/distance-energy-2009/) | `DistanceEnergy.conjecture_false`, `DistanceEnergy.conjectureMax_false` in [DistanceEnergy.lean](Conjectures/DistanceEnergy.lean) | proved |
| [λ₂ ≤ μ₁ − 2, Cazenave Conj. 2](../conjectures/cazenave-conjecture-2/) | `Cazenave.conjecture2_false` in [Cazenave.lean](Conjectures/Cazenave.lean) | proved |
| [Hausmann, Question 5.4](../conjectures/hausmann-question-5.4/) | `Hausmann.question54_false` in [Hausmann.lean](Conjectures/Hausmann.lean) | proved |
| [RSA vs. uniform jamming, Conj. 5.2](../conjectures/rsa-jamming-2611.14718/) | | in progress |
| [11-adic congruences, Conj. 6.1](../conjectures/eleven-adic-2611.09681/) | | in progress |
| [Five corpus statements](../conjectures/cazenave-archive-5/) | | not formalised (exact Python check only) |

The three proved theorems depend on the axioms `[propext, Classical.choice, Quot.sound]` and nothing else; `#print axioms` output from Lean v4.36.0 with Mathlib v4.36.0.

## Shared files

- `Conjectures/Spectral.lean`: facts about `Matrix.IsHermitian.eigenvalues` of real symmetric matrices, proved from Mathlib's spectral theorem.
  - `x ⬝ A x = Σ λᵢ (uᵢ ⬝ x)²` and `Σᵢ uᵢ ⬝ M uᵢ = tr M` in the eigenbasis.
  - `eigenvalues₀_le_of_psd`: `c I − A ⪰ 0` implies every eigenvalue is at most `c`.
  - `lt_eigenvalues₀_one`: if `A − q I` is positive definite on a 2-dimensional subspace, the second largest eigenvalue exceeds `q` (the case of Courant–Fischer we need; Mathlib has no Courant–Fischer).
  - `trace_mul_le_sum_abs`: `−I ⪯ S ⪯ I` implies `tr(A S) ≤ Σ |λᵢ|`.
  - `sum_abs_le_trace_add_trace`: `A = X − Y` with `X, Y ⪰ 0` implies `Σ |λᵢ| ≤ tr X + tr Y`.
  - `psd_of_ldl`: a factorisation `M = Pᵀ diag(d) P` over `ℚ` with `d ≥ 0` makes `M` positive semidefinite over `ℝ`.
- `Conjectures/GraphCert.lean`: a breadth-first-search table certifies `SimpleGraph.dist` and connectivity.

The rational certificates (LDLᵀ factorisations, test vectors) were computed with exact fractions by a helper script and are checked in Lean in exact rational arithmetic.
