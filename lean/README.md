# Lean 4 proofs

Machine-checked refutations of the conjectures in this repository, in Lean 4 with Mathlib.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain (`lean-toolchain`) and the Mathlib release (`lakefile.toml`, `lake-manifest.json`) are pinned:
Lean `v4.36.0`, Mathlib `v4.36.0` (commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).

```
cd lean
lake exe cache get    # prebuilt Mathlib: about 0.5 GB download, 7.3 GB unpacked
lake build
```

`lake build` compiles the files below in about two minutes and prints the axioms of every main theorem (`#print axioms`).
No file needs more than about 3.5 GB of memory.
The only warnings are Mathlib's advisory "designed for use with the module system" notes about imports.

## Standards

- Every statement is general (for all graphs, every `k`, …), worded as close to the source as we could. The counterexample appears only inside the proof.
- No proof uses `sorry`, `native_decide` or a new axiom.
- Every main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, Lean's three standard axioms, which all of Mathlib uses.
- Finite checks use `decide` (evaluated by the elaborator) or `decide +kernel` (evaluated by the kernel). Both are checked by the kernel and add no axiom.
- The rational certificates (LDLᵀ factorisations, test vectors, coefficient lists) and the case analyses were produced by small helper scripts. Lean checks all of them in exact arithmetic.

## Results

### 1. Hausmann, Question 5.4 (`Conjectures/Hausmann.lean`)

Theorem `Hausmann.question54_false : ¬ Hausmann.Question54`.

```lean
def Question54 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ 3) → HasOddGirth G 5 →
      ∃ L : Set V, G.IsIndepSet L ∧
        ∀ c : (G.induce Lᶜ).ConnectedComponent, c.supp.ncard ≤ 3
```

```
'Hausmann.question54_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Faithfulness:
- "subcubic graph G": a finite simple graph with `G.degree v ≤ 3` for every `v`.
- "odd girth exactly five": `HasOddGirth G 5`. Some cycle (`Walk.IsCycle`) has odd length 5, and every cycle of odd length has length at least 5.
- "a partition V(G) = L ∪ R such that L is independent": `R = Lᶜ` and `G.IsIndepSet L`, Mathlib's notion.
- "every component of G[R] has order at most three": every connected component of the induced graph `G.induce Lᶜ` has at most 3 vertices (`ConnectedComponent.supp`, `Set.ncard`).
- Counterexample: the Wagner graph on `Fin 8`, where `i ~ j` iff `j − i ≡ ±1` or `4 (mod 8)`. A generated case analysis covers the independent sets in 23 leaves. Each leaf finds either two adjacent vertices in `L` or a 4-vertex path outside `L`.

### 2. Higuita-Diaz, López, Roldán-Correa, Conjecture 5.2 (`Conjectures/RSA.lean` and `Conjectures/RSA/`)

Theorem `RSA.conjecture52_false : ¬ RSA.Conjecture52`.

```lean
def Conjecture52 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ 3) → ∀ k : ℕ, seqCDF G k ≤ statCDF G k
```

```
'RSA.conjecture52_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Faithfulness:
- "finite simple graph G with maximum degree Δ(G) ≤ 3": every degree is at most 3.
- "N_stat ≤st N_seq" (Definition 2.1): `P[N_seq ≤ k] ≤ P[N_stat ≤ k]` for every `k ∈ ℕ`. Both sizes are natural numbers, so other values of `k` add nothing.
- Sequential model: `seqLaw G j A` (`RSA/Basic.lean`) is the probability that the process, started from the available set `A`, ends with exactly `j` occupied vertices. It is defined by the one-step recursion of the process:
  - if `A` is empty, the process has stopped (`N = 0`);
  - otherwise a vertex `v ∈ A` is chosen with probability `1/|A|` and occupied, and `v` and its neighbours are removed from `A`.

  `seqCDF G k = Σ_{j ≤ k} seqLaw G j V`.
- Static model: `statCDF G k = #{maximal independent S : |S| ≤ k} / #{maximal independent S}`. Here "maximal" is `Maximal` for inclusion among Mathlib's `IsIndepSet`.
- Counterexample: the 15-vertex tree. Lean proves three facts:
  - `P[N_seq ≤ 6] ≥ 64/3375`, by summing only the runs that occupy `{0, 6, 7, 8, 13, 14}` (`RSA/Seq.lean`);
  - that set is the only maximal independent set with at most 6 vertices, by a generated case analysis with 200 leaves (`RSA/Static/Cases.lean`);
  - the tree has at least 55 maximal independent sets (`RSA/Static/List.lean`).

  Hence `P[N_stat ≤ 6] ≤ 1/55 < 64/3375`. The exact values are `64/3375` and `1/55`, but Lean proves only the two inequalities, which is all the refutation needs.

### 3. Cazenave, Conjecture 2 (`Conjectures/Cazenave.lean`)

Theorem `Cazenave.conjecture2_false : ¬ Cazenave.Conjecture2`.

```lean
def Conjecture2 : Prop :=
  ∀ (n : ℕ) (h : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → lambda2 G h ≤ mu1 G h - 2
-- lambda2 G h = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨1, _⟩
-- mu1 G h     = (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨0, _⟩
```

```
'Cazenave.conjecture2_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Faithfulness:
- "for every connected graph": every connected simple graph on `Fin n`. `λ₂` needs at least two vertices, hence `2 ≤ n`. Cazenave's own `Invariants.ofGraph` has the same hypothesis.
- `λ₂` and `μ₁` are defined as in Cazenave's `SpectralLean/Invariants.lean` (`l2 := adjEig G ⟨1, _⟩`, `mu1 := lapEig G ⟨0, _⟩`). Both are Mathlib's `eigenvalues₀`, the eigenvalues in decreasing order with multiplicity, of the real adjacency matrix and of the Laplacian `D − A`.
- Counterexample: `G(4,3)` on 11 vertices.
  - `μ₁ ≤ 4.62`, from an exact `LDLᵀ` certificate for `4.62 I − L`.
  - `λ₂ > 2.63`, because `A − 2.63 I` is positive definite on the span of two explicit rational vectors. The step from there to `λ₂` is a case of Courant–Fischer proved in `Spectral.lean`.

### 4. Caporossi–Chasset–Furtula, Conjecture 4 (`Conjectures/DistanceEnergy.lean`)

Theorems:
- `DistanceEnergy.conjecture_false : ¬ DistanceEnergy.Conjecture`, the conjecture as worded;
- `DistanceEnergy.conjectureMax_false : ¬ DistanceEnergy.ConjectureMax`, the form "PK(n, m) maximises E_D".

```lean
def Conjecture : Prop :=
  ∀ (n m : ℕ), m ≤ (n - 2) * (n - 3) / 2 →
    ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard = m →
      (∀ H : SimpleGraph (Fin n), H.Connected → H.edgeSet.ncard = m →
        distEnergy H ≤ distEnergy G) →
      ∃ k j : ℕ, IsPKParams n m k j ∧ Nonempty (G ≃g pathComplete n k j)

def ConjectureMax : Prop :=
  ∀ (n m : ℕ), m ≤ (n - 2) * (n - 3) / 2 →
    ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard = m →
      ∀ k j : ℕ, IsPKParams n m k j → distEnergy G ≤ distEnergy (pathComplete n k j)
```

```
'DistanceEnergy.conjecture_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'DistanceEnergy.conjectureMax_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Faithfulness:
- "a graph on n vertices and m ≤ (n−2)(n−3)/2 edges that maximises distance energy": a connected simple graph on `Fin n` with `m` edges whose distance energy is at least that of every connected graph on `Fin n` with `m` edges. Connectedness is implicit in the source, since the distance matrix needs it.
- "composed of a path appended to a clique with possibly some edges between vertices of the clique and the vertex of the path adjacent to the clique": isomorphic to `pathComplete n k j`, with `IsPKParams n m k j`, i.e. `2 ≤ k < n`, `1 ≤ j < k` and `k(k−1)/2 + (n−k−1) + j = m`.
  - `pathComplete n k j` is a clique on `0, …, k−1` plus a path `k, k+1, …, n−1`, with vertex `k` also joined to the clique vertices `0, …, j−1`.
- `distEnergy G = Σᵢ |λᵢ(D)|` for the real distance matrix `D i j = G.dist i j`, using Mathlib's `SimpleGraph.dist`.
- How the proof of `¬ Conjecture` goes:
  - a maximiser exists, since there are finitely many graphs on `Fin 12`;
  - `E_D` is invariant under isomorphism, proved via `charpoly_reindex`;
  - `(9, 6)` are the only parameters for `n = 12, m = 44`;
  - so a maximiser would satisfy `E_D = E_D(PK(12; 9, 6)) < E_D(G)`, which is impossible.
- Counterexample: `n = 12`, `m = 44`, `G` = `K₄,₄,₃` plus one vertex joined to a 4-part. Lean proves two bounds:
  - `E_D(G) ≥ tr(D S) = 37.0692` for an explicit rational `S` with `−I ⪯ S ⪯ I`;
  - `E_D(PK(12; 9, 6)) ≤ tr X + tr Y = 36.9424` for `D = X − Y` with rational `X, Y ⪰ 0`.

  Every positive-semidefiniteness claim is certified by an exact `Pᵀ diag(d) P` factorisation with `d ≥ 0`, and every distance by a checked breadth-first-search table.

### 6. Banerjee–Smoot, Conjecture 6.1 (1) (`Conjectures/ElevenAdic.lean`)

Theorems `ElevenAdic.conjecturePart1_false : ¬ ElevenAdic.ConjecturePart1` and `ElevenAdic.p1_value_dvd : 11 ∣ p1 36 54 ∧ ¬ 121 ∣ p1 36 54`, together with `ElevenAdic.p1_value : p1 36 54 = 62043410886974649205238011198`.

```lean
def ConjecturePart1 : Prop :=
  ∀ a : ℕ, (a % 11 = 3 ∨ a % 11 = 5 ∨ a % 11 = 7) → ∀ α : ℕ, 1 ≤ α → ∀ n δ : ℕ,
    (24 * δ : ℤ) ≡ 1 - a [ZMOD 11 ^ α] → (11 : ℤ) ^ ((α + 1) / 2) ∣ p1 a (11 ^ α * n + δ)
```

```
'ElevenAdic.conjecturePart1_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElevenAdic.p1_value_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Faithfulness:
- The series `∏_{n≥1} (1 + qⁿ)ᵃ / (1 − qⁿ)` lives in Mathlib's `PowerSeries ℤ`. `1/(1 − qⁿ)` is `geom n = Σₖ q^{nk}`, and `one_sub_mul_geom` proves `(1 − qⁿ) · geom n = 1`.
- The reduction we use is a theorem: `coeff_stable` shows that the coefficient of `q^N` is the same in every partial product `∏_{1 ≤ n ≤ M}` with `M ≥ N`, because each factor with `n > N` is `1 + q^{N+1}(…)`. This common value is the coefficient of `q^N` in the infinite product, and `p1 a N` is defined as it. The infinite product itself is not formalised.
- `a ∈ ℕ`: the paper allows every `a ∈ ℤ`, so our statement is weaker and its refutation also refutes the paper's. `α ∈ ℕ` means `α ≥ 1`, `n ∈ ℕ₀`, and `⌈α/2⌉ = (α + 1) / 2`. Allowing every `δ ≥ 0` with `24δ ≡ 1 − a (mod 11^α)` is equivalent to taking the least one, since `n` ranges over `ℕ₀`.
- The coefficient is computed exactly by list arithmetic, one factor at a time (54 kernel-checked steps), each step linked to the power series by `approx_step`.
- Counterexample: `a = 36 ≡ 3`, `α = 3`, `n = 0`, `δ = 54`. The conjecture asks that `121` divides `p1 36 54`; it is divisible by `11` but not by `121`.
- Only part (1) is formalised; part (2) is not.

Result 5 (`conjectures/cazenave-archive-5`) is not formalised.

## Shared files

- `Conjectures/Spectral.lean`: facts about `Matrix.IsHermitian.eigenvalues` of real symmetric matrices, proved from Mathlib's spectral theorem.
  - `x ⬝ A x = Σ λᵢ (uᵢ ⬝ x)²` and `Σᵢ uᵢ ⬝ M uᵢ = tr M` in the eigenbasis.
  - `eigenvalues₀_le_of_psd`: if `c I − A ⪰ 0`, every eigenvalue is at most `c`.
  - `lt_eigenvalues₀_one`: if `A − q I` is positive definite on a 2-dimensional subspace, the second largest eigenvalue exceeds `q`. This is the case of Courant–Fischer we need; Mathlib has no Courant–Fischer.
  - `trace_mul_le_sum_abs`: if `−I ⪯ S ⪯ I`, then `tr(A S) ≤ Σ |λᵢ|`.
  - `sum_abs_le_trace_add_trace`: if `A = X − Y` with `X, Y ⪰ 0`, then `Σ |λᵢ| ≤ tr X + tr Y`.
  - `psd_of_ldl`: a factorisation `M = Pᵀ diag(d) P` over `ℚ` with `d ≥ 0` makes `M` positive semidefinite over `ℝ`.
- `Conjectures/GraphCert.lean`: a breadth-first-search table certifies `SimpleGraph.dist` and connectivity.
