import Conjectures.Spectral
import Conjectures.GraphCert
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# `λ₂(A) ≤ μ₁(L) − 2` is false: Conjecture 2 of arXiv:2611.03879

T. Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*, arXiv:2611.03879, Section 7,
Conjecture 2 (corpus id #20829):

> For every connected graph, λ₂ ≤ μ₁ − 2.

`λ₂` is the second largest eigenvalue of the adjacency matrix and `μ₁` the largest eigenvalue of
the Laplacian, both counted with multiplicity. Following Cazenave's own Lean files
(`SpectralLean/Invariants.lean`: `l2 := adjEig G ⟨1, _⟩`, `mu1 := lapEig G ⟨0, _⟩`), they are
`Matrix.IsHermitian.eigenvalues₀` (eigenvalues sorted in decreasing order) at indices `1` and `0`,
for a graph on `Fin n` with `n ≥ 2`.

Counterexample `G(4,3)`: two diamonds `K₄ − e` whose tips are joined by a path with 3 inner
vertices (11 vertices). Certificates, all checked in exact rational arithmetic:
* `μ₁ ≤ 231/50 = 4.62`: `(231/50) I − L = Pᵀ diag(d) P` with `d ≥ 0`;
* `λ₂ > 263/100 = 2.63`: `A − 2.63 I` is positive definite on the span of two explicit vectors.
Hence `λ₂ > 2.63 > 2.62 ≥ μ₁ − 2`.
-/

namespace Cazenave

open Matrix SimpleGraph Spectral

/-- `λ₂`: the second largest adjacency eigenvalue, counted with multiplicity. -/
noncomputable def lambda2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n) :
    ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨1, by simp; omega⟩

/-- `μ₁`: the largest Laplacian eigenvalue. -/
noncomputable def mu1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n) : ℝ :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨0, by simp; omega⟩

/-- **Conjecture 2 of arXiv:2611.03879**: for every connected graph, `λ₂ ≤ μ₁ − 2`. -/
def Conjecture2 : Prop :=
  ∀ (n : ℕ) (h : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → lambda2 G h ≤ mu1 G h - 2

/-! ### The counterexample `G(4,3)` -/

/-- Diamonds on `{0,1,2,3}` and `{4,5,6,7}` (tips `0, 3` and `4, 7`), path `3 - 8 - 9 - 10 - 4`. -/
def edgeList : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (4, 5), (4, 6), (5, 6), (5, 7), (6, 7), (3, 8), (8, 9), (9, 10), (10, 4)]

def G43 : SimpleGraph (Fin 11) where
  Adj i j := (i.val, j.val) ∈ edgeList ∨ (j.val, i.val) ∈ edgeList
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G43.Adj := fun i j => by unfold G43; infer_instance

/-- Breadth-first-search depth from vertex `0`. -/
def depth : Fin 11 → ℕ := ![0, 1, 1, 2, 6, 7, 7, 8, 3, 4, 5]

theorem G43_connected : G43.Connected :=
  GraphCert.connected_of_parent G43 0 depth rfl (by decide +kernel)

theorem lapMatrix_real : G43.lapMatrix ℝ = (G43.lapMatrix ℚ).map (Rat.castHom ℝ) := by
  ext i j
  simp only [lapMatrix, degMatrix, adjMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem adjMatrix_real : G43.adjMatrix ℝ = (G43.adjMatrix ℚ).map (Rat.castHom ℝ) := by
  ext i j
  simp only [adjMatrix_apply, Matrix.map_apply]
  split_ifs <;> simp

/-! #### `μ₁ ≤ 231/50` -/

def PL : Matrix (Fin 11) (Fin 11) ℚ :=
  !![1, 50/131, 50/131, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 4050/8111, 6550/8111, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 6550/12161, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 608050/330041, 0, 0;
    0, 0, 0, 0, 1, 50/81, 50/81, 0, 0, 0, 50/81;
    0, 0, 0, 0, 0, 1, 50/131, 4050/4061, 0, 0, -2500/4061;
    0, 0, 0, 0, 0, 0, 1, 4050/5611, 0, 0, -2500/5611;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 250000/330041;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 16502050/12832871, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 641643550/856003601;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def dL : Fin 11 → ℚ := ![131/50, 8111/6550, 376991/405550, 330041/608050, 81/50, 4061/4050, 5611/6550, 330041/280550, 12832871/16502050, 856003601/641643550, 396549842890971/14125814223882050]

theorem lap_ldl : (231 / 50 : ℚ) • (1 : Matrix (Fin 11) (Fin 11) ℚ) - G43.lapMatrix ℚ =
    PLᵀ * diagonal dL * PL := by
  decide +kernel

theorem dL_nonneg : ∀ i, 0 ≤ dL i := by decide +kernel

theorem h11 : 2 ≤ 11 := by norm_num

theorem mu1_le : mu1 G43 h11 ≤ 231 / 50 := by
  unfold mu1
  apply Spectral.eigenvalues₀_le_of_psd
  intro x
  have : (231 / 50 : ℝ) • (1 : Matrix (Fin 11) (Fin 11) ℝ) - G43.lapMatrix ℝ =
      (PLᵀ * diagonal dL * PL).map (Rat.castHom ℝ) := by
    rw [← lap_ldl, lapMatrix_real]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [this]
  exact psd_of_ldl PL dL dL_nonneg x

/-! #### `λ₂ > 263/100` -/

def w₁ : Fin 11 → ℚ := ![137/50, 367/100, 367/100, 17/5, 17/5, 367/100, 367/100, 137/50, 177/100, 33/25, 177/100]

def w₂ : Fin 11 → ℚ := ![72/25, 19/5, 19/5, 84/25, -84/25, -19/5, -19/5, -72/25, 127/100, 0, -127/100]

theorem gram_values :
    w₁ ⬝ᵥ (G43.adjMatrix ℚ *ᵥ w₁) = 668909/2500 ∧ w₁ ⬝ᵥ (G43.adjMatrix ℚ *ᵥ w₂) = 0 ∧
    w₂ ⬝ᵥ (G43.adjMatrix ℚ *ᵥ w₂) = 165328/625 ∧ w₁ ⬝ᵥ w₁ = 100019/1000 ∧
    w₁ ⬝ᵥ w₂ = 0 ∧ w₂ ⬝ᵥ w₂ = 500769/5000 := by
  decide +kernel

theorem lambda2_gt : 263 / 100 < lambda2 G43 h11 := by
  unfold lambda2
  refine Spectral.lt_eigenvalues₀_one (G43.isHermitian_adjMatrix ℝ) _ (263 / 100)
    (fun i => (w₁ i : ℝ)) (fun i => (w₂ i : ℝ)) fun a b hab => ?_
  have hsymm : (G43.adjMatrix ℝ)ᵀ = G43.adjMatrix ℝ :=
    Spectral.transpose_eq_self (G43.isHermitian_adjMatrix ℝ)
  rw [gram_expand hsymm, adjMatrix_real, cast_dot_mulVec, cast_dot_mulVec, cast_dot_mulVec,
    cast_dot, cast_dot, cast_dot]
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := gram_values
  rw [e1, e2, e3, e4, e5, e6]
  have := quad2_pos (668909/2500 - 263 / 100 * 100019/1000) (0 - 263 / 100 * 0)
    (165328/625 - 263 / 100 * 500769/5000) a b (by norm_num) (by norm_num) hab
  push_cast
  linarith

/-- **Conjecture 2 of arXiv:2611.03879 is false**, on `G(4,3)`:
`λ₂ > 2.63 > 2.62 ≥ μ₁ − 2`. -/
theorem conjecture2_false : ¬ Conjecture2 := by
  intro h
  have := h 11 h11 G43 G43_connected
  have h1 := lambda2_gt
  have h2 := mu1_le
  linarith

end Cazenave

#print axioms Cazenave.conjecture2_false
