import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Rat.Cast.Order

/-!
# Spectral lemmas for real symmetric matrices

Small facts about `Matrix.IsHermitian.eigenvalues` and `eigenvectorBasis` for real matrices,
used to bound eigenvalues by exact rational certificates:

* `quad_eq_sum` : `x ⬝ᵥ A x = ∑ᵢ λᵢ (uᵢ ⬝ᵥ x)²` and `dot_self_eq_sum` : `x ⬝ᵥ x = ∑ᵢ (uᵢ ⬝ᵥ x)²`;
* `sum_quad_eq_trace` : `∑ᵢ uᵢ ⬝ᵥ M uᵢ = tr M` for any matrix `M`;
* `eigenvalues₀_le_of_psd` : if `c I - A ⪰ 0` then every eigenvalue is `≤ c`;
* `lt_eigenvalues₀_one` : a 2-dimensional subspace on which `A - q I` is positive definite forces
  the second largest eigenvalue to exceed `q` (the case of Courant–Fischer that we need);
* `trace_mul_le_sum_abs` and `sum_abs_le_trace_add_trace` : the two trace-norm bounds;
* `psd_of_ldl` : a factorisation `M = Pᵀ diag(d) P` over `ℚ` with `d ≥ 0` makes `M` positive
  semidefinite over `ℝ`.
-/

namespace Spectral

open Matrix

section Basic

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-- The `i`-th eigenvector, as a plain vector. -/
noncomputable def u (i : n) : n → ℝ := ⇑(hA.eigenvectorBasis i)

/-- The orthogonal matrix whose columns are the eigenvectors. -/
noncomputable def U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)

lemma U_apply (k i : n) : U hA k i = u hA i k := rfl

omit [Fintype n] [DecidableEq n] in
lemma transpose_eq_self {B : Matrix n n ℝ} (hB : B.IsHermitian) : Bᵀ = B := by
  have := hB.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma star_U : star (U hA) = (U hA)ᵀ := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

lemma Ut_mul_U : (U hA)ᵀ * U hA = 1 := by
  rw [← star_U]
  exact mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2

lemma U_mul_Ut : U hA * (U hA)ᵀ = 1 := by
  rw [← star_U]
  exact mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2

lemma mulVec_u (i : n) : A *ᵥ u hA i = hA.eigenvalues i • u hA i :=
  hA.mulVec_eigenvectorBasis i

lemma dot_u (i j : n) : u hA i ⬝ᵥ u hA j = if i = j then 1 else 0 := by
  have := congrArg (fun N : Matrix n n ℝ => N i j) (Ut_mul_U hA)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, U_apply, Matrix.one_apply] at this
  simpa [dotProduct] using this

lemma dot_u_self (i : n) : u hA i ⬝ᵥ u hA i = 1 := by
  simp [dot_u]

/-- Coordinates in the eigenbasis. -/
lemma Ut_mulVec (x : n → ℝ) (i : n) : ((U hA)ᵀ *ᵥ x) i = u hA i ⬝ᵥ x := by
  simp only [mulVec_apply_eq_sum, dotProduct, Matrix.transpose_apply, U_apply]

lemma A_mul_U : A * U hA = U hA * diagonal hA.eigenvalues := by
  ext k i
  have h := congrArg (fun v => v k) (mulVec_u hA i)
  simp only [mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] at h
  rw [mul_diagonal, Matrix.mul_apply, U_apply]
  simp only [U_apply]
  rw [h, mul_comm]

omit [DecidableEq n] in
/-- `(M v) ⬝ w = v ⬝ (Mᵀ w)`. -/
lemma mulVec_dot (M : Matrix n n ℝ) (v w : n → ℝ) : (M *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Mᵀ *ᵥ w) := by
  rw [dotProduct_comm (M *ᵥ v) w, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

lemma x_eq (x : n → ℝ) : U hA *ᵥ ((U hA)ᵀ *ᵥ x) = x := by
  rw [mulVec_mulVec, U_mul_Ut, one_mulVec]

theorem quad_eq_sum (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * (u hA i ⬝ᵥ x) ^ 2 := by
  have hc : ∀ i, ((U hA)ᵀ *ᵥ x) i = u hA i ⬝ᵥ x := Ut_mulVec hA x
  obtain ⟨c, hcdef⟩ : ∃ c, c = (U hA)ᵀ *ᵥ x := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hx : x = U hA *ᵥ c := by rw [hcdef, x_eq]
  have h1 : A *ᵥ (U hA *ᵥ c) = U hA *ᵥ (diagonal hA.eigenvalues *ᵥ c) := by
    rw [mulVec_mulVec c A (U hA), A_mul_U, ← mulVec_mulVec c (U hA) (diagonal _)]
  have h2 : (U hA *ᵥ c) ⬝ᵥ (U hA *ᵥ (diagonal hA.eigenvalues *ᵥ c)) =
      c ⬝ᵥ (diagonal hA.eigenvalues *ᵥ c) := by
    rw [mulVec_dot, mulVec_mulVec (diagonal hA.eigenvalues *ᵥ c) (U hA)ᵀ (U hA), Ut_mul_U,
      one_mulVec]
  calc x ⬝ᵥ (A *ᵥ x) = (U hA *ᵥ c) ⬝ᵥ (A *ᵥ (U hA *ᵥ c)) := by rw [← hx]
    _ = c ⬝ᵥ (diagonal hA.eigenvalues *ᵥ c) := by rw [h1, h2]
    _ = ∑ i, hA.eigenvalues i * c i ^ 2 := by
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, hA.eigenvalues i * (u hA i ⬝ᵥ x) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hc i]

theorem dot_self_eq_sum (x : n → ℝ) : x ⬝ᵥ x = ∑ i, (u hA i ⬝ᵥ x) ^ 2 := by
  have hc : ∀ i, ((U hA)ᵀ *ᵥ x) i = u hA i ⬝ᵥ x := Ut_mulVec hA x
  obtain ⟨c, hcdef⟩ : ∃ c, c = (U hA)ᵀ *ᵥ x := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hx : x = U hA *ᵥ c := by rw [hcdef, x_eq]
  have h2 : (U hA *ᵥ c) ⬝ᵥ (U hA *ᵥ c) = c ⬝ᵥ c := by
    rw [mulVec_dot, mulVec_mulVec c (U hA)ᵀ (U hA), Ut_mul_U, one_mulVec]
  calc x ⬝ᵥ x = (U hA *ᵥ c) ⬝ᵥ (U hA *ᵥ c) := by rw [← hx]
    _ = c ⬝ᵥ c := h2
    _ = ∑ i, c i ^ 2 := by
      simp only [dotProduct]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, (u hA i ⬝ᵥ x) ^ 2 := Finset.sum_congr rfl fun i _ => by rw [hc i]

/-- `∑ᵢ uᵢ ⬝ᵥ M uᵢ = tr M` for any matrix `M`. -/
theorem sum_quad_eq_trace (M : Matrix n n ℝ) : ∑ i, u hA i ⬝ᵥ (M *ᵥ u hA i) = M.trace := by
  have hUU : ∀ k l, ∑ i, u hA i k * u hA i l = if k = l then 1 else 0 := by
    intro k l
    have := congrArg (fun N : Matrix n n ℝ => N k l) (U_mul_Ut hA)
    simpa [Matrix.mul_apply, Matrix.transpose_apply, U_apply, Matrix.one_apply] using this
  calc ∑ i, u hA i ⬝ᵥ (M *ᵥ u hA i) = ∑ i, ∑ k, ∑ l, M k l * (u hA i k * u hA i l) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [dotProduct, mulVec_apply_eq_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ k, ∑ i, ∑ l, M k l * (u hA i k * u hA i l) := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, M k l * (u hA i k * u hA i l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, M k l * ∑ i, u hA i k * u hA i l := by simp only [Finset.mul_sum]
    _ = M.trace := by
        simp only [hUU, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          Matrix.trace, Matrix.diag]

lemma quad_u (M : Matrix n n ℝ) (c : ℝ) (i : n) :
    u hA i ⬝ᵥ ((c • 1 - M) *ᵥ u hA i) = c - u hA i ⬝ᵥ (M *ᵥ u hA i) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, dot_u_self,
    smul_eq_mul, mul_one]

lemma quad_u_A (i : n) : u hA i ⬝ᵥ (A *ᵥ u hA i) = hA.eigenvalues i := by
  rw [mulVec_u, dotProduct_smul, dot_u_self, smul_eq_mul, mul_one]

/-- If `c I - A` is positive semidefinite, every eigenvalue of `A` is at most `c`. -/
theorem eigenvalues_le_of_psd (c : ℝ) (h : ∀ x, 0 ≤ x ⬝ᵥ ((c • 1 - A) *ᵥ x)) (i : n) :
    hA.eigenvalues i ≤ c := by
  have := h (u hA i)
  rw [quad_u, quad_u_A] at this
  linarith

lemma eigenvalues₀_eq (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k = hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) k) := by
  simp [IsHermitian.eigenvalues]

theorem eigenvalues₀_le_of_psd (c : ℝ) (h : ∀ x, 0 ≤ x ⬝ᵥ ((c • 1 - A) *ᵥ x))
    (k : Fin (Fintype.card n)) : hA.eigenvalues₀ k ≤ c := by
  rw [eigenvalues₀_eq]
  exact eigenvalues_le_of_psd hA c h _

/-- **Second eigenvalue from a 2-dimensional test space.** If `x ⬝ (A - q I) x > 0` for every
nonzero `x` in the span of `w₁, w₂`, then the second largest eigenvalue of `A` exceeds `q`. -/
theorem lt_eigenvalues₀_one (h1 : 1 < Fintype.card n) (q : ℝ) (w₁ w₂ : n → ℝ)
    (hpos : ∀ a b : ℝ, ¬ (a = 0 ∧ b = 0) →
      0 < (a • w₁ + b • w₂) ⬝ᵥ (A *ᵥ (a • w₁ + b • w₂)) -
        q * ((a • w₁ + b • w₂) ⬝ᵥ (a • w₁ + b • w₂))) :
    q < hA.eigenvalues₀ ⟨1, h1⟩ := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let i₀ : n := e ⟨0, by omega⟩
  -- a nonzero combination orthogonal to the top eigenvector
  obtain ⟨a, b, hab, horth⟩ : ∃ a b : ℝ, ¬ (a = 0 ∧ b = 0) ∧
      a * (u hA i₀ ⬝ᵥ w₁) + b * (u hA i₀ ⬝ᵥ w₂) = 0 := by
    by_cases h : u hA i₀ ⬝ᵥ w₁ = 0 ∧ u hA i₀ ⬝ᵥ w₂ = 0
    · exact ⟨1, 0, by simp, by simp [h.1]⟩
    · exact ⟨u hA i₀ ⬝ᵥ w₂, -(u hA i₀ ⬝ᵥ w₁), fun h' => h ⟨neg_eq_zero.1 h'.2, h'.1⟩, by ring⟩
  have hq := hpos a b hab
  have hx0 : u hA i₀ ⬝ᵥ (a • w₁ + b • w₂) = 0 := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact horth
  obtain ⟨x, hxdef⟩ : ∃ x, x = a • w₁ + b • w₂ := ⟨_, rfl⟩
  rw [← hxdef] at hq hx0
  have hle : ∀ i, hA.eigenvalues i * (u hA i ⬝ᵥ x) ^ 2 ≤
      hA.eigenvalues₀ ⟨1, h1⟩ * (u hA i ⬝ᵥ x) ^ 2 := by
    intro i
    by_cases hi : i = i₀
    · rw [hi, hx0]
      simp
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hne : e.symm i ≠ ⟨0, by omega⟩ := by
        intro h
        have : i = e (e.symm i) := (e.apply_symm_apply i).symm
        rw [h] at this
        exact hi this
      have h1le : (⟨1, h1⟩ : Fin (Fintype.card n)) ≤ e.symm i := by
        rw [Fin.le_def]
        have : (e.symm i).val ≠ 0 := fun h => hne (Fin.ext h)
        show 1 ≤ (e.symm i).val
        omega
      exact hA.eigenvalues₀_antitone h1le
  rw [quad_eq_sum hA x, dot_self_eq_sum hA x] at hq
  have hsum : ∑ i, hA.eigenvalues i * (u hA i ⬝ᵥ x) ^ 2 ≤
      hA.eigenvalues₀ ⟨1, h1⟩ * ∑ i, (u hA i ⬝ᵥ x) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hle i
  have hnn : 0 ≤ ∑ i, (u hA i ⬝ᵥ x) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **Trace-norm lower bound.** If `-I ⪯ S ⪯ I` then `tr(A S) ≤ ∑ |λᵢ(A)|`. -/
theorem trace_mul_le_sum_abs (S : Matrix n n ℝ) (h₁ : ∀ x, 0 ≤ x ⬝ᵥ ((1 - S) *ᵥ x))
    (h₂ : ∀ x, 0 ≤ x ⬝ᵥ ((1 + S) *ᵥ x)) : (A * S).trace ≤ ∑ i, |hA.eigenvalues i| := by
  rw [← sum_quad_eq_trace hA]
  refine Finset.sum_le_sum fun i _ => ?_
  have hs : u hA i ⬝ᵥ ((A * S) *ᵥ u hA i) =
      hA.eigenvalues i * (u hA i ⬝ᵥ (S *ᵥ u hA i)) := by
    rw [← mulVec_mulVec, dotProduct_comm, mulVec_dot, transpose_eq_self hA, mulVec_u,
      dotProduct_smul, smul_eq_mul, dotProduct_comm]
  rw [hs]
  have a1 := h₁ (u hA i)
  have a2 := h₂ (u hA i)
  rw [sub_mulVec, one_mulVec, dotProduct_sub, dot_u_self] at a1
  rw [add_mulVec, one_mulVec, dotProduct_add, dot_u_self] at a2
  have habs : |u hA i ⬝ᵥ (S *ᵥ u hA i)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  calc hA.eigenvalues i * (u hA i ⬝ᵥ (S *ᵥ u hA i))
      ≤ |hA.eigenvalues i * (u hA i ⬝ᵥ (S *ᵥ u hA i))| := le_abs_self _
    _ = |hA.eigenvalues i| * |u hA i ⬝ᵥ (S *ᵥ u hA i)| := abs_mul _ _
    _ ≤ |hA.eigenvalues i| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = |hA.eigenvalues i| := mul_one _

/-- **Trace-norm upper bound.** If `A = X - Y` with `X, Y ⪰ 0` then `∑ |λᵢ(A)| ≤ tr X + tr Y`. -/
theorem sum_abs_le_trace_add_trace (X Y : Matrix n n ℝ) (hXY : A = X - Y)
    (hX : ∀ x, 0 ≤ x ⬝ᵥ (X *ᵥ x)) (hY : ∀ x, 0 ≤ x ⬝ᵥ (Y *ᵥ x)) :
    ∑ i, |hA.eigenvalues i| ≤ X.trace + Y.trace := by
  rw [← sum_quad_eq_trace hA X, ← sum_quad_eq_trace hA Y, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := quad_u_A hA i
  have hv : ∀ v, A *ᵥ v = X *ᵥ v - Y *ᵥ v := fun v => by rw [hXY, sub_mulVec]
  rw [hv, dotProduct_sub] at h
  have := hX (u hA i)
  have := hY (u hA i)
  rw [← h]
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Basic

section Certificates

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- A factorisation `M = Pᵀ diag(d) P` over `ℚ` with `d ≥ 0` certifies that `M`, read over `ℝ`, is
positive semidefinite. -/
theorem psd_of_ldl (P : Matrix m n ℚ) (d : m → ℚ) (hd : ∀ i, 0 ≤ d i) (x : n → ℝ) :
    0 ≤ x ⬝ᵥ ((Pᵀ * diagonal d * P).map (Rat.castHom ℝ) *ᵥ x) := by
  set P' := P.map (Rat.castHom ℝ)
  have hmap : (Pᵀ * diagonal d * P).map (Rat.castHom ℝ) =
      P'ᵀ * diagonal (fun i => (d i : ℝ)) * P' := by
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, diagonal_map (by simp)]
    rfl
  rw [hmap, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_nonneg fun i _ => by
    have := hd i
    have : (0 : ℝ) ≤ d i := by exact_mod_cast this
    nlinarith [sq_nonneg ((P' *ᵥ x) i)]

omit [DecidableEq m] in
/-- Expansion of `x ⬝ (A x) - q (x ⬝ x)` on `x = a v + b w`, for symmetric `A`. -/
theorem gram_expand {A : Matrix m m ℝ} (hA : Aᵀ = A) (q a b : ℝ) (v w : m → ℝ) :
    (a • v + b • w) ⬝ᵥ (A *ᵥ (a • v + b • w)) - q * ((a • v + b • w) ⬝ᵥ (a • v + b • w)) =
      a ^ 2 * (v ⬝ᵥ (A *ᵥ v) - q * (v ⬝ᵥ v)) + 2 * a * b * (v ⬝ᵥ (A *ᵥ w) - q * (v ⬝ᵥ w)) +
        b ^ 2 * (w ⬝ᵥ (A *ᵥ w) - q * (w ⬝ᵥ w)) := by
  have h1 : w ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ w) := by
    rw [dotProduct_comm w (A *ᵥ v), mulVec_dot, hA]
  have h2 : w ⬝ᵥ v = v ⬝ᵥ w := dotProduct_comm _ _
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, h1, h2]
  ring

/-- A positive definite `2 × 2` Gram matrix. -/
theorem quad2_pos (g₁₁ g₁₂ g₂₂ a b : ℝ) (h₁ : 0 < g₁₁) (h₂ : g₁₂ ^ 2 < g₁₁ * g₂₂)
    (hab : ¬ (a = 0 ∧ b = 0)) : 0 < a ^ 2 * g₁₁ + 2 * a * b * g₁₂ + b ^ 2 * g₂₂ := by
  have key : g₁₁ * (a ^ 2 * g₁₁ + 2 * a * b * g₁₂ + b ^ 2 * g₂₂) =
      (g₁₁ * a + g₁₂ * b) ^ 2 + (g₁₁ * g₂₂ - g₁₂ ^ 2) * b ^ 2 := by ring
  have hpos : 0 < (g₁₁ * a + g₁₂ * b) ^ 2 + (g₁₁ * g₂₂ - g₁₂ ^ 2) * b ^ 2 := by
    by_cases hb : b = 0
    · have ha : a ≠ 0 := fun ha => hab ⟨ha, hb⟩
      subst hb
      have hx : g₁₁ * a ≠ 0 := mul_ne_zero h₁.ne' ha
      have : 0 < (g₁₁ * a) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
      simpa using this
    · have : 0 < b ^ 2 := by positivity
      have : 0 < g₁₁ * g₂₂ - g₁₂ ^ 2 := by linarith
      positivity
  rw [← key] at hpos
  by_contra hcon
  push Not at hcon
  nlinarith

omit [DecidableEq m] in
theorem cast_dot_mulVec (M : Matrix m m ℚ) (v w : m → ℚ) :
    (fun i => (v i : ℝ)) ⬝ᵥ (M.map (Rat.castHom ℝ) *ᵥ fun i => (w i : ℝ)) =
      ((v ⬝ᵥ (M *ᵥ w) : ℚ) : ℝ) := by
  simp [dotProduct, mulVec, Rat.cast_sum, Rat.cast_mul]

omit [DecidableEq m] in
theorem cast_dot (v w : m → ℚ) :
    (fun i => (v i : ℝ)) ⬝ᵥ (fun i => (w i : ℝ)) = ((v ⬝ᵥ w : ℚ) : ℝ) := by
  simp [dotProduct, Rat.cast_sum, Rat.cast_mul]

omit [DecidableEq m] in
theorem cast_trace (M : Matrix m m ℚ) : (M.map (Rat.castHom ℝ)).trace = ((M.trace : ℚ) : ℝ) := by
  simp [trace, Rat.cast_sum]

end Certificates

end Spectral
