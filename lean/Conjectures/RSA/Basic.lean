import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Minimal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases


/-! Definitions for `Conjectures/RSA.lean`: the two models, and the 15-vertex tree. -/

namespace RSA

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The available set after occupying `v`: remove `v` and its neighbours from `A`. -/
def after (A : Finset V) (v : V) : Finset V := A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)

/-- **Sequential model.** `seqLaw G j A` is the probability that random sequential adsorption,
started with available set `A`, ends with exactly `j` occupied vertices: if nothing is available
the process has stopped; otherwise a vertex `v ∈ A` is chosen with probability `1/|A|`, occupied,
and the process continues from `after G A v`. -/
def seqLaw : ℕ → Finset V → ℚ
  | 0, A => if A = ∅ then 1 else 0
  | j + 1, A => if A = ∅ then 0 else (A.card : ℚ)⁻¹ * ∑ v ∈ A, seqLaw j (after G A v)

/-- `P[N_seq ≤ k]` for the process started on the whole vertex set. -/
def seqCDF (k : ℕ) : ℚ := ∑ j ∈ range (k + 1), seqLaw G j univ

/-- A maximal independent set: an independent set that is maximal for inclusion. -/
def IsMaxIndepSet (S : Finset V) : Prop :=
  Maximal (fun T : Finset V => G.IsIndepSet (T : Set V)) S

open Classical in
/-- **Static model.** `P[N_stat ≤ k]` when a maximal independent set is chosen uniformly. -/
noncomputable def statCDF (k : ℕ) : ℚ :=
  ((univ.filter (fun S : Finset V => IsMaxIndepSet G S ∧ S.card ≤ k)).card : ℚ) /
    (univ.filter (fun S : Finset V => IsMaxIndepSet G S)).card

/-- The same recursion as `seqLaw`, but keeping only the choices that lie in `T`. -/
def seqLawVia (T : Finset V) : ℕ → Finset V → ℚ
  | 0, A => if A = ∅ then 1 else 0
  | j + 1, A => if A = ∅ then 0 else (A.card : ℚ)⁻¹ * ∑ v ∈ A ∩ T, seqLawVia T j (after G A v)

omit [Fintype V] in
theorem seqLaw_nonneg (j : ℕ) (A : Finset V) : 0 ≤ seqLaw G j A := by
  induction j generalizing A with
  | zero => unfold seqLaw; split_ifs <;> norm_num
  | succ j ih =>
    unfold seqLaw
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (sum_nonneg fun v _ => ih _)

omit [Fintype V] in
theorem seqLawVia_le (T : Finset V) (j : ℕ) (A : Finset V) :
    seqLawVia G T j A ≤ seqLaw G j A := by
  induction j generalizing A with
  | zero => unfold seqLawVia seqLaw; exact le_rfl
  | succ j ih =>
    unfold seqLawVia seqLaw
    split_ifs
    · exact le_rfl
    · apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg _))
      calc ∑ v ∈ A ∩ T, seqLawVia G T j (after G A v)
          ≤ ∑ v ∈ A ∩ T, seqLaw G j (after G A v) := sum_le_sum fun v _ => ih _
        _ ≤ ∑ v ∈ A, seqLaw G j (after G A v) :=
          sum_le_sum_of_subset_of_nonneg inter_subset_left
            fun v _ _ => seqLaw_nonneg G j _

omit [Fintype V] in
/-- Maximal independent sets are exactly the independent dominating sets. -/
theorem isMaxIndepSet_iff (S : Finset V) : IsMaxIndepSet G S ↔
    (∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) ∧ ∀ v, v ∉ S → ∃ w ∈ S, G.Adj v w := by
  constructor
  · rintro ⟨hind, hmax⟩
    refine ⟨fun x hx y hy hxy => hind hx hy (G.ne_of_adj hxy) hxy, fun v hv => ?_⟩
    by_contra hcon
    push Not at hcon
    have hT : G.IsIndepSet ((insert v S : Finset V) : Set V) := by
      rw [coe_insert, SimpleGraph.IsIndepSet, Set.pairwise_insert]
      exact ⟨hind, fun b hb _ => ⟨hcon b hb, fun h => hcon b hb (G.adj_symm h)⟩⟩
    exact hv (hmax hT (subset_insert v S) (mem_insert_self v S))
  · rintro ⟨hI, hD⟩
    refine ⟨fun x hx y hy _ => hI x hx y hy, fun T hT hST t ht => ?_⟩
    by_contra hts
    obtain ⟨w, hw, hadj⟩ := hD t hts
    exact hT (mem_coe.2 ht) (mem_coe.2 (hST hw)) (G.ne_of_adj hadj) hadj

end General

/-- **Conjecture 5.2 of arXiv:2611.14718**: for every finite simple graph with maximum degree at
most 3 and every `k`, `P[N_seq ≤ k] ≤ P[N_stat ≤ k]`. -/
def Conjecture52 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ 3) → ∀ k : ℕ, seqCDF G k ≤ statCDF G k

/-! ### The counterexample: a tree on 15 vertices -/

/-- Edges `0-1 0-2 0-3 1-4 2-5 3-6 4-7 5-8 7-9 7-10 8-11 8-12 9-13 11-14`. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 7), (5, 8),
    (7, 9), (7, 10), (8, 11), (8, 12), (9, 13), (11, 14)]

def tree : SimpleGraph (Fin 15) where
  Adj i j := (i.val, j.val) ∈ edgeList ∨ (j.val, i.val) ∈ edgeList
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel tree.Adj := fun i j => by unfold tree; infer_instance

theorem tree_degree (v : Fin 15) : tree.degree v ≤ 3 := by
  revert v; decide +kernel

/-- The unique smallest maximal independent set. -/
def Sstar : Finset (Fin 15) := {0, 6, 7, 8, 13, 14}

end RSA
