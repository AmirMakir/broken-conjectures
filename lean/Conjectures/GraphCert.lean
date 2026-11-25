import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Distance certificates

A breadth-first-search table certifies graph distances: if `f u = 0`, `f` grows by at most one
along every edge, and every vertex other than `u` has a neighbour one step closer, then
`G.dist u v = f v` for every `v`, and every vertex is reachable from `u`.
-/

namespace GraphCert

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (u : V) (f : V → ℕ)

theorem exists_walk_of_parent (h0 : f u = 0)
    (hpar : ∀ v, v ≠ u → ∃ w, G.Adj w v ∧ f w + 1 = f v) :
    ∀ k v, f v = k → ∃ p : G.Walk u v, p.length = k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    by_cases h : v = u
    · subst h; exact ⟨.nil, rfl⟩
    · obtain ⟨w, _, hw⟩ := hpar v h
      omega
  | succ k ih =>
    intro v hv
    have hvu : v ≠ u := by rintro rfl; omega
    obtain ⟨w, hadj, hw⟩ := hpar v hvu
    obtain ⟨p, hp⟩ := ih w (by omega)
    exact ⟨p.concat hadj, by rw [Walk.length_concat, hp]⟩

theorem le_of_walk (hlip : ∀ x y, G.Adj x y → f y ≤ f x + 1) :
    ∀ {x y : V} (p : G.Walk x y), f y ≤ f x + p.length := by
  intro x y p
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons]
    have := hlip _ _ h
    omega

theorem reachable_of_parent (h0 : f u = 0)
    (hpar : ∀ v, v ≠ u → ∃ w, G.Adj w v ∧ f w + 1 = f v) (v : V) : G.Reachable u v := by
  obtain ⟨p, _⟩ := exists_walk_of_parent G u f h0 hpar (f v) v rfl
  exact ⟨p⟩

theorem dist_eq_of_bfs (h0 : f u = 0) (hlip : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    (hpar : ∀ v, v ≠ u → ∃ w, G.Adj w v ∧ f w + 1 = f v) (v : V) : G.dist u v = f v := by
  obtain ⟨p, hp⟩ := exists_walk_of_parent G u f h0 hpar (f v) v rfl
  obtain ⟨q, hq⟩ := (reachable_of_parent G u f h0 hpar v).exists_walk_length_eq_dist
  have h1 := dist_le p
  have h2 := le_of_walk G f hlip q
  omega

theorem connected_of_parent (h0 : f u = 0)
    (hpar : ∀ v, v ≠ u → ∃ w, G.Adj w v ∧ f w + 1 = f v) : G.Connected :=
  (connected_iff_exists_forall_reachable G).2 ⟨u, reachable_of_parent G u f h0 hpar⟩

end GraphCert
