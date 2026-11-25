import Conjectures.RSA.Seq
import Conjectures.RSA.Static.List

/-!
# Random sequential adsorption vs. uniform jamming: Conjecture 5.2 of arXiv:2611.14718 is false

Higuita-Diaz, López, Roldán-Correa, *Random Sequential Adsorption versus the Uniform Ensemble of
Jammed Configurations: Stochastic Dominance on Graphs*, arXiv:2611.14718, Conjecture 5.2:

> For every finite simple graph G with maximum degree Δ(G) ≤ 3, the sequential model dominates
> the static model (N_stat ≤st N_seq).

Dominance (Definition 2.1) means `P[N_seq ≤ k] ≤ P[N_stat ≤ k]` for every `k`.

* **Sequential model.** Vertices are occupied one at a time, each chosen uniformly among the
  still-available vertices; an occupied vertex blocks itself and its neighbours; the process stops
  when nothing is available. `seqLaw G j A` is the probability that, started from the available
  set `A`, the process occupies exactly `j` vertices; it is defined by the one-step recursion.
* **Static model.** A maximal independent set is chosen uniformly at random.

We prove `¬ Conjecture52` on a 15-vertex tree of maximum degree 3, at `k = 6`:
`P[N_seq ≤ 6] ≥ 64/3375 > 1/55 ≥ P[N_stat ≤ 6]`. (The exact values are 64/3375 and 1/55; Lean proves the two inequalities, which is all the refutation needs.)
-/


namespace RSA

/-- **Conjecture 5.2 of arXiv:2611.14718 is false**: on the 15-vertex tree,
`P[N_seq ≤ 6] ≥ 64/3375 > 1/55 ≥ P[N_stat ≤ 6]`. -/
theorem conjecture52_false : ¬ Conjecture52 := by
  intro h
  have := h (Fin 15) tree tree_degree 6
  have h1 := seqCDF_ge
  have h2 := statCDF_le
  have : (1 / 55 : ℚ) < 64 / 3375 := by norm_num
  linarith

end RSA

#print axioms RSA.conjecture52_false
