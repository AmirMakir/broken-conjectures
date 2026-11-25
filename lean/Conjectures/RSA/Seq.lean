import Conjectures.RSA.Basic

/-! Sequential side: `P[N_seq ≤ 6] ≥ 64/3375` on the tree. -/

namespace RSA

open Finset

/-- Exact value of the sequential paths that occupy exactly the vertices of `Sstar`. -/
theorem seqLawVia_value : seqLawVia tree Sstar 6 univ = 64 / 3375 := by
  decide +kernel

theorem seqCDF_ge : (64 / 3375 : ℚ) ≤ seqCDF tree 6 := by
  rw [← seqLawVia_value]
  refine (seqLawVia_le tree Sstar 6 univ).trans ?_
  unfold seqCDF
  exact single_le_sum (f := fun j => seqLaw tree j univ) (fun j _ => seqLaw_nonneg tree j univ)
    (by simp)

end RSA
