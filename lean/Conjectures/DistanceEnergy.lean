import Conjectures.Spectral
import Conjectures.GraphCert
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Distance energy: the 2009 path-complete conjecture is false

Caporossi, Chasset, Furtula, *Some conjectures and properties on distance energy*, Les Cahiers du
GERAD G-2009-64, Conjecture 4 (restated as open in Aouchiche–Hansen, *Distance spectra of graphs:
a survey*, LAA 458 (2014), Conjecture 8.13):

> Let G be a graph on n vertices and m ≤ (n − 2)(n − 3)/2 edges [that maximises distance energy],
> then G is composed of a path appended to a clique with possibly some edges between vertices of
> the clique and the vertex of the path adjacent to the clique.

`E_D(G) = ∑ |eigenvalues of the distance matrix|`. For given `n, m` the path-complete graph is
`PK(n; k, j)`: a clique on `0, …, k-1`, a path `k, k+1, …, n-1`, and the path vertex `k` joined to
the `j` clique vertices `0, …, j-1` (`2 ≤ k < n`, `1 ≤ j ≤ k-1`); `(k, j)` is determined by
`(n, m)` through `m = k(k-1)/2 + (n-k-1) + j`.

We prove `¬ Conjecture` with `n = 12`, `m = 44` (limit 45), `PK(12; 9, 6)`, and `G` = the complete
tripartite graph `K₄,₄,₃` plus one vertex joined to one 4-part (graph6 `K]Nxnsor}^^R`):
* `E_D(G) ≥ tr(D_G S) = 37.069200` for a rational `S` with `-I ⪯ S ⪯ I`;
* `E_D(PK) ≤ tr X + tr Y = 36.942400` for `D_PK = X − Y` with rational `X, Y ⪰ 0`.
Every PSD claim is certified by an exact factorisation `Pᵀ diag(d) P` with `d ≥ 0`, and every
distance by a breadth-first-search table.
-/

namespace DistanceEnergy

open Matrix SimpleGraph Spectral

/-- The distance matrix `D(G)ᵢⱼ = dist(i, j)`. -/
noncomputable def distMatrix {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (G.dist i j : ℝ)

theorem distMatrix_isHermitian {n : ℕ} (G : SimpleGraph (Fin n)) : (distMatrix G).IsHermitian :=
  IsHermitian.ext fun i j => by simp [distMatrix, SimpleGraph.dist_comm]

/-- Distance energy: the sum of the absolute values of the eigenvalues of `D(G)`. -/
noncomputable def distEnergy {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ i, |(distMatrix_isHermitian G).eigenvalues i|

/-- The path-complete graph `PK(n; k, j)`. -/
def pathComplete (n k j : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ ((a.val < k ∧ b.val < k) ∨
    (k ≤ a.val ∧ k ≤ b.val ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val)) ∨
    (a.val = k ∧ b.val < j) ∨ (b.val = k ∧ a.val < j))
  symm := ⟨fun _ _ ⟨h, h'⟩ => ⟨Ne.symm h, by omega⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

instance (n k j : ℕ) : DecidableRel (pathComplete n k j).Adj := fun a b => by
  unfold pathComplete; infer_instance

/-- `(k, j)` are parameters of a path-complete graph with `n` vertices and `m` edges. -/
def IsPKParams (n m k j : ℕ) : Prop :=
  2 ≤ k ∧ k < n ∧ 1 ≤ j ∧ j < k ∧ k * (k - 1) / 2 + (n - k - 1) + j = m

/-- **Conjecture 4 of GERAD G-2009-64 / Conjecture 8.13 of Aouchiche–Hansen**, as worded: for
`m ≤ (n-2)(n-3)/2`, a connected graph with `n` vertices and `m` edges that maximises distance
energy (among connected graphs with `n` vertices and `m` edges) is a path-complete graph. -/
def Conjecture : Prop :=
  ∀ (n m : ℕ), m ≤ (n - 2) * (n - 3) / 2 →
    ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard = m →
      (∀ H : SimpleGraph (Fin n), H.Connected → H.edgeSet.ncard = m →
        distEnergy H ≤ distEnergy G) →
      ∃ k j : ℕ, IsPKParams n m k j ∧ Nonempty (G ≃g pathComplete n k j)

/-- The same conjecture in the form "PK(n, m) maximises distance energy". -/
def ConjectureMax : Prop :=
  ∀ (n m : ℕ), m ≤ (n - 2) * (n - 3) / 2 →
    ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard = m →
      ∀ k j : ℕ, IsPKParams n m k j → distEnergy G ≤ distEnergy (pathComplete n k j)

/-- Distance energy is invariant under graph isomorphism. -/
theorem distEnergy_iso {n : ℕ} {H H' : SimpleGraph (Fin n)} (f : H ≃g H') :
    distEnergy H = distEnergy H' := by
  unfold distEnergy
  have hM : distMatrix H' = Matrix.reindex f.toEquiv f.toEquiv (distMatrix H) := by
    ext i j
    have h := f.dist_eq (f.symm i) (f.symm j)
    rw [f.apply_symm_apply, f.apply_symm_apply] at h
    simp only [distMatrix, reindex_apply, submatrix_apply]
    rw [h]
    rfl
  have hc : (distMatrix H').charpoly = (distMatrix H).charpoly := by
    rw [hM, charpoly_reindex]
  rw [((distMatrix_isHermitian H').eigenvalues_eq_eigenvalues_iff
    (distMatrix_isHermitian H)).2 hc]

/-! ### The counterexample -/

def edgeList : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 5), (0, 7), (0, 9), (0, 10), (0, 11), (1, 2), (1, 3), (1, 5), (1, 7), (1, 9), (1, 10), (1, 11), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 11), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 11), (4, 5), (4, 7), (4, 9), (4, 10), (4, 11), (5, 6), (5, 9), (5, 10), (6, 7), (6, 9), (6, 10), (6, 11), (7, 9), (7, 10), (8, 9), (8, 10), (9, 11), (10, 11)]

/-- `K₄,₄,₃` plus a vertex joined to one 4-part (graph6 `K]Nxnsor}^^R`). -/
def G : SimpleGraph (Fin 12) where
  Adj i j := (i.val, j.val) ∈ edgeList ∨ (j.val, i.val) ∈ edgeList
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G.Adj := fun i j => by unfold G; infer_instance

abbrev PK : SimpleGraph (Fin 12) := pathComplete 12 9 6

/-- Distance table of `G`. -/
def DG : Matrix (Fin 12) (Fin 12) ℕ :=
  !![0, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1;
    2, 0, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1;
    1, 1, 0, 2, 1, 1, 1, 1, 1, 2, 2, 1;
    1, 1, 2, 0, 1, 1, 1, 1, 1, 2, 2, 1;
    2, 2, 1, 1, 0, 1, 2, 1, 2, 1, 1, 1;
    1, 1, 1, 1, 1, 0, 1, 2, 2, 1, 1, 2;
    2, 2, 1, 1, 2, 1, 0, 1, 2, 1, 1, 1;
    1, 1, 1, 1, 1, 2, 1, 0, 2, 1, 1, 2;
    2, 2, 1, 1, 2, 2, 2, 2, 0, 1, 1, 2;
    1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 2, 1;
    1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 0, 1;
    1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 0]

/-- Distance table of `PK(12; 9, 6)`. -/
def DP : Matrix (Fin 12) (Fin 12) ℕ :=
  !![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3;
    1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3;
    1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 3;
    1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 3;
    1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 3;
    1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 2, 3;
    1, 1, 1, 1, 1, 1, 0, 1, 1, 2, 3, 4;
    1, 1, 1, 1, 1, 1, 1, 0, 1, 2, 3, 4;
    1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 3, 4;
    1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 1, 2;
    2, 2, 2, 2, 2, 2, 3, 3, 3, 1, 0, 1;
    3, 3, 3, 3, 3, 3, 4, 4, 4, 2, 1, 0]

theorem DG_cert : ∀ u, DG u u = 0 ∧ (∀ x y, G.Adj x y → DG u y ≤ DG u x + 1) ∧
    (∀ v, v ≠ u → ∃ w, G.Adj w v ∧ DG u w + 1 = DG u v) := by
  decide +kernel

theorem DP_cert : ∀ u, DP u u = 0 ∧ (∀ x y, PK.Adj x y → DP u y ≤ DP u x + 1) ∧
    (∀ v, v ≠ u → ∃ w, PK.Adj w v ∧ DP u w + 1 = DP u v) := by
  decide +kernel

theorem distMatrix_G : distMatrix G = (DG.map (Nat.cast : ℕ → ℚ)).map (Rat.castHom ℝ) := by
  ext u v
  obtain ⟨h0, h1, h2⟩ := DG_cert u
  simp [distMatrix, GraphCert.dist_eq_of_bfs G u (DG u) h0 h1 h2 v]

theorem distMatrix_PK : distMatrix PK = (DP.map (Nat.cast : ℕ → ℚ)).map (Rat.castHom ℝ) := by
  ext u v
  obtain ⟨h0, h1, h2⟩ := DP_cert u
  simp [distMatrix, GraphCert.dist_eq_of_bfs PK u (DP u) h0 h1 h2 v]

theorem G_connected : G.Connected := by
  obtain ⟨h0, _, h2⟩ := DG_cert 0
  exact GraphCert.connected_of_parent G 0 (DG 0) h0 h2

theorem G_card_edges : G.edgeSet.ncard = 44 := by
  have h := G.sum_degrees_eq_twice_card_edges
  have : ∑ v, G.degree v = 88 := by decide +kernel
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  omega

/-- For `n = 12, m = 44` the only path-complete parameters are `k = 9, j = 6`. -/
theorem params_unique (k j : ℕ) (h : IsPKParams 12 44 k j) : k = 9 ∧ j = 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have : k < 12 := h2
  have : j < 12 := by omega
  interval_cases k <;> omega

/-! #### Lower bound for `E_D(G)` -/

def S : Matrix (Fin 12) (Fin 12) ℚ :=
  !![-1367/2500, 282/625, 119/10000, 119/10000, 282/625, -153/2500, 282/625, -153/2500, 2729/10000, 119/10000, 119/10000, -153/2500;
    282/625, -1367/2500, 119/10000, 119/10000, 282/625, -153/2500, 282/625, -153/2500, 2729/10000, 119/10000, 119/10000, -153/2500;
    119/10000, 119/10000, -251/500, 62/125, 119/10000, 19/1250, 119/10000, 19/1250, -339/5000, 62/125, 62/125, 19/1250;
    119/10000, 119/10000, 62/125, -251/500, 119/10000, 19/1250, 119/10000, 19/1250, -339/5000, 62/125, 62/125, 19/1250;
    282/625, 282/625, 119/10000, 119/10000, -1367/2500, -153/2500, 282/625, -153/2500, 2729/10000, 119/10000, 119/10000, -153/2500;
    -153/2500, -153/2500, 19/1250, 19/1250, -153/2500, -411/1000, -153/2500, 587/1000, 3493/10000, 19/1250, 19/1250, 587/1000;
    282/625, 282/625, 119/10000, 119/10000, 282/625, -153/2500, -1367/2500, -153/2500, 2729/10000, 119/10000, 119/10000, -153/2500;
    -153/2500, -153/2500, 19/1250, 19/1250, -153/2500, 587/1000, -153/2500, -411/1000, 3493/10000, 19/1250, 19/1250, 587/1000;
    2729/10000, 2729/10000, -339/5000, -339/5000, 2729/10000, 3493/10000, 2729/10000, 3493/10000, -14/25, -339/5000, -339/5000, 3493/10000;
    119/10000, 119/10000, 62/125, 62/125, 119/10000, 19/1250, 119/10000, 19/1250, -339/5000, -251/500, 62/125, 19/1250;
    119/10000, 119/10000, 62/125, 62/125, 119/10000, 19/1250, 119/10000, 19/1250, -339/5000, 62/125, -251/500, 19/1250;
    -153/2500, -153/2500, 19/1250, 19/1250, -153/2500, 587/1000, -153/2500, 587/1000, 3493/10000, 19/1250, 19/1250, -411/1000]

def P₁ : Matrix (Fin 12) (Fin 12) ℚ :=
  !![1, -376/1289, -119/15468, -119/15468, -376/1289, 51/1289, -376/1289, 51/1289, -2729/15468, -119/15468, -119/15468, 51/1289;
    0, 1, -119/10956, -119/10956, -376/913, 51/913, -376/913, 51/913, -2729/10956, -119/10956, -119/10956, 51/913;
    0, 0, 1, -27185041/82265399, -1188810/82265399, -759828/82265399, -1188810/82265399, -759828/82265399, 3389333/82265399, -27185041/82265399, -27185041/82265399, -759828/82265399;
    0, 0, 0, 1, -594405/27540179, -379914/27540179, -594405/27540179, -379914/27540179, 3389333/55080358, -27185041/55080358, -27185041/55080358, -379914/27540179;
    0, 0, 0, 0, 1, 3060272/32370837, -22709521/32370837, 3060272/32370837, -13646188/32370837, -396270/10790279, -396270/10790279, 3060272/32370837;
    0, 0, 0, 0, 0, 1, 2038141152/15033939269, -6525038173/15033939269, -5833395071/30067878538, -253414332/15033939269, -253414332/15033939269, -6525038173/15033939269;
    0, 0, 0, 0, 0, 0, 1, 1528605864/3220731635, -4546455051/3220731635, -792239967/6441463270, -792239967/6441463270, 1528605864/3220731635;
    0, 0, 0, 0, 0, 0, 0, 1, -16972649/3231271856, -146853/403908982, -146853/403908982, -1605095707/1615635928;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 18154906920/291609415483, 18154906920/291609415483, -169556763510/291609415483;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -290967306635/292251524331, -546786/7493628829;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -10662327/642108848;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def d₁ : Fin 12 → ℚ := ![3867/2500, 912087/644500, 82265399/54780000, 27512638821/20566349750, 32338466163/27540179000, 15033939269/10790279000, 214500726891/375848481725, 403505073018/402591454375, 291609415483/16156359280000, 291959272806669/291609415483000, 106911123192/12177146847125, 222494283/32105442400]

def P₂ : Matrix (Fin 12) (Fin 12) ℚ :=
  !![1, 1128/1133, 119/4532, 119/4532, 1128/1133, -153/1133, 1128/1133, -153/1133, 2729/4532, 119/4532, 119/4532, -153/1133;
    0, 1, 1/76, 1/76, 1128/2261, -9/133, 1128/2261, -9/133, 2729/9044, 1/76, 1/76, -9/133;
    0, 0, 1, 188361/189121, 10/189121, 6388/189121, 10/189121, 6388/189121, -28493/189121, 188361/189121, 188361/189121, 6388/189121;
    0, 0, 0, 1, 5/188741, 3194/188741, 5/188741, 3194/188741, -28493/377482, 188361/377482, 188361/377482, 3194/188741;
    0, 0, 0, 0, 1, -437104/9618691, 3201497/9618691, -437104/9618691, 1949116/9618691, 170/9618691, 170/9618691, -437104/9618691;
    0, 0, 0, 0, 0, 1, -6119456/39061456193, 38926794519/39061456193, 52356353213/78122912386, 2278996/39061456193, 2278996/39061456193, 38926794519/39061456193;
    0, 0, 0, 0, 0, 0, 1, -1529864/13015610365, 2276242551/13015610365, 396967/26031220730, 396967/26031220730, -1529864/13015610365;
    0, 0, 0, 0, 0, 0, 0, 1, 17446296649/51972700144, 189853/6496587518, 189853/6496587518, 12970739707/25986350072;
    0, 0, 0, 0, 0, 0, 0, 0, 1, -45139473080/719110399483, -45139473080/719110399483, 174462966490/719110399483;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 709820229365/2148041028331, 30347041346/2148041028331;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 15173520673/1428930628848;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def d₂ : Fin 12 → ℚ := ![1133/2500, 2261/566500, 189121/380000, 188741/47280250, 9618691/3208597000, 39061456193/67330837000, 2603122073/976536404825, 6496587518/1626951295625, 719110399483/259863500720000, 2148041028331/719110399483000, 714465314424/268505128541375, 202515039517/71446531442400]

theorem cert₁ : 1 - S = P₁ᵀ * diagonal d₁ * P₁ := by decide +kernel

theorem cert₂ : 1 + S = P₂ᵀ * diagonal d₂ * P₂ := by decide +kernel

theorem d₁₂_nonneg : (∀ i, 0 ≤ d₁ i) ∧ ∀ i, 0 ≤ d₂ i := by decide +kernel

theorem trace_DS : (DG.map (Nat.cast : ℕ → ℚ) * S).trace = 92673/2500 := by decide +kernel

theorem one_sub_map (M : Matrix (Fin 12) (Fin 12) ℚ) :
    (1 : Matrix (Fin 12) (Fin 12) ℝ) - M.map (Rat.castHom ℝ) = (1 - M).map (Rat.castHom ℝ) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem one_add_map (M : Matrix (Fin 12) (Fin 12) ℚ) :
    (1 : Matrix (Fin 12) (Fin 12) ℝ) + M.map (Rat.castHom ℝ) = (1 + M).map (Rat.castHom ℝ) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem energy_G_ge : (92673/2500 : ℝ) ≤ distEnergy G := by
  unfold distEnergy
  have key := trace_mul_le_sum_abs (distMatrix_isHermitian G) (S.map (Rat.castHom ℝ))
    (fun x => by rw [one_sub_map, cert₁]; exact psd_of_ldl P₁ d₁ d₁₂_nonneg.1 x)
    (fun x => by rw [one_add_map, cert₂]; exact psd_of_ldl P₂ d₂ d₁₂_nonneg.2 x)
  have htr : (distMatrix G * S.map (Rat.castHom ℝ)).trace = ((92673/2500 : ℚ) : ℝ) := by
    rw [distMatrix_G, ← Matrix.map_mul, cast_trace, trace_DS]
  rw [htr] at key
  have hc : ((92673 / 2500 : ℚ) : ℝ) = 92673 / 2500 := by norm_num
  rw [hc] at key
  exact key

/-! #### Upper bound for `E_D(PK)` -/

def X : Matrix (Fin 12) (Fin 12) ℚ :=
  !![10627/10000, 10607/10000, 10607/10000, 10607/10000, 10607/10000, 10607/10000, 6477/5000, 6477/5000, 6477/5000, 5347/5000, 7477/5000, 2599/1250;
    10607/10000, 10627/10000, 10607/10000, 10607/10000, 10607/10000, 10607/10000, 6477/5000, 6477/5000, 6477/5000, 5347/5000, 7477/5000, 2599/1250;
    10607/10000, 10607/10000, 10627/10000, 10607/10000, 10607/10000, 10607/10000, 6477/5000, 6477/5000, 6477/5000, 5347/5000, 7477/5000, 2599/1250;
    10607/10000, 10607/10000, 10607/10000, 10627/10000, 10607/10000, 10607/10000, 6477/5000, 6477/5000, 6477/5000, 5347/5000, 7477/5000, 2599/1250;
    10607/10000, 10607/10000, 10607/10000, 10607/10000, 10627/10000, 10607/10000, 6477/5000, 6477/5000, 6477/5000, 5347/5000, 7477/5000, 2599/1250;
    10607/10000, 10607/10000, 10607/10000, 10607/10000, 10607/10000, 10627/10000, 6477/5000, 6477/5000, 6477/5000, 5347/5000, 7477/5000, 2599/1250;
    6477/5000, 6477/5000, 6477/5000, 6477/5000, 6477/5000, 6477/5000, 15963/10000, 15943/10000, 15943/10000, 13241/10000, 917/500, 25483/10000;
    6477/5000, 6477/5000, 6477/5000, 6477/5000, 6477/5000, 6477/5000, 15943/10000, 15963/10000, 15943/10000, 13241/10000, 917/500, 25483/10000;
    6477/5000, 6477/5000, 6477/5000, 6477/5000, 6477/5000, 6477/5000, 15943/10000, 15943/10000, 15963/10000, 13241/10000, 917/500, 25483/10000;
    5347/5000, 5347/5000, 5347/5000, 5347/5000, 5347/5000, 5347/5000, 13241/10000, 13241/10000, 13241/10000, 11067/10000, 1519/1000, 4219/2000;
    7477/5000, 7477/5000, 7477/5000, 7477/5000, 7477/5000, 7477/5000, 917/500, 917/500, 917/500, 1519/1000, 21151/10000, 2937/1000;
    2599/1250, 2599/1250, 2599/1250, 2599/1250, 2599/1250, 2599/1250, 25483/10000, 25483/10000, 25483/10000, 4219/2000, 2937/1000, 40843/10000]

def P₃ : Matrix (Fin 12) (Fin 12) ℚ :=
  !![1, 10607/10627, 10607/10627, 10607/10627, 10607/10627, 10607/10627, 12954/10627, 12954/10627, 12954/10627, 10694/10627, 14954/10627, 20792/10627;
    0, 1, 10607/21234, 10607/21234, 10607/21234, 10607/21234, 2159/3539, 2159/3539, 2159/3539, 5347/10617, 7477/10617, 10396/10617;
    0, 0, 1, 10607/31841, 10607/31841, 10607/31841, 762/1873, 762/1873, 762/1873, 10694/31841, 14954/31841, 20792/31841;
    0, 0, 0, 1, 10607/42448, 10607/42448, 6477/21224, 6477/21224, 6477/21224, 5347/21224, 7477/21224, 2599/5306;
    0, 0, 0, 0, 1, 10607/53055, 4318/17685, 4318/17685, 4318/17685, 10694/53055, 14954/53055, 20792/53055;
    0, 0, 0, 0, 0, 1, 6477/31831, 6477/31831, 6477/31831, 5347/31831, 7477/31831, 10396/31831;
    0, 0, 0, 0, 0, 0, 1, 812657/939981, 812657/939981, 5884043/4699905, 2638192/4699905, 184157/276465;
    0, 0, 0, 0, 0, 0, 0, 1, 812657/1752638, 5884043/8763190, 1319096/4381595, 3130669/8763190;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 5884043/12826475, 2638192/12826475, 3130669/12826475;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 25771711/219811344, 23672177/219811344;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 553175843/2583511957;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def d₃ : Fin 12 → ℚ := ![10627/10000, 10617/2656750, 31841/10617000, 10612/3980125, 10611/4244800, 31831/13263750, 939981/63662000, 876319/234995250, 513059/175263800, 27476418/8016546875, 2583511957/1099056720000, 13187348827/5167023914000]

def P₄ : Matrix (Fin 12) (Fin 12) ℚ :=
  !![1, 607/10627, 607/10627, 607/10627, 607/10627, 607/10627, 2954/10627, 2954/10627, 2954/10627, 694/10627, -5046/10627, -9208/10627;
    0, 1, 607/11234, 607/11234, 607/11234, 607/11234, 1477/5617, 1477/5617, 1477/5617, 347/5617, -2523/5617, -4604/5617;
    0, 0, 1, 607/11841, 607/11841, 607/11841, 2954/11841, 2954/11841, 2954/11841, 694/11841, -1682/3947, -9208/11841;
    0, 0, 0, 1, 607/12448, 607/12448, 1477/6224, 1477/6224, 1477/6224, 347/6224, -2523/6224, -1151/1556;
    0, 0, 0, 0, 1, 607/13055, 422/1865, 422/1865, 422/1865, 694/13055, -5046/13055, -9208/13055;
    0, 0, 0, 0, 0, 1, 1477/6831, 1477/6831, 1477/6831, 347/6831, -841/2277, -4604/6831;
    0, 0, 0, 0, 0, 0, 1, 961219/5524327, 961219/5524327, -17440319/27621635, -11643936/27621635, -5854777/27621635;
    0, 0, 0, 0, 0, 0, 0, 1, 961219/6485546, -17440319/32427730, -5821968/16213865, -5854777/32427730;
    0, 0, 0, 0, 0, 0, 0, 0, 1, -17440319/37233825, -3881312/12411275, -5854777/37233825;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2841185921/574486816, 1789296353/574486816;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -580782476573/834970645773;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def d₄ : Fin 12 → ℚ := ![10627/10000, 2814117/2656750, 5932341/5617000, 519704/493375, 1308111/1244800, 3422331/3263750, 5524327/4554000, 1624629273/1381081750, 746165853/648554600, 71810852/7757046875, 834970645773/2872434080000, 14900538342203/1669941291546000]

theorem cert₃ : X = P₃ᵀ * diagonal d₃ * P₃ := by decide +kernel

theorem cert₄ : X - DP.map (Nat.cast : ℕ → ℚ) = P₄ᵀ * diagonal d₄ * P₄ := by decide +kernel

theorem d₃₄_nonneg : (∀ i, 0 ≤ d₃ i) ∧ ∀ i, 0 ≤ d₄ i := by decide +kernel

theorem trace_XY : X.trace + (X - DP.map (Nat.cast : ℕ → ℚ)).trace = 23089/625 := by
  decide +kernel

theorem energy_PK_le : distEnergy PK ≤ (23089/625 : ℝ) := by
  unfold distEnergy
  have key := sum_abs_le_trace_add_trace (distMatrix_isHermitian PK) (X.map (Rat.castHom ℝ))
    ((X - DP.map (Nat.cast : ℕ → ℚ)).map (Rat.castHom ℝ))
    (by rw [distMatrix_PK]; ext i j; simp)
    (fun x => by rw [cert₃]; exact psd_of_ldl P₃ d₃ d₃₄_nonneg.1 x)
    (fun x => by rw [cert₄]; exact psd_of_ldl P₄ d₄ d₃₄_nonneg.2 x)
  rw [cast_trace, cast_trace, ← Rat.cast_add, trace_XY] at key
  have hc : ((23089 / 625 : ℚ) : ℝ) = 23089 / 625 := by norm_num
  rw [hc] at key
  exact key

/-- Among connected graphs on `Fin n` with `m` edges, if there is one, some graph has maximal
distance energy (there are finitely many graphs on `Fin n`). -/
theorem exists_maximiser {n : ℕ} (m : ℕ) (G₀ : SimpleGraph (Fin n))
    (h₀ : G₀.Connected ∧ G₀.edgeSet.ncard = m) :
    ∃ M : SimpleGraph (Fin n), (M.Connected ∧ M.edgeSet.ncard = m) ∧
      ∀ H : SimpleGraph (Fin n), H.Connected ∧ H.edgeSet.ncard = m →
        distEnergy H ≤ distEnergy M := by
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image
    {H : SimpleGraph (Fin n) | H.Connected ∧ H.edgeSet.ncard = m} distEnergy (Set.toFinite _)
    ⟨G₀, h₀⟩
  exact ⟨M, hM, fun H hH => hmax H hH⟩

theorem energy_gap : distEnergy PK < distEnergy G := by
  have h1 := energy_G_ge
  have h2 := energy_PK_le
  norm_num at h1 h2
  linarith

/-- **"PK(n, m) maximises distance energy" is false**: with `n = 12, m = 44`,
`E_D(G) ≥ 37.0692 > 36.9424 ≥ E_D(PK(12; 9, 6))`. -/
theorem conjectureMax_false : ¬ ConjectureMax := by
  intro h
  have := h 12 44 (by norm_num) G G_connected G_card_edges 9 6 (by norm_num [IsPKParams])
  linarith [energy_gap]

/-- **Conjecture 4 of GERAD G-2009-64 (Conjecture 8.13 of Aouchiche–Hansen) is false**: a
maximiser of distance energy among connected graphs with 12 vertices and 44 edges exists, and it
cannot be isomorphic to `PK(12; 9, 6)`, because `E_D(G) > E_D(PK(12; 9, 6))`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  obtain ⟨M, hM, hmax⟩ := exists_maximiser 44 G ⟨G_connected, G_card_edges⟩
  obtain ⟨k, j, hkj, ⟨f⟩⟩ := h 12 44 (by norm_num) M hM.1 hM.2
    (fun H hH hH' => hmax H ⟨hH, hH'⟩)
  obtain ⟨rfl, rfl⟩ := params_unique k j hkj
  have h1 := distEnergy_iso f
  have h2 := hmax G ⟨G_connected, G_card_edges⟩
  have h3 := energy_gap
  linarith

end DistanceEnergy

#print axioms DistanceEnergy.conjecture_false
#print axioms DistanceEnergy.conjectureMax_false
