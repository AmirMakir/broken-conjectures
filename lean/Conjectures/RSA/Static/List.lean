import Conjectures.RSA.Static.Cases

/-! At least 55 maximal independent sets, so `P[N_stat ≤ 6] ≤ 1/55`. -/

namespace RSA

open Finset

/-- The 55 maximal independent sets of the tree. -/
def misList : List (Finset (Fin 15)) :=
  [{1, 2, 3, 9, 10, 11, 12},
    {2, 3, 4, 9, 10, 11, 12},
    {1, 3, 5, 9, 10, 11, 12},
    {3, 4, 5, 9, 10, 11, 12},
    {1, 2, 6, 9, 10, 11, 12},
    {2, 4, 6, 9, 10, 11, 12},
    {1, 5, 6, 9, 10, 11, 12},
    {0, 4, 5, 6, 9, 10, 11, 12},
    {1, 2, 3, 7, 11, 12, 13},
    {1, 3, 5, 7, 11, 12, 13},
    {1, 2, 6, 7, 11, 12, 13},
    {0, 5, 6, 7, 11, 12, 13},
    {1, 5, 6, 7, 11, 12, 13},
    {1, 2, 3, 10, 11, 12, 13},
    {2, 3, 4, 10, 11, 12, 13},
    {1, 3, 5, 10, 11, 12, 13},
    {3, 4, 5, 10, 11, 12, 13},
    {1, 2, 6, 10, 11, 12, 13},
    {2, 4, 6, 10, 11, 12, 13},
    {1, 5, 6, 10, 11, 12, 13},
    {0, 4, 5, 6, 10, 11, 12, 13},
    {1, 2, 3, 8, 9, 10, 14},
    {2, 3, 4, 8, 9, 10, 14},
    {1, 2, 6, 8, 9, 10, 14},
    {0, 4, 6, 8, 9, 10, 14},
    {2, 4, 6, 8, 9, 10, 14},
    {1, 2, 3, 9, 10, 12, 14},
    {2, 3, 4, 9, 10, 12, 14},
    {1, 3, 5, 9, 10, 12, 14},
    {3, 4, 5, 9, 10, 12, 14},
    {1, 2, 6, 9, 10, 12, 14},
    {2, 4, 6, 9, 10, 12, 14},
    {1, 5, 6, 9, 10, 12, 14},
    {0, 4, 5, 6, 9, 10, 12, 14},
    {1, 2, 3, 7, 8, 13, 14},
    {0, 6, 7, 8, 13, 14},
    {1, 2, 6, 7, 8, 13, 14},
    {1, 2, 3, 8, 10, 13, 14},
    {2, 3, 4, 8, 10, 13, 14},
    {1, 2, 6, 8, 10, 13, 14},
    {0, 4, 6, 8, 10, 13, 14},
    {2, 4, 6, 8, 10, 13, 14},
    {1, 2, 3, 7, 12, 13, 14},
    {1, 3, 5, 7, 12, 13, 14},
    {1, 2, 6, 7, 12, 13, 14},
    {0, 5, 6, 7, 12, 13, 14},
    {1, 5, 6, 7, 12, 13, 14},
    {1, 2, 3, 10, 12, 13, 14},
    {2, 3, 4, 10, 12, 13, 14},
    {1, 3, 5, 10, 12, 13, 14},
    {3, 4, 5, 10, 12, 13, 14},
    {1, 2, 6, 10, 12, 13, 14},
    {2, 4, 6, 10, 12, 13, 14},
    {1, 5, 6, 10, 12, 13, 14},
    {0, 4, 5, 6, 10, 12, 13, 14}]

/-- A numeric key (the bitmask of the set), used to check that the 55 sets are distinct. -/
def key (S : Finset (Fin 15)) : ℕ := ∑ i ∈ S, 2 ^ i.val

theorem misList_keys : (misList.map key).Nodup := by decide +kernel

/-- Independent and dominating: the decidable form of a maximal independent set. -/
def IndDom (S : Finset (Fin 15)) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, ¬ tree.Adj x y) ∧ ∀ v, v ∉ S → ∃ w ∈ S, tree.Adj v w

instance : DecidablePred IndDom := fun S => by unfold IndDom; infer_instance

theorem mis1 : IndDom {1, 2, 3, 9, 10, 11, 12} := by decide +kernel

theorem mis2 : IndDom {2, 3, 4, 9, 10, 11, 12} := by decide +kernel

theorem mis3 : IndDom {1, 3, 5, 9, 10, 11, 12} := by decide +kernel

theorem mis4 : IndDom {3, 4, 5, 9, 10, 11, 12} := by decide +kernel

theorem mis5 : IndDom {1, 2, 6, 9, 10, 11, 12} := by decide +kernel

theorem mis6 : IndDom {2, 4, 6, 9, 10, 11, 12} := by decide +kernel

theorem mis7 : IndDom {1, 5, 6, 9, 10, 11, 12} := by decide +kernel

theorem mis8 : IndDom {0, 4, 5, 6, 9, 10, 11, 12} := by decide +kernel

theorem mis9 : IndDom {1, 2, 3, 7, 11, 12, 13} := by decide +kernel

theorem mis10 : IndDom {1, 3, 5, 7, 11, 12, 13} := by decide +kernel

theorem mis11 : IndDom {1, 2, 6, 7, 11, 12, 13} := by decide +kernel

theorem mis12 : IndDom {0, 5, 6, 7, 11, 12, 13} := by decide +kernel

theorem mis13 : IndDom {1, 5, 6, 7, 11, 12, 13} := by decide +kernel

theorem mis14 : IndDom {1, 2, 3, 10, 11, 12, 13} := by decide +kernel

theorem mis15 : IndDom {2, 3, 4, 10, 11, 12, 13} := by decide +kernel

theorem mis16 : IndDom {1, 3, 5, 10, 11, 12, 13} := by decide +kernel

theorem mis17 : IndDom {3, 4, 5, 10, 11, 12, 13} := by decide +kernel

theorem mis18 : IndDom {1, 2, 6, 10, 11, 12, 13} := by decide +kernel

theorem mis19 : IndDom {2, 4, 6, 10, 11, 12, 13} := by decide +kernel

theorem mis20 : IndDom {1, 5, 6, 10, 11, 12, 13} := by decide +kernel

theorem mis21 : IndDom {0, 4, 5, 6, 10, 11, 12, 13} := by decide +kernel

theorem mis22 : IndDom {1, 2, 3, 8, 9, 10, 14} := by decide +kernel

theorem mis23 : IndDom {2, 3, 4, 8, 9, 10, 14} := by decide +kernel

theorem mis24 : IndDom {1, 2, 6, 8, 9, 10, 14} := by decide +kernel

theorem mis25 : IndDom {0, 4, 6, 8, 9, 10, 14} := by decide +kernel

theorem mis26 : IndDom {2, 4, 6, 8, 9, 10, 14} := by decide +kernel

theorem mis27 : IndDom {1, 2, 3, 9, 10, 12, 14} := by decide +kernel

theorem mis28 : IndDom {2, 3, 4, 9, 10, 12, 14} := by decide +kernel

theorem mis29 : IndDom {1, 3, 5, 9, 10, 12, 14} := by decide +kernel

theorem mis30 : IndDom {3, 4, 5, 9, 10, 12, 14} := by decide +kernel

theorem mis31 : IndDom {1, 2, 6, 9, 10, 12, 14} := by decide +kernel

theorem mis32 : IndDom {2, 4, 6, 9, 10, 12, 14} := by decide +kernel

theorem mis33 : IndDom {1, 5, 6, 9, 10, 12, 14} := by decide +kernel

theorem mis34 : IndDom {0, 4, 5, 6, 9, 10, 12, 14} := by decide +kernel

theorem mis35 : IndDom {1, 2, 3, 7, 8, 13, 14} := by decide +kernel

theorem mis36 : IndDom {0, 6, 7, 8, 13, 14} := by decide +kernel

theorem mis37 : IndDom {1, 2, 6, 7, 8, 13, 14} := by decide +kernel

theorem mis38 : IndDom {1, 2, 3, 8, 10, 13, 14} := by decide +kernel

theorem mis39 : IndDom {2, 3, 4, 8, 10, 13, 14} := by decide +kernel

theorem mis40 : IndDom {1, 2, 6, 8, 10, 13, 14} := by decide +kernel

theorem mis41 : IndDom {0, 4, 6, 8, 10, 13, 14} := by decide +kernel

theorem mis42 : IndDom {2, 4, 6, 8, 10, 13, 14} := by decide +kernel

theorem mis43 : IndDom {1, 2, 3, 7, 12, 13, 14} := by decide +kernel

theorem mis44 : IndDom {1, 3, 5, 7, 12, 13, 14} := by decide +kernel

theorem mis45 : IndDom {1, 2, 6, 7, 12, 13, 14} := by decide +kernel

theorem mis46 : IndDom {0, 5, 6, 7, 12, 13, 14} := by decide +kernel

theorem mis47 : IndDom {1, 5, 6, 7, 12, 13, 14} := by decide +kernel

theorem mis48 : IndDom {1, 2, 3, 10, 12, 13, 14} := by decide +kernel

theorem mis49 : IndDom {2, 3, 4, 10, 12, 13, 14} := by decide +kernel

theorem mis50 : IndDom {1, 3, 5, 10, 12, 13, 14} := by decide +kernel

theorem mis51 : IndDom {3, 4, 5, 10, 12, 13, 14} := by decide +kernel

theorem mis52 : IndDom {1, 2, 6, 10, 12, 13, 14} := by decide +kernel

theorem mis53 : IndDom {2, 4, 6, 10, 12, 13, 14} := by decide +kernel

theorem mis54 : IndDom {1, 5, 6, 10, 12, 13, 14} := by decide +kernel

theorem mis55 : IndDom {0, 4, 5, 6, 10, 12, 13, 14} := by decide +kernel

theorem misList_spec : misList.Nodup ∧ misList.length = 55 ∧ ∀ S ∈ misList, IndDom S := by
  refine ⟨misList_keys.of_map key, rfl, ?_⟩
  simp only [misList, List.forall_mem_cons]
  exact ⟨mis1, mis2, mis3, mis4, mis5, mis6, mis7, mis8, mis9, mis10, mis11, mis12, mis13, mis14, mis15, mis16, mis17, mis18, mis19, mis20, mis21, mis22, mis23, mis24, mis25, mis26, mis27, mis28, mis29, mis30, mis31, mis32, mis33, mis34, mis35, mis36, mis37, mis38, mis39, mis40, mis41, mis42, mis43, mis44, mis45, mis46, mis47, mis48, mis49, mis50, mis51, mis52, mis53, mis54, mis55, by simp⟩

theorem statCDF_le : statCDF tree 6 ≤ 1 / 55 := by
  classical
  unfold statCDF
  have hnum : (univ.filter (fun S : Finset (Fin 15) =>
      IsMaxIndepSet tree S ∧ S.card ≤ 6)).card ≤ 1 := by
    refine card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_univ, true_and, isMaxIndepSet_iff] at ha hb
    rw [small_mis a ha.1.1 ha.1.2 ha.2, small_mis b hb.1.1 hb.1.2 hb.2]
  have hden : 55 ≤ (univ.filter (fun S : Finset (Fin 15) => IsMaxIndepSet tree S)).card := by
    obtain ⟨hnd, hlen, hspec⟩ := misList_spec
    have hsub : misList.toFinset ⊆ univ.filter (fun S : Finset (Fin 15) => IsMaxIndepSet tree S) :=
      fun S hS => by
        rw [mem_filter, isMaxIndepSet_iff]
        exact ⟨mem_univ _, hspec S (List.mem_toFinset.1 hS)⟩
    have := card_le_card hsub
    rwa [List.toFinset_card_of_nodup hnd, hlen] at this
  have hnum' : ((univ.filter (fun S : Finset (Fin 15) =>
      IsMaxIndepSet tree S ∧ S.card ≤ 6)).card : ℚ) ≤ 1 := by exact_mod_cast hnum
  have hden' : (55 : ℚ) ≤ (univ.filter (fun S : Finset (Fin 15) =>
      IsMaxIndepSet tree S)).card := by exact_mod_cast hden
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

end RSA
