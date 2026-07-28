import DeanK5.COYExteriorClaimThreeNineRank

/-!
# The terminal modified-core case of COY Claim 3.9(4)

In modification (M2), the removed vertex `t₀` cannot be the source vertex
`b'_z`.  If it were, the equality case of Claim 3.9 would provide a
working-`T` neighbour of `b_z`.  A temporary type-2 core first shows that
`b_z` has no neighbour in the original `S`-side.  All `rank + 1`
working-core neighbours of `b_z` therefore lie in the working `T`-side.
Adjoining `t₀` to them and adjoining `b_z` to the original `S`-side then
produces a type-3 core with a larger `S`-side, contrary to the selected
core's maximality.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace ExteriorZEndBlock

/--
COY Claim 3.9(4), terminal modification (M2): the second exterior
neighbour is not the distinguished vertex removed from the original
type-3 core.
-/
theorem bPrime_ne_t₀_of_terminal
    (M : MinimalCounterexample q G x y z)
    (T : TypeThreeModificationTrigger
      (z := z) P.orientation.chosen)
    (hlarge :
      P.orientation.chosen.rank + 2 ≤ T.core.T.card)
    (hworking :
      P.working =
        .modified T (.terminal hlarge))
    (E : P.ExteriorZEndBlock) :
    E.bPrime ≠ T.t₀ := by
  classical
  let K : TypeThreeModificationChoice T :=
    .terminal hlarge
  intro hPrime
  have hbzNeT₀ : E.bz ≠ T.t₀ := by
    intro h
    exact E.bz_ne_bPrime (h.trans hPrime.symm)
  have hbzNotCarrier :
      E.bz ∉ K.rooted.core.carrier := by
    have hnot :
        E.bz ∉ P.working.rooted.core.carrier :=
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        E.bz_mem_otherRegion
    rw [hworking] at hnot
    change E.bz ∉ K.rooted.core.carrier at hnot
    exact hnot
  have hcountP :=
    (E.claim_three_nine_rank_and_core_neighbor_count M).2
  have hcount :
      (G.neighborSet E.bz ∩
        (↑K.rooted.core.carrier : Set V)).ncard =
          P.orientation.chosen.rank + 1 := by
    rw [hworking] at hcountP
    simpa [K, SelectedWorkingCore.rooted,
      SelectedWorkingCore.rank,
      TypeThreeModificationChoice.rank] using hcountP
  obtain ⟨tb, htbT, hbzTb⟩ :=
    K.exists_T_neighbor_of_coreNeighbor_ncard_eq_modified
      hbzNotCarrier E.bz_ne_y hbzNeT₀
      (by
        simpa [K, TypeThreeModificationChoice.rank] using hcount)
  have htbKT : tb ∈ K.core.T := by
    simpa [TypeThreeModificationChoice.rooted, Core.T] using htbT
  have htbOriginalT : tb ∈ T.core.T := by
    simpa [K, TypeThreeModificationChoice.core,
      TypeThreeCore.eraseTerminal] using
        Finset.mem_of_mem_erase htbKT
  have htbNeT₀ : tb ≠ T.t₀ := by
    intro h
    exact K.t₀_not_mem_core_T (h ▸ htbKT)
  have hbzT₀ : G.Adj E.bz T.t₀ := by
    simpa [hPrime] using E.bz_adj_bPrime
  have hyNotOriginalCarrier :
      y ∉ P.orientation.chosen.rooted.core.carrier :=
    P.orientation.chosen.rooted.other_root_not_mem
  have hyNeX : y ≠ x := by
    intro h
    exact hyNotOriginalCarrier
      (h.symm ▸
        P.orientation.chosen.rooted.core.root_mem_carrier)
  have hbzNoOriginalS :
      ∀ s ∈ T.core.S, ¬G.Adj E.bz s := by
    intro s hsS hbzS
    have ht₀NeBz : T.t₀ ≠ E.bz :=
      hbzNeT₀.symm
    have ht₀NeS : T.t₀ ≠ s := by
      intro h
      exact Finset.disjoint_left.mp T.core.disjoint
        hsS (h.symm ▸ T.t₀_mem)
    have htbNeBz : tb ≠ E.bz :=
      hbzTb.ne.symm
    have htbNeS : tb ≠ s := by
      intro h
      exact Finset.disjoint_left.mp T.core.disjoint
        hsS (h.symm ▸ htbOriginalT)
    have hbzNeS : E.bz ≠ s :=
      hbzS.ne
    let C₂ : TypeTwoCore G x 2 := {
      S := {T.t₀, tb}
      T := {E.bz, s}
      rank_ge_two := le_rfl
      card_S := by simp [htbNeT₀.symm]
      card_T := by simp [hbzNeS]
      disjoint := by
        rw [Finset.disjoint_left]
        intro v hvS hvT
        simp only [Finset.mem_insert,
          Finset.mem_singleton] at hvS hvT
        rcases hvS with hvT₀ | hvTb
        · rcases hvT with hvBz | hvS
          · exact ht₀NeBz (hvT₀.symm.trans hvBz)
          · exact ht₀NeS (hvT₀.symm.trans hvS)
        · rcases hvT with hvBz | hvS
          · exact htbNeBz (hvTb.symm.trans hvBz)
          · exact htbNeS (hvTb.symm.trans hvS)
      root_not_mem_S := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        constructor
        · intro h
          apply T.core.root_not_mem_T
          simpa only [h] using T.t₀_mem
        · intro h
          apply T.core.root_not_mem_T
          simpa only [h] using htbOriginalT
      root_not_mem_T := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_⟩
        · intro h
          apply hbzNotCarrier
          rw [← h]
          exact K.rooted.core.root_mem_carrier
        · intro h
          exact T.core.root_not_mem_S (h.symm ▸ hsS)
      independent_S := by
        intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;>
          rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · exact T.core.independent_T
            (by simpa using T.t₀_mem)
            (by simpa using htbOriginalT)
            htbNeT₀.symm
        · intro hadj
          exact T.core.independent_T
            (by simpa using T.t₀_mem)
            (by simpa using htbOriginalT)
            htbNeT₀.symm hadj.symm
        · exact False.elim (hab rfl)
      clique_T := by
        simpa only [Finset.coe_insert, Finset.coe_singleton,
          SimpleGraph.isClique_pair] using
            (show E.bz ≠ s → G.Adj E.bz s from
              fun _ => hbzS)
      root_adj_S := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact T.root_adj_t₀
        · exact T.core.root_adj_T _ htbOriginalT
      cross_adj := by
        intro t ht v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht hv
        rcases ht with rfl | rfl <;>
          rcases hv with rfl | rfl
        · exact hbzT₀.symm
        · exact T.core.cross_adj _ T.t₀_mem _ hsS
        · exact hbzTb.symm
        · exact T.core.cross_adj _ htbOriginalT _ hsS
    }
    have hyNeT₀ : y ≠ T.t₀ := by
      intro h
      apply hyNotOriginalCarrier
      rw [T.core_eq]
      simp [Core.carrier, Core.S, Core.T, h, T.t₀_mem]
    have hyNeTb : y ≠ tb := by
      intro h
      apply hyNotOriginalCarrier
      rw [T.core_eq]
      simp [Core.carrier, Core.S, Core.T, h, htbOriginalT]
    have hyNeS : y ≠ s := by
      intro h
      apply hyNotOriginalCarrier
      rw [T.core_eq]
      simp [Core.carrier, Core.S, Core.T, h, hsS]
    let R₂ : RootedCore G x y 2 := {
      core := .typeTwo C₂
      other_root_not_mem := by
        simp [Core.carrier, Core.S, Core.T, C₂,
          hyNeX, hyNeT₀, hyNeTb, E.y_ne_bz, hyNeS]
    }
    have hminimal :=
      P.orientation.chosen.type_minimal R₂
    rw [T.core_eq] at hminimal
    change 3 ≤ 2 at hminimal
    omega
  have hbzNotOriginalS : E.bz ∉ T.core.S := by
    intro hbzS
    apply hbzNotCarrier
    exact K.rooted.core.S_subset_carrier
      (by
        simpa [K, TypeThreeModificationChoice.rooted,
          TypeThreeModificationChoice.core, Core.S,
          TypeThreeCore.eraseTerminal] using hbzS)
  have hbzNeX : E.bz ≠ x := by
    intro h
    apply hbzNotCarrier
    rw [h]
    exact K.rooted.core.root_mem_carrier
  have hbzNotAdjX : ¬G.Adj E.bz x := by
    intro h
    have hbzOriginalT : E.bz ∈ T.core.T :=
      (T.root_neighbors E.bz).1 h.symm
    have hbzKT : E.bz ∈ K.core.T :=
      K.mem_core_T_of_mem_original_T_of_ne_t₀
        hbzOriginalT hbzNeT₀
    exact hbzNotCarrier
      (K.rooted.core.T_subset_carrier
        (by simpa [TypeThreeModificationChoice.rooted,
          Core.T] using hbzKT))
  let U₀ : Finset V :=
    K.core.T.filter (G.Adj E.bz)
  have hneighborSet :
      G.neighborSet E.bz ∩
          (↑K.rooted.core.carrier : Set V) =
        (↑U₀ : Set V) := by
    ext v
    constructor
    · rintro ⟨hbzv, hvCarrier⟩
      have hvx : v ≠ x := by
        intro h
        exact hbzNotAdjX (h ▸ hbzv)
      rcases
          K.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
            hvCarrier hvx with
        hvS | hvT
      · have hvOriginalS : v ∈ T.core.S := by
          simpa [K, TypeThreeModificationChoice.rooted,
            TypeThreeModificationChoice.core, Core.S,
            TypeThreeCore.eraseTerminal] using hvS
        exact False.elim
          (hbzNoOriginalS v hvOriginalS hbzv)
      · have hvKT : v ∈ K.core.T := by
          simpa [TypeThreeModificationChoice.rooted,
            Core.T] using hvT
        exact Finset.mem_filter.mpr ⟨hvKT, hbzv⟩
    · intro hv
      have hvData :
          v ∈ K.core.T ∧ G.Adj E.bz v := by
        simpa [U₀] using hv
      exact ⟨hvData.2,
        K.rooted.core.T_subset_carrier
          (by simpa [TypeThreeModificationChoice.rooted,
            Core.T] using hvData.1)⟩
  have hU₀Card :
      U₀.card = P.orientation.chosen.rank + 1 := by
    rw [hneighborSet, Set.ncard_coe_finset] at hcount
    exact hcount
  have ht₀NotU₀ : T.t₀ ∉ U₀ := by
    intro ht
    have htK : T.t₀ ∈ K.core.T := by
      exact (Finset.mem_filter.mp ht).1
    exact K.t₀_not_mem_core_T htK
  let U : Finset V :=
    insert T.t₀ U₀
  have hUCard :
      U.card = P.orientation.chosen.rank + 2 := by
    simp [U, ht₀NotU₀, hU₀Card]
  have hUOriginal : U ⊆ T.core.T := by
    intro v hv
    simp only [U, Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact T.t₀_mem
    · have hvKT : v ∈ K.core.T :=
        (Finset.mem_filter.mp hv).1
      simpa [K, TypeThreeModificationChoice.core,
        TypeThreeCore.eraseTerminal] using
          Finset.mem_of_mem_erase hvKT
  have hULower :
      max ((P.orientation.chosen.rank + 1) + 1) 2 ≤
        U.card := by
    rw [hUCard]
    omega
  have hbzNotU : E.bz ∉ U := by
    intro hbzU
    simp only [U, Finset.mem_insert] at hbzU
    rcases hbzU with h | h
    · exact hbzNeT₀ h
    · exact G.loopless.irrefl E.bz
        (Finset.mem_filter.mp h).2
  have hbzAdjU :
      ∀ t ∈ U, G.Adj E.bz t := by
    intro t ht
    simp only [U, Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact hbzT₀
    · exact (Finset.mem_filter.mp ht).2
  let C₃ :
      TypeThreeCore G x
        (P.orientation.chosen.rank + 1) :=
    T.core.insertInitial E.bz U hUOriginal hULower
      hbzNeX hbzNotOriginalS hbzNotU
      hbzNoOriginalS hbzAdjU
  have hyOriginalS : y ∉ T.core.S := by
    intro hyS
    apply hyNotOriginalCarrier
    rw [T.core_eq]
    exact (Core.typeThree T.core).S_subset_carrier hyS
  have hyU : y ∉ U := by
    intro hyU
    have hyOriginalT := hUOriginal hyU
    apply hyNotOriginalCarrier
    rw [T.core_eq]
    exact (Core.typeThree T.core).T_subset_carrier
      hyOriginalT
  let R₃ :
      RootedCore G x y
        (P.orientation.chosen.rank + 1) := {
    core := .typeThree C₃
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C₃,
        TypeThreeCore.insertInitial, hyNeX,
        E.y_ne_bz, hyOriginalS, hyU]
  }
  have htype :
      R₃.core.typeNumber =
        P.orientation.chosen.rooted.core.typeNumber := by
    rw [T.core_eq]
    rfl
  have hmax :=
    P.orientation.chosen.S_maximal R₃ htype
  have hcardNew :
      R₃.core.S.card =
        P.orientation.chosen.rank + 1 := by
    simp [R₃, C₃, Core.S,
      TypeThreeCore.insertInitial,
      hbzNotOriginalS, T.core.card_S]
  have hcardOld :
      P.orientation.chosen.rooted.core.S.card =
        P.orientation.chosen.rank := by
    rw [T.core_eq]
    exact T.core.card_S
  rw [hcardNew, hcardOld] at hmax
  omega

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
