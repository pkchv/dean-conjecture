import DeanK5.COYSingletonExteriorOtherComponents
import DeanK5.COYSingletonExteriorTypeOne
import DeanK5.COYSingletonExteriorTypeTwo
import DeanK5.COYSingletonExteriorTypeThreeDeletion

/-!
# Eliminating the singleton exterior in the COY core argument

COY Case 1 treats the possibility that the deletion component containing
the second root is the singleton `{y}`.  The modified working core is
excluded by Claim 3.4.  In the natural branch, the three possible core
types are eliminated by the internally formalized Case 1.1--1.3
arguments.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
In a natural type-1 singleton exterior, every ambient vertex belongs to
the clique side of the core or is one of the three protected vertices.
-/
private theorem typeOne_singleton_cover
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty
        (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (C : TypeOneCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeOne C) :
    (Finset.univ : Finset V) ⊆ C.T ∪ {x, y, z} := by
  classical
  intro v _
  by_cases hvCarrier :
      v ∈ D.chosen.rooted.core.carrier
  · have hvClass : v = x ∨ v ∈ C.T := by
      rw [hcore] at hvCarrier
      simpa [Core.carrier, Core.S, Core.T] using
        hvCarrier
    rcases hvClass with rfl | hvT
    · simp
    · exact Finset.mem_union_left _ hvT
  · let vDeleted :
        {w : V // w ∉ D.chosen.rooted.core.carrier} :=
      ⟨v, hvCarrier⟩
    let K :=
      (deleteVertices G
        D.chosen.rooted.core.carrier).connectedComponentMk
        vDeleted
    have hvK :
        v ∈ componentVertices G
          D.chosen.rooted.core.carrier K := by
      apply
        (mem_componentVertices_iff
          G D.chosen.rooted.core.carrier K v).2
      exact
        ⟨hvCarrier,
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    by_cases hK :
        K = D.chosen.rooted.otherComponent
    · have hvRegion :
          v ∈ D.chosen.rooted.otherRegion := by
        simpa [RootedCore.otherRegion, hK] using hvK
      change D.chosen.rooted.otherRegion = {y} at hregion
      rw [hregion] at hvRegion
      have hvy : v = y := by
        simpa using hvRegion
      simp [hvy]
    · have hvz : v = z := by
        by_contra hvz
        exact
          D.no_ordinary_other_component_of_natural_singleton_typeOne
            M hnot hregion C hcore K hK
            ⟨v, hvK, hvz⟩
      simp [hvz]

/--
The deletion component containing the second root is never a singleton in
a minimal counterexample.
-/
theorem selectedWorkingCore_otherRegion_ne_singleton
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (W : SelectedWorkingCore (z := z) D.chosen) :
    W.rooted.otherRegion ≠ {y} := by
  classical
  intro hregion
  obtain ⟨hnot, hW⟩ :=
    W.eq_natural_of_otherRegion_eq_singleton
      M.left_root_not_adj_exception hregion
  subst W
  cases hcore : D.chosen.rooted.core with
  | typeOne C =>
      have htype :
          D.chosen.rooted.core.typeNumber = 1 := by
        rw [hcore]
        rfl
      have hneighbors :=
        D.neighborSets_eq_T_of_natural_singleton
          M hnot hregion (Or.inl htype)
      have hneighborRight :
          G.neighborSet y = (↑C.T : Set V) := by
        simpa [hcore, Core.T] using hneighbors.2
      have hneighborLeft :
          G.neighborSet x = (↑C.T : Set V) :=
        hneighbors.1.trans hneighborRight
      have hQ :
          ComponentRegion G
            (insert x C.T)
            D.chosen.rooted.otherRegion := by
        simpa [hcore, Core.carrier, Core.S, Core.T] using
          D.chosen.rooted.otherRegion_componentRegion
      have hrankStrong :
          D.chosen.rank + 1 < q :=
        C.rank_add_one_lt_of_component
          hQ D.chosen.rooted.other_root_mem_otherRegion
          M.rooted_two_connected M.q_pos M.q_le_four M.no_paths
      have hcardUpper : C.T.card ≤ q - 1 := by
        rw [C.card_T]
        omega
      have hcover :=
        M.typeOne_singleton_cover D hnot hregion C hcore
      obtain ⟨ordinary, hox, hoy, hoz⟩ :=
        M.ordinary_nonempty
      have hoT : ordinary ∈ C.T := by
        have hoCover := hcover (Finset.mem_univ ordinary)
        rcases Finset.mem_union.mp hoCover with
          hoT | hoProtected
        · exact hoT
        · simp only [Finset.mem_insert,
            Finset.mem_singleton] at hoProtected
          rcases hoProtected with rfl | rfl | rfl
          · exact False.elim (hox rfl)
          · exact False.elim (hoy rfl)
          · exact False.elim (hoz rfl)
      have hordinary :
          (C.T \ {z}).Nonempty := by
        exact
          ⟨ordinary,
            Finset.mem_sdiff.mpr
              ⟨hoT, by simpa using hoz⟩⟩
      exact
        D.chosen.contradiction_of_natural_singleton_typeOne
          M C hcore hneighborLeft hneighborRight
          hcover hcardUpper hordinary
  | typeTwo C =>
      exact
        M.false_of_natural_singleton_typeTwo
          D hnot hregion (by rw [hcore]; rfl)
  | typeThree C =>
      exact
        M.false_of_natural_singleton_typeThree
          D hnot hregion (by rw [hcore]; rfl)

end MinimalCounterexample

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The selected working exterior contains a vertex other than `y`. -/
theorem otherRegion_ne_singleton
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z) :
    P.working.rooted.otherRegion ≠ {y} :=
  M.selectedWorkingCore_otherRegion_ne_singleton
    P.orientation P.working

end PreferredWorkingCoreData

end COY

end DeanK5
