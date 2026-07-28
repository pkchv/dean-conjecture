import DeanK5.COYExteriorClaimThreeThirteenClose
import DeanK5.COYModifiedExteriorCut

/-!
# The attachment bound after COY Claim 3.13

At the Type III rank-one stage, every ordinary exterior vertex has at most
one neighbour in the selected working core.  Claim 3.3 first bounds the
number by two.  Equality supplies a `T`-neighbour and excludes adjacency to
the core root.  Two `T`-neighbours would give a Type I witness; one
`T`-neighbour and the remaining `S`-neighbour would give a Type II witness.
Both alternatives contradict Claim 3.13.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.TypeThreeStage

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/--
Every exterior ordinary vertex avoids the extra vertex omitted from the
selected-core form of Claim 3.3.
-/
theorem ordinary_ne_excludedVertex
    (ordinary : P.ExteriorOrdinaryVertex) :
    ordinary.vertex.1 ≠ P.working.excludedVertex := by
  rcases P.working.excludedVertex_eq_otherRoot_or_exteriorCut with
    heq | ⟨hmem, hcut⟩
  · intro h
    exact ordinary.ne_y (h.trans heq)
  · intro h
    apply ordinary.not_cut
    have hsubtype :
        ordinary.vertex =
          (⟨P.working.excludedVertex, hmem⟩ :
            P.ExteriorVertex) := by
      apply Subtype.ext
      exact h
    exact hsubtype ▸ hcut

/-- Terminal-side neighbours form a subset of all selected-core neighbours. -/
theorem terminalNeighbor_subset_coreNeighbors
    (D : P.TypeThreeStage)
    (v : V) :
    (↑(D.terminalNeighborFinset v) : Set V) ⊆
      G.neighborSet v ∩
        (↑P.working.rooted.core.carrier : Set V) := by
  intro t ht
  have htData :=
    D.mem_terminalNeighborFinset.mp ht
  refine ⟨htData.2, ?_⟩
  rw [D.core_eq]
  exact
    (Core.typeThree D.core).T_subset_carrier
      (by simpa [Core.T] using htData.1)

/--
COY equation (3.3): an exterior non-cut vertex outside the two protected
vertices has at most one neighbour in the selected working core.
-/
theorem coreNeighbor_ncard_le_one
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    (ordinary : P.ExteriorOrdinaryVertex) :
    (G.neighborSet ordinary.vertex.1 ∩
      (↑P.working.rooted.core.carrier : Set V)).ncard ≤ 1 := by
  classical
  have hclaim := D.claim_three_thirteen M
  have hrank : P.working.rank = 1 :=
    hclaim.1
  have htypeIII : D.IsTypeIII :=
    hclaim.2
  have hvNotCarrier :
      ordinary.vertex.1 ∉
        P.working.rooted.core.carrier :=
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      ordinary.vertex.2
  have hvExcluded :
      ordinary.vertex.1 ≠ P.working.excludedVertex :=
    ordinary_ne_excludedVertex ordinary
  have hupper :=
    P.working.coreNeighbor_ncard_le
      hvNotCarrier ordinary.ne_y hvExcluded
  by_contra hnot
  have htwo :
      (G.neighborSet ordinary.vertex.1 ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard = 2 := by
    omega
  have hequality :
      (G.neighborSet ordinary.vertex.1 ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard =
          P.working.rank + 1 := by
    omega
  obtain ⟨t, htWorking, hvt⟩ :=
    P.working.exists_T_neighbor_of_coreNeighbor_ncard_eq
      hvNotCarrier ordinary.ne_y hvExcluded hequality
  have htCore : t ∈ D.core.T := by
    simpa [D.core_eq, Core.T] using htWorking
  have htNeighbor :
      t ∈ D.terminalNeighborFinset ordinary.vertex.1 :=
    D.mem_terminalNeighborFinset.mpr
      ⟨htCore, hvt⟩
  have hterminalPositive :
      1 ≤
        (D.terminalNeighborFinset
          ordinary.vertex.1).card :=
    Finset.one_le_card.mpr ⟨t, htNeighbor⟩
  have hterminalUpper :
      (D.terminalNeighborFinset
        ordinary.vertex.1).card ≤ 2 := by
    rw [← Set.ncard_coe_finset]
    calc
      (↑(D.terminalNeighborFinset
          ordinary.vertex.1) : Set V).ncard ≤
          (G.neighborSet ordinary.vertex.1 ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard :=
        Set.ncard_le_ncard
          (D.terminalNeighbor_subset_coreNeighbors
            ordinary.vertex.1)
      _ = 2 := htwo
  have hnotRoot :
      ¬G.Adj x ordinary.vertex.1 :=
    P.working.not_adj_root_of_typeThree_of_T_neighbor
      D.core D.core_eq hvNotCarrier ordinary.ne_y
      hvExcluded htWorking hvt
  by_cases hterminalTwo :
      (D.terminalNeighborFinset
        ordinary.vertex.1).card = 2
  · apply htypeIII.1
    exact ⟨{
      ordinary := ordinary
      terminal_neighbor_card := by
        omega
    }⟩
  · have hterminalOne :
        (D.terminalNeighborFinset
          ordinary.vertex.1).card = 1 := by
      omega
    have hinitialPositive :
        1 ≤
          (D.initialNeighborFinset
            ordinary.vertex.1).card := by
      by_contra hzero
      have hinitialEmpty :
          D.initialNeighborFinset
            ordinary.vertex.1 = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      have hcoreSubsetTerminal :
          G.neighborSet ordinary.vertex.1 ∩
              (↑P.working.rooted.core.carrier : Set V) ⊆
            (↑(D.terminalNeighborFinset
              ordinary.vertex.1) : Set V) := by
        intro u hu
        have huAdj :
            G.Adj ordinary.vertex.1 u :=
          hu.1
        have huCarrier :
            u ∈ (Core.typeThree D.core).carrier := by
          simpa [D.core_eq] using hu.2
        have huParts :
            u = x ∨ u ∈ D.core.S ∨ u ∈ D.core.T := by
          simpa [Core.carrier, Core.S, Core.T] using
            huCarrier
        rcases huParts with rfl | huS | huT
        · exact False.elim (hnotRoot huAdj.symm)
        · have huInitial :
              u ∈ D.initialNeighborFinset
                ordinary.vertex.1 :=
            D.mem_initialNeighborFinset.mpr
              ⟨huS, huAdj⟩
          rw [hinitialEmpty] at huInitial
          simp at huInitial
        · exact
            D.mem_terminalNeighborFinset.mpr
              ⟨huT, huAdj⟩
      have hcardLe :
          (G.neighborSet ordinary.vertex.1 ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard ≤
              (↑(D.terminalNeighborFinset
                ordinary.vertex.1) : Set V).ncard :=
        Set.ncard_le_ncard hcoreSubsetTerminal
      rw [htwo, Set.ncard_coe_finset,
        hterminalOne] at hcardLe
      omega
    have hinitialUpper :
        (D.initialNeighborFinset
          ordinary.vertex.1).card ≤ 1 := by
      have hsubset :
          D.initialNeighborFinset
            ordinary.vertex.1 ⊆ D.core.S :=
        Finset.filter_subset _ _
      have hcard :=
        Finset.card_le_card hsubset
      rw [D.core.card_S] at hcard
      omega
    have hinitialOne :
        (D.initialNeighborFinset
          ordinary.vertex.1).card = 1 := by
      omega
    apply htypeIII.2
    exact ⟨{
      ordinary := ordinary
      rank_eq_one := hrank
      initial_neighbor_card := hinitialOne
      terminal_neighbor_card := hterminalOne
    }⟩

end PreferredWorkingCoreData.TypeThreeStage

end COY

end DeanK5
