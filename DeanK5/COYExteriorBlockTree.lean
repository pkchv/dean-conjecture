import DeanK5.COYExteriorClaimThreeFifteen
import DeanK5.Graph.BlockCutLeaves
import DeanK5.Graph.BlockCutTree

/-!
# The block--cut tree after COY Claim 3.15

This file translates the local conclusion of COY Claim 3.15 for every
feasible exterior block into the generic marked-leaf interface for the
block--cut tree.  Claim 3.15(2) rules out the degenerate one-block case.
The two protected exterior vertices then bound the tree to exactly two
leaves and force maximum degree two.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- Finiteness of the selected exterior's block--cut nodes. -/
noncomputable local instance exteriorBlockCutNodeFintype
    (P : PreferredWorkingCoreData G x y z) :
    Fintype (BlockCutNode P.exteriorGraph) :=
  Fintype.ofFinite _

/-- Decidable adjacency in the selected exterior's block--cut incidence graph. -/
noncomputable local instance exteriorBlockCutAdjDecidable
    (P : PreferredWorkingCoreData G x y z) :
    DecidableRel (blockCutIncidence P.exteriorGraph).Adj :=
  Classical.decRel _

/--
Claim 3.15(1), uniformly over every feasible block of the selected
exterior.
-/
def AllFeasibleBlocksMeetProtectedInterior
    (P : PreferredWorkingCoreData G x y z) : Prop :=
  ∀ C : P.ExteriorFeasibleBlockChoice,
    C.MeetsProtectedInterior

/-- Claim 3.15 supplies the uniform feasible-block conclusion. -/
theorem allFeasibleBlocksMeetProtectedInterior
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage) :
    P.AllFeasibleBlocksMeetProtectedInterior := by
  intro C
  exact C.claim_three_fifteen_part_one M D

/--
The uniform conclusion of Claim 3.15(1) is exactly the anchored-block
hypothesis used by the generic marked-leaf theorem.
-/
theorem anchoredBlockMeetsExceptions_of_allFeasibleBlocks
    (P : PreferredWorkingCoreData G x y z)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    BlockCutIncidence.AnchoredBlockMeetsExceptions
      P.exteriorGraph P.exteriorProtected P.exteriorY := by
  intro B hfeasible A
  let C : P.ExteriorFeasibleBlockChoice := {
    block := B
    feasible := hfeasible
    anchor := A
  }
  rcases hall C with hy | hzPrime
  · have hyCarrier : y ∈ C.ambientCarrier :=
      Finset.mem_of_mem_erase hy
    obtain ⟨w, hwB, hwValue⟩ :=
      C.mem_ambientCarrier.mp hyCarrier
    have hwY : w = P.exteriorY := by
      apply Subtype.ext
      exact hwValue
    refine ⟨P.exteriorY, ?_, Or.inl rfl⟩
    apply Finset.mem_erase.mpr
    constructor
    · intro hYb
      have hyb : y = C.b :=
        congrArg Subtype.val hYb
      exact (Finset.mem_erase.mp hy).1 hyb
    · simpa [C, hwY] using hwB
  · have hzCarrier : C.zPrime ∈ C.ambientCarrier :=
      Finset.mem_of_mem_erase hzPrime
    obtain ⟨w, hwB, hwValue⟩ :=
      C.mem_ambientCarrier.mp hzCarrier
    have hwPrime : w = A.zPrime := by
      apply Subtype.ext
      exact hwValue
    refine ⟨A.zPrime, ?_, Or.inr rfl⟩
    apply Finset.mem_erase.mpr
    constructor
    · intro hPrimeB
      have hzB : C.zPrime = C.b :=
        congrArg Subtype.val hPrimeB
      exact (Finset.mem_erase.mp hzPrime).1 hzB
    · simpa [C, hwPrime] using hwB

/--
Claim 3.15(2) supplies a second incidence node: a feasible block cannot
span the selected exterior, so an exterior vertex outside it lies in a
different block.
-/
theorem exteriorBlockCutNode_nontrivial
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    Nontrivial (BlockCutNode P.exteriorGraph) := by
  classical
  obtain ⟨C⟩ :=
    P.exists_exteriorFeasibleBlockChoice M hregion
  have hnotSpan :
      ¬C.SpansExterior :=
    C.not_spansExterior_of_meetsProtectedInterior
      M D (hall C)
  have houtside :
      ∃ v ∈ P.working.rooted.otherRegion,
        v ∉ C.ambientCarrier := by
    by_contra hnone
    push Not at hnone
    apply hnotSpan
    apply Finset.Subset.antisymm
    · exact C.ambientCarrier_subset_otherRegion
    · intro v hv
      exact hnone v hv
  obtain ⟨v, hvRegion, hvOutside⟩ := houtside
  let w : P.ExteriorVertex := ⟨v, hvRegion⟩
  have horder :
      2 ≤ Fintype.card P.ExteriorVertex := by
    have := P.one_lt_exteriorVertex_card hregion
    omega
  obtain ⟨B, hwB⟩ :=
    GraphBlock.exists_of_vertex
      P.exteriorGraph_connected horder w
  have hBC : B ≠ C.block := by
    intro hBC
    subst B
    apply hvOutside
    apply C.mem_ambientCarrier.mpr
    exact ⟨w, hwB, rfl⟩
  exact
    ⟨⟨(.inl B : BlockCutNode P.exteriorGraph),
      .inl C.block, by
        intro h
        exact hBC (Sum.inl.inj h)⟩⟩

/-- The selected exterior has the standard finite block--cut tree. -/
theorem exteriorBlockCutIncidence_isTree
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    (blockCutIncidence P.exteriorGraph).IsTree := by
  apply BlockCutIncidence.isTree P.exteriorGraph_connected
  have := P.one_lt_exteriorVertex_card hregion
  omega

/--
After Claim 3.15, the exterior block--cut tree has exactly two leaves.
-/
theorem exteriorBlockCutIncidence_leafVertices_card_eq_two
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    (TreePath.leafVertices
      (blockCutIncidence P.exteriorGraph)).card = 2 := by
  letI : Nontrivial (BlockCutNode P.exteriorGraph) :=
    P.exteriorBlockCutNode_nontrivial M D hregion hall
  exact
    BlockCutIncidence.incidence_leafVertices_card_eq_two
      (P.exteriorBlockCutIncidence_isTree hregion)
      P.exteriorGraph_connected
      P.exteriorProtected P.exteriorY
      P.exteriorY_mem_exteriorProtected
      P.exteriorProtected_card_le_two
      (P.anchoredBlockMeetsExceptions_of_allFeasibleBlocks hall)

/--
After Claim 3.15, every node of the exterior block--cut tree has degree at
most two.
-/
theorem exteriorBlockCutIncidence_degree_le_two
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (n : BlockCutNode P.exteriorGraph) :
    (blockCutIncidence P.exteriorGraph).degree n ≤ 2 := by
  letI : Nontrivial (BlockCutNode P.exteriorGraph) :=
    P.exteriorBlockCutNode_nontrivial M D hregion hall
  exact
    BlockCutIncidence.incidence_degree_le_two
      (P.exteriorBlockCutIncidence_isTree hregion)
      P.exteriorGraph_connected
      P.exteriorProtected P.exteriorY
      P.exteriorY_mem_exteriorProtected
      P.exteriorProtected_card_le_two
      (P.anchoredBlockMeetsExceptions_of_allFeasibleBlocks hall)
      n

end PreferredWorkingCoreData

end COY

end DeanK5
