import DeanK5.COYExteriorClaimThreeEleven
import DeanK5.Graph.FeasibleBlockAnchor

/-!
# Selecting and anchoring the feasible exterior block

After COY Claim 3.11 supplies a feasible block, the source choices
(B1)--(B3) orient it toward the second root and retain at most one further
exceptional vertex.  `ExteriorFeasibleBlockChoice` records exactly that
common interface.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
A feasible block of the selected exterior together with its uniform
orientation toward the exterior copy of `y`.
-/
structure ExteriorFeasibleBlockChoice
    (P : PreferredWorkingCoreData G x y z) where
  /-- The feasible block supplied by Claim 3.11. -/
  block : GraphBlock P.exteriorGraph
  /-- The source feasibility condition for the selected block. -/
  feasible :
    IsFeasibleBlock
      P.exteriorGraph P.exteriorProtected block
  /-- The uniform content of the source choices (B1)--(B3). -/
  anchor :
    FeasibleBlockAnchor
      P.exteriorGraph P.exteriorProtected block P.exteriorY

namespace ExteriorFeasibleBlockChoice

variable {P : PreferredWorkingCoreData G x y z}

/-- The ambient vertex represented by the selected block anchor. -/
abbrev b (C : P.ExteriorFeasibleBlockChoice) : V :=
  C.anchor.b.1

/-- The ambient vertex represented by the possible second exception. -/
abbrev zPrime (C : P.ExteriorFeasibleBlockChoice) : V :=
  C.anchor.zPrime.1

/-- The ambient ordinary vertex certified by feasibility. -/
abbrev ordinary (C : P.ExteriorFeasibleBlockChoice) : V :=
  C.anchor.ordinary.1

/-- The fixed anchor-to-`y` connector, viewed in the ambient graph. -/
noncomputable def pathToY
    (C : P.ExteriorFeasibleBlockChoice) :
    SimplePath G C.b y :=
  C.anchor.pathToTarget.mapInjectiveHom
    P.exteriorEmbedding.toHom Subtype.val_injective

/-- Every ambient vertex on the fixed connector belongs to the exterior. -/
theorem pathToY_support_mem_otherRegion
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.pathToY.walk.support) :
    v ∈ P.working.rooted.otherRegion := by
  have hvRange :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := C.anchor.pathToTarget)
      (f := P.exteriorEmbedding.toHom)
      (hinj := Subtype.val_injective)
      (by
        change
          v ∈
            (C.anchor.pathToTarget.mapInjectiveHom
              P.exteriorEmbedding.toHom
              Subtype.val_injective).walk.support at hv
        exact hv)
  obtain ⟨w, rfl⟩ := hvRange
  exact w.2

/-- The ambient connector from `b` to `y` does not re-enter the block. -/
theorem pathToY_meets_block_only_at_b
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.pathToY.walk.support)
    (hvBlock :
      ∃ w ∈ C.block.carrier, w.1 = v) :
    v = C.b := by
  change
    v ∈
      (C.anchor.pathToTarget.walk.map
        P.exteriorEmbedding.toHom).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨u, huSupport, huMap⟩ :=
    List.mem_map.mp hv
  obtain ⟨w, hwBlock, hwVal⟩ := hvBlock
  have huw : u = w := by
    apply Subtype.ext
    exact huMap.trans hwVal.symm
  have huBlock : u ∈ C.block.carrier := by
    simpa [huw] using hwBlock
  have hub : u = C.anchor.b :=
    C.anchor.path_meets_carrier_only_at_b
      huSupport huBlock
  exact huMap.symm.trans
    (congrArg Subtype.val hub)

end ExteriorFeasibleBlockChoice

/--
Claim 3.11 together with the generic feasible-block orientation produces
the selected source block data for every nonsingleton exterior.
-/
theorem exists_exteriorFeasibleBlockChoice
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    Nonempty P.ExteriorFeasibleBlockChoice := by
  classical
  obtain ⟨B, hfeasible⟩ :=
    P.exists_feasible_exterior_block M hregion
  obtain ⟨anchor⟩ :=
    B.exists_feasibleBlockAnchor
      P.exteriorGraph_connected P.exteriorProtected
        P.exteriorY P.exteriorY_mem_exteriorProtected
        hfeasible
  exact ⟨{
    block := B
    feasible := hfeasible
    anchor := anchor
  }⟩

end PreferredWorkingCoreData

end COY

end DeanK5
