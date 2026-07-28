import DeanK5.COYExteriorClaimThreeSixteenAssemblyChain

/-!
# COY Claim 3.16: exclusion of earlier terminal attachments

Let `B_p` be the selected last feasible block in the exterior chain.  If a
vertex of the terminal side `T` of the working core were adjacent to a
vertex of an earlier block, the Claim 3.16 path assembly would produce the
forbidden ambient admissible family.  Thus no such attachment exists.

The first theorem below is the blockwise form used in the source argument.
The second packages the same conclusion over the finite union of all blocks
strictly before `B_p`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorOrderedBlockChain

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}

/--
COY Claim 3.16, in curried blockwise form: a terminal-side core vertex has
no neighbor in any block strictly before the selected last feasible block.
-/
theorem claim_three_sixteen_blockwise
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hS : D.core.S = {s})
    (t : V)
    (ht : t ∈ D.core.T)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < L.index.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier) :
    ¬G.Adj t a.1 := by
  intro hta
  have hpositive : 0 < L.index.1 := by
    omega
  exact
    O.false_of_terminal_attachment_before_lastFeasible
      M D hregion hall L hpositive hS i hip a ha ht hta

/--
Finite-union form of Claim 3.16: the terminal side has no attachment to the
union of the block carriers strictly before the selected block.
-/
theorem claim_three_sixteen_blocksBeforeCarrier
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hS : D.core.S = {s})
    (t : V)
    (ht : t ∈ D.core.T)
    (a : P.ExteriorVertex)
    (ha :
      a ∈ O.chain.blocksBeforeCarrier L.index.1) :
    ¬G.Adj t a.1 := by
  obtain ⟨i, hip, haBlock⟩ :=
    (O.chain.mem_blocksBeforeCarrier).1 ha
  exact
    O.claim_three_sixteen_blockwise
      M D hregion hall L hS t ht i hip a haBlock

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
