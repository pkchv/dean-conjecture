import DeanK5.COYExteriorBlockChainCoverage
import DeanK5.COYExteriorChosenRootAttachment
import DeanK5.COYExteriorClaimThreeFourteen
import DeanK5.COYExteriorClaimThreeSixteenTerminalAssembly

/-!
# Closing the terminal last-feasible-block branch

Suppose that the last feasible exterior block is the final block of the
ordered chain.  The terminal version of Claim 3.16 excludes terminal-side
attachments in every earlier block, while equation (3.4) excludes them in
the final block away from `y`.  Block coverage then contradicts Claim
3.14(2).
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
Terminal form of Claim 3.16: no `T`-vertex is adjacent to a vertex in a
block strictly before the selected terminal last feasible block.
-/
theorem claim_three_sixteen_terminal_blockwise
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hS : D.core.S = {s})
    (t : V)
    (ht : t ∈ D.core.T)
    (i : Fin (O.chain.cutCount + 1))
    (hi : i.1 < L.index.1)
    (d : P.ExteriorVertex)
    (hd : d ∈ (O.chain.blocks i).carrier) :
    ¬G.Adj t d.1 := by
  intro htd
  exact
    O.false_of_terminal_attachment_before_terminalLastFeasible
      M D hregion hall L hS i hi d hd ht htd

/--
The branch in which the selected last feasible block is the terminal block
is impossible.
-/
theorem false_of_terminal_lastFeasible
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion) :
    False := by
  let A :=
    L.choice.chosenRootAttachmentData M D
  have hnoExteriorAttachment :
      ¬P.HasExteriorAttachmentAwayFrom
        D.core.T y := by
    apply
      O.not_hasExteriorAttachmentAwayFrom_of_selected_last
        hregion D.core.T L.index
          L.index_eq_cutCount
    · intro i hi d hd t ht
      exact
        O.claim_three_sixteen_terminal_blockwise
          M D hregion hall L A.side_eq
            t ht i hi d hd
    · intro d hd hdY t ht
      have hindex :
          L.index = O.lastIndex := by
        apply Fin.ext
        simpa [ExteriorOrderedBlockChain.lastIndex] using
          L.index_eq_cutCount
      have hdChoice :
          d ∈ L.choice.block.carrier := by
        rw [L.block_eq_last]
        simpa [hindex] using hd
      have hdAmbient :
          d.1 ∈ L.choice.ambientCarrier := by
        apply L.choice.mem_ambientCarrier.mpr
        exact ⟨d, hdChoice, rfl⟩
      have htWorking :
          t ∈ P.working.rooted.core.T := by
        simpa [D.core_eq, Core.T] using ht
      exact
        L.equation_three_four
          t htWorking d.1 hdAmbient hdY
  have hattachment :
      P.HasTAttachmentAwayFromY D.core :=
    P.hasTAttachmentAwayFromY_of_exception_mem
      M D.core D.core_eq A.side_eq hregion
        O.endpoints.z_mem_otherRegion
  apply hnoExteriorAttachment
  simpa [PreferredWorkingCoreData.HasExteriorAttachmentAwayFrom,
    PreferredWorkingCoreData.HasTAttachmentAwayFromY] using
      hattachment

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
