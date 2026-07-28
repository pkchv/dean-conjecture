import DeanK5.COYExteriorBlockChainCoverage
import DeanK5.COYExteriorClaimThreeFourteen
import DeanK5.COYExteriorClaimThreeSixteenNoEarlier
import DeanK5.COYExteriorFinalRootData

/-!
# Closing the nonterminal last-feasible-block branch

Let `B_p` be the last feasible block of the exterior chain and suppose that
it is not the final block.  Claim 3.16 excludes terminal-side attachments
before `B_p`, while equation (3.4) excludes them inside `B_p` away from its
right cut.

If `B_p` is penultimate, the final block consists only of that cut and `y`;
the exact root-neighborhood data also excludes terminal attachments at the
cut.  This contradicts Claim 3.14(2).  If at least two blocks follow `B_p`,
the final cut differs from the chosen exterior neighbor of `x`.  The exact
root neighborhoods then exclude both the root and the terminal side at that
cut, and the final degree bound gives the contradiction.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorOrderedBlockChain

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/--
For a nonterminal last feasible block, maximality makes the final block a
two-vertex block consisting of the final cut and `y`.
-/
theorem lastBlock_carrier_eq_terminalCut_pair
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion) :
    (O.chain.blocks O.lastIndex).carrier =
      {(O.chain.cuts O.terminalCutIndex).1, P.exteriorY} := by
  have hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 <
        O.chain.cutCount := by
    rw [← L.index_eq_lastFeasible]
    exact L.index_lt_cutCount
  have hcard :
      (O.chain.blocks O.lastIndex).carrier.card = 2 := by
    simpa [ExteriorOrderedBlockChain.lastIndex] using
      O.terminal_block_card_eq_two_of_lastFeasible_before
        M hregion hall hbefore
  have hcutMem :
      (O.chain.cuts O.terminalCutIndex).1 ∈
        (O.chain.blocks O.lastIndex).carrier := by
    have hmem :=
      O.chain.cut_mem_right O.terminalCutIndex
    have hindex :
        (⟨O.terminalCutIndex.1 + 1, by omega⟩ :
          Fin (O.chain.cutCount + 1)) =
            O.lastIndex := by
      apply Fin.ext
      dsimp [terminalCutIndex,
        ExteriorOrderedBlockChain.lastIndex]
      have := O.chain.one_le_cutCount
      omega
    simpa [hindex] using hmem
  have hcutNeY :
      (O.chain.cuts O.terminalCutIndex).1 ≠
        P.exteriorY := by
    intro h
    apply O.terminalCut_ne_y
    exact congrArg Subtype.val h
  exact
    (O.chain.blocks O.lastIndex).carrier_eq_pair_of_card_eq_two
      hcard hcutMem O.y_mem_last_block hcutNeY

/--
Equation (3.4), expressed on the selected chain block: every terminal-side
vertex avoids every selected-block vertex other than the right cut.
-/
theorem selectedBlock_terminal_exclusion
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (d : P.ExteriorVertex)
    (hd : d ∈ (O.chain.blocks L.index).carrier)
    (hdRight :
      d ≠
        (O.chain.cuts
          ⟨L.index.1, L.index_lt_cutCount⟩).1)
    (t : V)
    (ht : t ∈ D.core.T) :
    ¬G.Adj t d.1 := by
  have hdAmbient :
      d.1 ∈ L.choice.ambientCarrier := by
    apply L.choice.mem_ambientCarrier.mpr
    refine ⟨d, ?_, rfl⟩
    simpa [L.block_eq] using hd
  have hdAnchor :
      d.1 ≠ L.choice.b := by
    intro h
    apply hdRight
    apply Subtype.ext
    exact h.trans L.b_eq_rightCut
  have htWorking :
      t ∈ P.working.rooted.core.T := by
    simpa [D.core_eq, Core.T] using ht
  exact
    L.equation_three_four
      t htWorking d.1 hdAmbient hdAnchor

/--
The branch in which the selected last feasible block is nonterminal is
impossible.
-/
theorem false_of_nonterminal_lastFeasible
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (L : P.ExteriorLastFeasibleAnchor M O hregion) :
    False := by
  let R :=
    L.finalRootData D hall
  by_cases hpenultimate :
      L.index.1 + 1 = O.chain.cutCount
  · let terminalCut : P.ExteriorVertex :=
      (O.chain.cuts O.terminalCutIndex).1
    have hrightIndex :
        (⟨L.index.1, L.index_lt_cutCount⟩ :
          Fin O.chain.cutCount) =
            O.terminalCutIndex := by
      apply Fin.ext
      dsimp [terminalCutIndex]
      omega
    have hfinalCarrier :
        (O.chain.blocks O.lastIndex).carrier =
          {terminalCut, P.exteriorY} := by
      simpa [terminalCut] using
        O.lastBlock_carrier_eq_terminalCut_pair
          M hregion hall L
    have hnoExteriorAttachment :
        ¬P.HasExteriorAttachmentAwayFrom
          D.core.T y := by
      apply
        O.not_hasExteriorAttachmentAwayFrom_of_selected_penultimate
          hregion D.core.T L.index hpenultimate
          terminalCut hfinalCarrier
      · intro t ht hAdj
        exact R.terminalCut_not_adj_terminal t ht hAdj.symm
      · intro i hi d hd t ht
        exact
          O.claim_three_sixteen_blockwise
            M D hregion hall L R.side_eq
              t ht i hi d hd
      · intro d hd hdCut t ht
        apply
          O.selectedBlock_terminal_exclusion
            M D hregion L d hd
              (by simpa [terminalCut, hrightIndex] using hdCut)
              t ht
    have hattachment :
        P.HasTAttachmentAwayFromY D.core :=
      P.hasTAttachmentAwayFromY_of_exception_mem
        M D.core D.core_eq R.side_eq hregion
          O.endpoints.z_mem_otherRegion
    apply hnoExteriorAttachment
    simpa [PreferredWorkingCoreData.HasExteriorAttachmentAwayFrom,
      PreferredWorkingCoreData.HasTAttachmentAwayFromY] using
        hattachment
  · have hstrict :
        L.index.1 + 1 < O.chain.cutCount := by
      have hp := L.index_lt_cutCount
      omega
    let attachmentExterior : P.ExteriorVertex :=
      ⟨R.attachment, R.attachment_mem_otherRegion⟩
    have hattachmentSelected :
        attachmentExterior ∈
          (O.chain.blocks L.index).carrier := by
      have hambient :=
        R.attachment_mem_ambientCarrier
      rw [L.choice.mem_ambientCarrier] at hambient
      obtain ⟨d, hdBlock, hdValue⟩ := hambient
      have hdSelected :
          d ∈ (O.chain.blocks L.index).carrier := by
        simpa [L.block_eq] using hdBlock
      have hdAttachment :
          d = attachmentExterior := by
        apply Subtype.ext
        exact hdValue
      simpa [hdAttachment] using hdSelected
    have hcutNeAttachment :
        O.terminalCut ≠ R.attachment := by
      intro hEq
      apply
        O.finalCut_not_mem_selected_of_add_one_lt
          L.index hstrict
      have hsubtype :
          (O.chain.cuts O.terminalCutIndex).1 =
            attachmentExterior := by
        apply Subtype.ext
        exact hEq
      have hsubtype' :
          (O.chain.cuts
            ⟨O.chain.cutCount - 1, by
              have := O.chain.one_le_cutCount
              omega⟩).1 =
              attachmentExterior := by
        simpa [terminalCutIndex] using hsubtype
      rw [hsubtype']
      exact hattachmentSelected
    have hnoRoot :
        ¬G.Adj O.terminalCut x :=
      R.terminalCut_not_adj_root_of_ne_attachment
        hcutNeAttachment
    have htwoCuts :
        2 ≤ O.chain.cutCount := by
      omega
    have hbefore :
        (O.toCandidateChain.lastFeasibleIndex M hregion).1 + 1 <
          O.chain.cutCount := by
      rw [← L.index_eq_lastFeasible]
      exact hstrict
    exact
      O.false_of_lastFeasible_before_preterminal
        M D hregion hall R.side_eq htwoCuts hbefore
          hnoRoot R.terminalCut_not_adj_terminal

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
