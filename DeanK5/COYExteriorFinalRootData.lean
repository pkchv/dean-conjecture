import DeanK5.COYExteriorChosenRootAttachment
import DeanK5.COYExteriorChainDegreeBridge
import DeanK5.COYExteriorLastFeasibleAnchor

/-!
# Final root-neighborhood data

For a nonterminal last feasible block, equation (3.2) supplies an exterior
neighbor of the chosen root.  The final two-vertex block then supplies the
only exterior neighbor of the other root.  The degree comparison forces
equality throughout, determining both root neighborhoods exactly and
excluding every edge from the final cut to the terminal side of the core.
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
The exact root-neighborhood information obtained from a nonterminal last
feasible exterior block.
-/
structure ExteriorFinalRootData
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (L : P.ExteriorLastFeasibleAnchor M O hregion) where
  /-- The unique vertex on the rank-one `S`-side. -/
  side : V
  /-- The selected `S`-side is the singleton containing `side`. -/
  side_eq : D.core.S = {side}
  /-- Equation (3.2) for the selected feasible block. -/
  coreAttachments_eq_pair :
    L.choice.coreAttachments = {x, side}
  /-- The chosen exterior neighbor of the core root. -/
  attachment : V
  /-- The attachment lies in the ambient selected-block carrier. -/
  attachment_mem_ambientCarrier :
    attachment ∈ L.choice.ambientCarrier
  /-- The attachment is different from the retained block anchor. -/
  attachment_ne_anchor :
    attachment ≠ L.choice.b
  /-- The attachment lies in the selected exterior component. -/
  attachment_mem_otherRegion :
    attachment ∈ P.working.rooted.otherRegion
  /-- The core root is adjacent to the chosen attachment. -/
  root_adj_attachment :
    G.Adj x attachment
  /-- The chosen attachment is not on the core's terminal side. -/
  attachment_not_mem_terminal :
    attachment ∉ D.core.T
  /-- Equality in the lower degree bound at the chosen root. -/
  chosenRoot_degree_eq :
    finiteDegree G x = D.core.T.card + 1
  /-- Equality in the corresponding degree bound at the other root. -/
  otherRoot_degree_eq :
    finiteDegree G y = D.core.T.card + 1
  /-- The chosen root sees exactly `T` and the selected attachment. -/
  chosenRoot_neighborSet_eq :
    G.neighborSet x =
      (↑(insert attachment D.core.T) : Set V)
  /-- The other root sees exactly `T` and the final exterior cut. -/
  otherRoot_neighborSet_eq :
    G.neighborSet y =
      (↑(insert O.terminalCut D.core.T) : Set V)
  /-- The final cut lies outside the terminal side of the core. -/
  terminalCut_not_mem_terminal :
    O.terminalCut ∉ D.core.T
  /-- No terminal-side vertex is adjacent to the final exterior cut. -/
  terminalCut_not_adj_terminal :
    ∀ t ∈ D.core.T, ¬G.Adj O.terminalCut t

namespace ExteriorFinalRootData

variable
  {M : MinimalCounterexample q G x y z}
  {P : PreferredWorkingCoreData G x y z}
  {O : P.ExteriorOrderedBlockChain}
  {D : P.TypeThreeStage}
  {hregion : P.working.rooted.otherRegion ≠ {y}}
  {L : P.ExteriorLastFeasibleAnchor M O hregion}

/--
If the final cut is not the selected attachment, the exact chosen-root
neighborhood excludes an edge from the final cut to the core root.
-/
theorem terminalCut_not_adj_root_of_ne_attachment
    (R : P.ExteriorFinalRootData M O D hregion L)
    (hne : O.terminalCut ≠ R.attachment) :
    ¬G.Adj O.terminalCut x := by
  intro hcutRoot
  have hmem :
      O.terminalCut ∈ G.neighborSet x :=
    hcutRoot.symm
  rw [R.chosenRoot_neighborSet_eq] at hmem
  change
    O.terminalCut ∈ insert R.attachment D.core.T at hmem
  simp only [Finset.mem_insert] at hmem
  rcases hmem with heq | hterminal
  · exact hne heq
  · exact R.terminalCut_not_mem_terminal hterminal

end ExteriorFinalRootData

namespace ExteriorLastFeasibleAnchor

variable
  {M : MinimalCounterexample q G x y z}
  {P : PreferredWorkingCoreData G x y z}
  {O : P.ExteriorOrderedBlockChain}
  {hregion : P.working.rooted.otherRegion ≠ {y}}

/--
Construct the complete final root-neighborhood package from the nonterminal
last feasible block.
-/
noncomputable def finalRootData
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    P.ExteriorFinalRootData M O D hregion L := by
  let A :=
    L.choice.chosenRootAttachmentData M D
  have hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 <
        O.chain.cutCount := by
    rw [← L.index_eq_lastFeasible]
    exact L.index_lt_cutCount
  obtain ⟨hxDegree, hyDegree, hyNeighbor⟩ :=
    O.root_degree_sandwich_of_lastFeasible_before
      M D hregion hall A.side_eq
      A.root_adj_attachment
      A.attachment_not_mem_terminal
      hbefore
  have hxNeighbor :
      G.neighborSet x =
        (↑(insert A.attachment D.core.T) : Set V) :=
    D.chosenRoot_neighborSet_eq_insert_terminal
      A.root_adj_attachment
      A.attachment_not_mem_terminal
      hxDegree
  have hterminalCutRegion :
      O.terminalCut ∈
        P.working.rooted.otherRegion :=
    (O.chain.cuts O.terminalCutIndex).1.2
  have hterminalCutNotCore :
      O.terminalCut ∉
        P.working.rooted.core.carrier :=
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      hterminalCutRegion
  have hterminalCutNotTerminal :
      O.terminalCut ∉ D.core.T := by
    intro hterminal
    apply hterminalCutNotCore
    rw [D.core_eq]
    exact
      (Core.typeThree D.core).T_subset_carrier
        (by simpa [Core.T] using hterminal)
  have hterminalExclusion :
      ∀ t ∈ D.core.T,
        ¬G.Adj O.terminalCut t :=
    D.terminal_not_adj_last_of_otherRoot_neighborSet
      M hterminalCutNotCore hyNeighbor
  exact {
    side := A.side
    side_eq := A.side_eq
    coreAttachments_eq_pair :=
      A.coreAttachments_eq_pair
    attachment := A.attachment
    attachment_mem_ambientCarrier :=
      A.attachment_mem_ambientCarrier
    attachment_ne_anchor :=
      A.attachment_ne_anchor
    attachment_mem_otherRegion :=
      A.attachment_mem_otherRegion
    root_adj_attachment :=
      A.root_adj_attachment
    attachment_not_mem_terminal :=
      A.attachment_not_mem_terminal
    chosenRoot_degree_eq := hxDegree
    otherRoot_degree_eq := hyDegree
    chosenRoot_neighborSet_eq := hxNeighbor
    otherRoot_neighborSet_eq := hyNeighbor
    terminalCut_not_mem_terminal :=
      hterminalCutNotTerminal
    terminalCut_not_adj_terminal :=
      hterminalExclusion
  }

end ExteriorLastFeasibleAnchor

end PreferredWorkingCoreData

end COY

end DeanK5
