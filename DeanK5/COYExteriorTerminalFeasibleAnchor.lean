import DeanK5.COYExteriorBlockCandidates
import DeanK5.COYExteriorClaimThreeTwelveTerminal

/-!
# The terminal last-feasible exterior block

When the last feasible block is the final block of the exterior chain, its
source anchor is the exterior copy of `y`.  The only other special vertex is
the final cut, and the fixed connector from the anchor to `y` is the
length-zero path.  This file packages that concrete anchor and records
Claim 3.12(1) in the terminal analogue of equation (3.4).
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
The source-oriented feasible-block package when the last feasible block is
the terminal block of the exterior chain.
-/
structure ExteriorTerminalFeasibleAnchor
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y}) where
  /-- The selected block index. -/
  index : Fin (O.chain.cutCount + 1)
  /-- The selected index is the maximum feasible index. -/
  index_eq_lastFeasible :
    index =
      O.toCandidateChain.lastFeasibleIndex M hregion
  /-- This is the branch in which the selected index is terminal. -/
  index_eq_cutCount :
    index.1 = O.chain.cutCount
  /-- The source-oriented feasible-block choice. -/
  choice : P.ExteriorFeasibleBlockChoice
  /-- The packaged block is the final chain block. -/
  block_eq_last :
    choice.block =
      O.chain.blocks O.lastIndex
  /-- The anchor is the exterior copy of `y`. -/
  anchor_eq_y :
    choice.anchor.b = P.exteriorY
  /-- The second special vertex is the final cut. -/
  zPrime_eq_finalCut :
    choice.anchor.zPrime =
      O.chain.cuts
        ⟨O.chain.cutCount - 1, by
          have := O.chain.one_le_cutCount
          omega⟩
  /-- The fixed anchor-to-`y` connector is the length-zero path. -/
  pathToTarget_length_eq_zero :
    choice.anchor.pathToTarget.walk.length = 0
  /-- The anchor and final cut are exactly the special block vertices. -/
  special_eq_pair :
    choice.block.carrier ∩
        (cutVertices P.exteriorGraph ∪
          P.exteriorProtected) =
      {P.exteriorY,
        (O.chain.cuts
          ⟨O.chain.cutCount - 1, by
            have := O.chain.one_le_cutCount
            omega⟩).1}
  /-- Claim 3.12(1) for the terminal source-oriented block. -/
  terminalAttachments_eq_empty :
    choice.terminalAttachments = ∅
  /--
  Terminal equation (3.4): no working-core `T`-vertex is adjacent to a
  selected-block vertex other than `y`.
  -/
  equation_three_four :
    ∀ t ∈ P.working.rooted.core.T,
      ∀ d ∈ choice.ambientCarrier,
        d ≠ y → ¬G.Adj t d

namespace ExteriorTerminalFeasibleAnchor

variable
  {M : MinimalCounterexample q G x y z}
  {P : PreferredWorkingCoreData G x y z}
  {O : P.ExteriorOrderedBlockChain}
  {hregion : P.working.rooted.otherRegion ≠ {y}}

/-- The terminal anchor, viewed as an ambient vertex, is `y`. -/
theorem b_eq_y
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion) :
    L.choice.b = y := by
  exact congrArg Subtype.val L.anchor_eq_y

/-- The second special vertex, viewed in the ambient graph, is the final cut. -/
theorem zPrime_eq_finalCut_ambient
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion) :
    L.choice.zPrime =
      (O.chain.cuts
        ⟨O.chain.cutCount - 1, by
          have := O.chain.one_le_cutCount
          omega⟩).1.1 := by
  exact congrArg Subtype.val L.zPrime_eq_finalCut

/-- The ambient anchor-to-`y` connector has length zero. -/
theorem pathToY_length_eq_zero
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion) :
    L.choice.pathToY.walk.length = 0 := by
  change
    (L.choice.anchor.pathToTarget.walk.map
      P.exteriorEmbedding.toHom).length = 0
  rw [SimpleGraph.Walk.length_map]
  exact L.pathToTarget_length_eq_zero

end ExteriorTerminalFeasibleAnchor

namespace ExteriorOrderedBlockChain

variable {P : PreferredWorkingCoreData G x y z}

/--
Construct the source-oriented feasible-block choice in the branch where the
last feasible block is the final block.
-/
noncomputable def terminalFeasibleAnchor
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hterminal :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 =
        O.chain.cutCount) :
    P.ExteriorTerminalFeasibleAnchor M O hregion := by
  classical
  let p :=
    O.toCandidateChain.lastFeasibleIndex M hregion
  have hpTerminal :
      p = O.lastIndex := by
    apply Fin.ext
    simpa [p, ExteriorOrderedBlockChain.lastIndex] using
      hterminal
  let finalCutIndex : Fin O.chain.cutCount :=
    ⟨O.chain.cutCount - 1, by
      have := O.chain.one_le_cutCount
      omega⟩
  let B : GraphBlock P.exteriorGraph :=
    O.chain.blocks O.lastIndex
  have hfeasible :
      IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected B := by
    have hraw :=
      O.toCandidateChain.lastFeasibleIndex_feasible
        M hregion
    change
      IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected
        (O.chain.blocks p) at hraw
    simpa [B, hpTerminal] using hraw
  have hyMem :
      P.exteriorY ∈ B.carrier := by
    simpa [B] using O.y_mem_last_block
  have hfinalCutMem :
      (O.chain.cuts finalCutIndex).1 ∈
        B.carrier := by
    have hmem :=
      O.chain.cut_mem_right finalCutIndex
    have hindex :
        (⟨finalCutIndex.1 + 1, by omega⟩ :
          Fin (O.chain.cutCount + 1)) =
        O.lastIndex := by
      apply Fin.ext
      dsimp [finalCutIndex,
        ExteriorOrderedBlockChain.lastIndex]
      have := O.chain.one_le_cutCount
      omega
    rw [hindex] at hmem
    simpa [B] using hmem
  have hySpecial :
      P.exteriorY ∈
        cutVertices P.exteriorGraph ∪
          P.exteriorProtected :=
    Finset.mem_union_right _ P.exteriorY_mem_exteriorProtected
  have hfinalCutSpecial :
      (O.chain.cuts finalCutIndex).1 ∈
        cutVertices P.exteriorGraph ∪
          P.exteriorProtected :=
    Finset.mem_union_left _ (by
      simpa using (O.chain.cuts finalCutIndex).2)
  have hyNeFinalCut :
      P.exteriorY ≠
        (O.chain.cuts finalCutIndex).1 := by
    intro h
    apply O.y_not_cut
    simpa [← h] using
      (O.chain.cuts finalCutIndex).2
  let special :=
    B.carrier ∩
      (cutVertices P.exteriorGraph ∪
        P.exteriorProtected)
  have hyInSpecial :
      P.exteriorY ∈ special :=
    Finset.mem_inter.mpr ⟨hyMem, hySpecial⟩
  have hfinalCutInSpecial :
      (O.chain.cuts finalCutIndex).1 ∈ special :=
    Finset.mem_inter.mpr
      ⟨hfinalCutMem, hfinalCutSpecial⟩
  have hpairSubset :
      ({P.exteriorY,
          (O.chain.cuts finalCutIndex).1} :
        Finset P.ExteriorVertex) ⊆ special := by
    intro v hv
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hyInSpecial
    · exact hfinalCutInSpecial
  have hpairCard :
      ({P.exteriorY,
          (O.chain.cuts finalCutIndex).1} :
        Finset P.ExteriorVertex).card = 2 :=
    Finset.card_pair hyNeFinalCut
  have hspecialEq :
      ({P.exteriorY,
          (O.chain.cuts finalCutIndex).1} :
        Finset P.ExteriorVertex) = special := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    rw [hpairCard]
    exact hfeasible.1
  let ordinary : P.ExteriorVertex :=
    Classical.choose hfeasible.2
  have hordinary :
      ordinary ∈
        B.carrier \
          (cutVertices P.exteriorGraph ∪
            P.exteriorProtected) :=
    Classical.choose_spec hfeasible.2
  let pathToY :
      SimplePath P.exteriorGraph
        P.exteriorY P.exteriorY := {
    walk := .nil
    isPath := .nil
  }
  have hpathMeet :
      ∀ ⦃v : P.ExteriorVertex⦄,
        v ∈ pathToY.walk.support →
          v ∈ B.carrier →
            v = P.exteriorY := by
    intro v hv _
    simpa [pathToY] using hv
  let anchor :
      FeasibleBlockAnchor P.exteriorGraph
        P.exteriorProtected B P.exteriorY := {
    b := P.exteriorY
    zPrime := (O.chain.cuts finalCutIndex).1
    ordinary := ordinary
    b_mem := hyMem
    zPrime_mem := hfinalCutMem
    b_eq_target_or_cut := Or.inl rfl
    b_special := hySpecial
    zPrime_special := hfinalCutSpecial
    special_subset := by
      intro v hv
      have hvSpecial : v ∈ special := by
        simpa [special] using hv
      rw [← hspecialEq] at hvSpecial
      exact hvSpecial
    ordinary_mem :=
      (Finset.mem_sdiff.mp hordinary).1
    ordinary_not_special :=
      (Finset.mem_sdiff.mp hordinary).2
    pathToTarget := pathToY
    path_meets_carrier_only_at_b := hpathMeet
  }
  let C : P.ExteriorFeasibleBlockChoice := {
    block := B
    feasible := hfeasible
    anchor := anchor
  }
  have hattachments :
      C.terminalAttachments = ∅ :=
    C.terminalAttachments_eq_empty M
  refine {
    index := p
    index_eq_lastFeasible := rfl
    index_eq_cutCount := by
      simpa [p] using hterminal
    choice := C
    block_eq_last := by
      rfl
    anchor_eq_y := by
      rfl
    zPrime_eq_finalCut := by
      rfl
    pathToTarget_length_eq_zero := by
      rfl
    special_eq_pair := ?_
    terminalAttachments_eq_empty := hattachments
    equation_three_four := ?_
  }
  · simpa [C, B, finalCutIndex, special] using
      hspecialEq.symm
  · intro t ht d hd hdNeY hadj
    have hdNeB :
        d ≠ C.b := by
      simpa [C, anchor,
        PreferredWorkingCoreData.exteriorY] using hdNeY
    have hdInterior :
        d ∈ C.compressionInterior :=
      Finset.mem_erase.mpr ⟨hdNeB, hd⟩
    have htAttachment :
        t ∈ C.terminalAttachments := by
      change
        t ∈ P.working.rooted.core.T.filter
          (fun t =>
            ∃ d ∈ C.compressionInterior,
              G.Adj t d)
      exact Finset.mem_filter.mpr
        ⟨ht, ⟨d, hdInterior, hadj⟩⟩
    rw [hattachments] at htAttachment
    simp at htAttachment

end ExteriorOrderedBlockChain

end PreferredWorkingCoreData

end COY

end DeanK5
