import DeanK5.COYExteriorBlockCandidates
import DeanK5.COYExteriorClaimThreeTwelveTerminal
import DeanK5.Graph.OrderedBlockChainPaths

/-!
# Orienting the last feasible exterior block

Let `B_p` be the last feasible block in the exterior chain oriented from
`z` to `y`.  When `B_p` is not the final block, its source anchor is the
cut vertex `b_p` on its right.  A path through the suffix of the chain
joins `b_p` to `y` and meets `B_p` only at `b_p`.  If `p > 0`, the only
other special vertex of `B_p` is the cut vertex `b_{p-1}` on its left.

This file packages that source-oriented choice as an
`ExteriorFeasibleBlockChoice` and records Claim 3.12(1) in the concrete
form used as equation (3.4).
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
The last feasible exterior block, oriented toward `y`.

The data are available in the branch where the last feasible block is not
the final block of the ordered chain.  The anchor is its right-hand cut
vertex, and for a positive block index the second special vertex is its
left-hand cut vertex.
-/
structure ExteriorLastFeasibleAnchor
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y}) where
  /-- The selected block index. -/
  index : Fin (O.chain.cutCount + 1)
  /-- The index is the maximum feasible index. -/
  index_eq_lastFeasible :
    index =
      O.toCandidateChain.lastFeasibleIndex M hregion
  /-- This is the branch in which the selected block is not final. -/
  index_lt_cutCount : index.1 < O.chain.cutCount
  /-- The source-oriented feasible-block package. -/
  choice : P.ExteriorFeasibleBlockChoice
  /-- The packaged block is the selected chain block. -/
  block_eq :
    choice.block = O.chain.blocks index
  /-- The anchor is the cut on the right of the selected block. -/
  anchor_eq_rightCut :
    choice.anchor.b =
      O.chain.cuts ⟨index.1, index_lt_cutCount⟩
  /-- The exterior copy of `y` does not lie in the selected block. -/
  y_not_mem_block :
    P.exteriorY ∉ choice.block.carrier
  /-- At a positive index, the second special vertex is the left cut. -/
  zPrime_eq_leftCut :
    ∀ hpositive : 0 < index.1,
      choice.anchor.zPrime =
        O.chain.cuts
          ⟨index.1 - 1, by omega⟩
  /-- Claim 3.12(1) for the source-oriented block. -/
  terminalAttachments_eq_empty :
    choice.terminalAttachments = ∅
  /--
  Equation (3.4): no vertex of the working core's `T`-side is adjacent
  to a nonanchor vertex of the selected block.
  -/
  equation_three_four :
    ∀ t ∈ P.working.rooted.core.T,
      ∀ d ∈ choice.ambientCarrier,
        d ≠ choice.b → ¬G.Adj t d

namespace ExteriorLastFeasibleAnchor

variable
  {M : MinimalCounterexample q G x y z}
  {P : PreferredWorkingCoreData G x y z}
  {O : P.ExteriorOrderedBlockChain}
  {hregion : P.working.rooted.otherRegion ≠ {y}}

/-- The right-hand cut, viewed as an ambient vertex. -/
theorem b_eq_rightCut
    (L : P.ExteriorLastFeasibleAnchor M O hregion) :
    L.choice.b =
      (O.chain.cuts
        ⟨L.index.1, L.index_lt_cutCount⟩).1 := by
  exact congrArg Subtype.val L.anchor_eq_rightCut

/-- The positive-index left-cut identity, viewed in the ambient graph. -/
theorem zPrime_eq_leftCut_ambient
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1) :
    L.choice.zPrime =
      (O.chain.cuts
        ⟨L.index.1 - 1, by omega⟩).1 := by
  exact
    congrArg Subtype.val
      (L.zPrime_eq_leftCut hpositive)

end ExteriorLastFeasibleAnchor

namespace ExteriorOrderedBlockChain

variable {P : PreferredWorkingCoreData G x y z}

/--
Construct the source-oriented anchor at the last feasible block, assuming
that block occurs before the end of the exterior chain.
-/
noncomputable def lastFeasibleAnchor
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 <
        O.chain.cutCount) :
    P.ExteriorLastFeasibleAnchor M O hregion := by
  classical
  let pRaw :=
    O.toCandidateChain.lastFeasibleIndex M hregion
  let p : Fin (O.chain.cutCount + 1) :=
    ⟨pRaw.1, by
      simpa [ExteriorOrderedBlockChain.toCandidateChain] using
        pRaw.2⟩
  have hpRaw : p = pRaw := by
    apply Fin.ext
    rfl
  have hpBefore : p.1 < O.chain.cutCount := by
    simpa only [p, pRaw] using hbefore
  let rightCut : Fin O.chain.cutCount :=
    ⟨p.1, hpBefore⟩
  let B : GraphBlock P.exteriorGraph :=
    O.chain.blocks p
  have hfeasible :
      IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected B := by
    have hraw :=
      O.toCandidateChain.lastFeasibleIndex_feasible M hregion
    change
      IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected
        (O.chain.blocks pRaw) at hraw
    simpa [B, hpRaw] using hraw
  have hyLast :
      P.exteriorY ∈
        (O.chain.blocks
          ⟨O.chain.cutCount, by omega⟩).carrier := by
    simpa [ExteriorOrderedBlockChain.lastIndex] using
      O.y_mem_last_block
  have hyNotB :
      P.exteriorY ∉ B.carrier := by
    intro hyB
    have hpLast :
        p =
          (⟨O.chain.cutCount, by omega⟩ :
            Fin (O.chain.cutCount + 1)) :=
      O.chain.block_index_eq_of_noncut_mem
        P.exteriorGraph_connected O.y_not_cut
        p ⟨O.chain.cutCount, by omega⟩
        (by simpa [B] using hyB) hyLast
    have hvalues :=
      congrArg
        (fun i : Fin (O.chain.cutCount + 1) => i.1)
        hpLast
    change p.1 = O.chain.cutCount at hvalues
    omega
  let pathExistence :=
    O.chain.exists_cut_to_lastBlock_path
      rightCut hyLast
  let pathToY :=
    Classical.choose pathExistence
  have hpathSupport :=
    Classical.choose_spec pathExistence
  have hpathMeet :
      ∀ ⦃v : P.ExteriorVertex⦄,
        v ∈ pathToY.walk.support →
          v ∈ B.carrier →
            v = O.chain.cuts rightCut := by
    intro v hvPath hvB
    let suffixLength :=
      O.chain.cutCount - (p.1 + 1)
    have hbound :
        p.1 + 1 + suffixLength ≤
          O.chain.cutCount := by
      dsimp [suffixLength]
      omega
    have hvPrevious :
        v ∈
          (O.chain.blocks
            ⟨(p.1 + 1) - 1, by omega⟩).carrier := by
      have hindex :
          (⟨(p.1 + 1) - 1, by omega⟩ :
            Fin (O.chain.cutCount + 1)) = p := by
        apply Fin.ext
        change (p.1 + 1) - 1 = p.1
        omega
      rw [hindex]
      simpa [B] using hvB
    have hmeet :=
      O.chain.path_meets_previousBlock_only_at_cut
        P.exteriorGraph_connected
        O.incidence_degree_le_two
        (start := p.1 + 1)
        (len := suffixLength)
        (by omega) hbound pathToY
        (by
          intro w hw
          simpa [suffixLength, rightCut] using
            hpathSupport w hw)
        hvPath hvPrevious
    have hcutIndex :
        (⟨(p.1 + 1) - 1, by omega⟩ :
          Fin O.chain.cutCount) = rightCut := by
      apply Fin.ext
      change (p.1 + 1) - 1 = p.1
      omega
    simpa [hcutIndex] using hmeet
  let zExterior :=
    P.exteriorZ O.endpoints.z_mem_otherRegion
  let zPrime : P.ExteriorVertex :=
    if hpositive : 0 < p.1 then
      O.chain.cuts ⟨p.1 - 1, by omega⟩
    else
      zExterior
  have hrightMem :
      (O.chain.cuts rightCut).1 ∈ B.carrier := by
    simpa [B, rightCut] using
      O.chain.cut_mem_left rightCut
  have hzPrimeMem :
      zPrime ∈ B.carrier := by
    by_cases hpositive : 0 < p.1
    · have hleft :=
        O.chain.cut_mem_right
          ⟨p.1 - 1, by omega⟩
      have hindex :
          (⟨(p.1 - 1) + 1, by omega⟩ :
            Fin (O.chain.cutCount + 1)) = p := by
        apply Fin.ext
        change (p.1 - 1) + 1 = p.1
        omega
      rw [hindex] at hleft
      simpa [zPrime, hpositive, B] using hleft
    · have hpZero : p = 0 := by
        apply Fin.ext
        change p.1 = 0
        omega
      have hzFirst := O.z_mem_first_block
      simpa [zPrime, hpositive, zExterior, B,
        ExteriorOrderedBlockChain.firstIndex, hpZero] using
        hzFirst
  have hrightSpecial :
      (O.chain.cuts rightCut).1 ∈
        cutVertices P.exteriorGraph ∪
          P.exteriorProtected := by
    apply Finset.mem_union_left
    simpa using (O.chain.cuts rightCut).2
  have hzPrimeSpecial :
      zPrime ∈
        cutVertices P.exteriorGraph ∪
          P.exteriorProtected := by
    by_cases hpositive : 0 < p.1
    · apply Finset.mem_union_left
      simpa [zPrime, hpositive] using
        (O.chain.cuts
          ⟨p.1 - 1, by omega⟩).2
    · apply Finset.mem_union_right
      simpa [zPrime, hpositive, zExterior] using
        P.exteriorZ_mem_exteriorProtected
          O.endpoints.z_mem_otherRegion
  have hrightNeZPrime :
      (O.chain.cuts rightCut).1 ≠ zPrime := by
    by_cases hpositive : 0 < p.1
    · intro heq
      have hindices :
          rightCut =
            (⟨p.1 - 1, by omega⟩ :
              Fin O.chain.cutCount) :=
        O.chain.cuts_injective
          (Subtype.ext
            (by simpa [zPrime, hpositive] using heq))
      have hvalues :=
        congrArg
          (fun i : Fin O.chain.cutCount => i.1)
          hindices
      dsimp [rightCut] at hvalues
      omega
    · intro heq
      apply O.z_not_cut
      have hsubtype :
          O.chain.cuts rightCut = zExterior := by
        simpa [zPrime, hpositive] using heq
      simpa [zExterior, ← hsubtype] using
        (O.chain.cuts rightCut).2
  let special :=
    B.carrier ∩
      (cutVertices P.exteriorGraph ∪
        P.exteriorProtected)
  have hrightInSpecial :
      (O.chain.cuts rightCut).1 ∈ special :=
    Finset.mem_inter.mpr
      ⟨hrightMem, hrightSpecial⟩
  have hzPrimeInSpecial :
      zPrime ∈ special :=
    Finset.mem_inter.mpr
      ⟨hzPrimeMem, hzPrimeSpecial⟩
  have hpairSubset :
      ({(O.chain.cuts rightCut).1, zPrime} :
          Finset P.ExteriorVertex) ⊆ special := by
    intro v hv
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hrightInSpecial
    · exact hzPrimeInSpecial
  have hpairCard :
      ({(O.chain.cuts rightCut).1, zPrime} :
          Finset P.ExteriorVertex).card = 2 :=
    Finset.card_pair hrightNeZPrime
  have hspecialEq :
      ({(O.chain.cuts rightCut).1, zPrime} :
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
  let anchor :
      FeasibleBlockAnchor P.exteriorGraph
        P.exteriorProtected B P.exteriorY := {
    b := O.chain.cuts rightCut
    zPrime := zPrime
    ordinary := ordinary
    b_mem := hrightMem
    zPrime_mem := hzPrimeMem
    b_eq_target_or_cut := Or.inr
      (O.chain.cuts rightCut).2
    b_special := hrightSpecial
    zPrime_special := hzPrimeSpecial
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
  have hterminal :
      C.terminalAttachments = ∅ :=
    C.terminalAttachments_eq_empty M
  refine {
    index := p
    index_eq_lastFeasible := by
      rfl
    index_lt_cutCount := hpBefore
    choice := C
    block_eq := by
      rfl
    anchor_eq_rightCut := by
      rfl
    y_not_mem_block := by
      simpa [C] using hyNotB
    zPrime_eq_leftCut := ?_
    terminalAttachments_eq_empty := hterminal
    equation_three_four := ?_
  }
  · intro hpositive
    simp [C, anchor, zPrime, hpositive]
  · intro t ht d hd hdNe hadj
    have hdInterior :
        d ∈ C.compressionInterior := by
      exact Finset.mem_erase.mpr
        ⟨hdNe, hd⟩
    have htAttachment :
        t ∈ C.terminalAttachments := by
      change
        t ∈ P.working.rooted.core.T.filter
          (fun t =>
            ∃ d ∈ C.compressionInterior,
              G.Adj t d)
      exact Finset.mem_filter.mpr
        ⟨ht, ⟨d, hdInterior, hadj⟩⟩
    rw [hterminal] at htAttachment
    simp at htAttachment

end ExteriorOrderedBlockChain

end PreferredWorkingCoreData

end COY

end DeanK5
