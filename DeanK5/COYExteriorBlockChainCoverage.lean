import DeanK5.COYExteriorOrderedBlockChain

/-!
# Coverage and terminal branches of the COY exterior block chain

Every vertex of the selected exterior occurs in the ordered list of blocks.
The resulting coverage principle turns the blockwise exclusions obtained
from Claim 3.16 and equation (3.4) into global exclusions of terminal-side
attachments.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}

/--
A vertex of `terminals` is attached to the selected exterior at a vertex
different from `excluded`.
-/
def HasExteriorAttachmentAwayFrom
    (P : PreferredWorkingCoreData G x y z)
    (terminals : Finset V)
    (excluded : V) : Prop :=
  ∃ a ∈ P.working.rooted.otherRegion, a ≠ excluded ∧
    ∃ t ∈ terminals, G.Adj t a

namespace ExteriorOrderedBlockChain

variable {P : PreferredWorkingCoreData G x y z}

/--
Every exterior vertex occurs in one of the indexed blocks of the ordered
block chain.
-/
theorem exists_block_index_of_vertex
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (v : P.ExteriorVertex) :
    ∃ i : Fin (O.chain.cutCount + 1),
      v ∈ (O.chain.blocks i).carrier := by
  have horder :
      2 ≤ Fintype.card P.ExteriorVertex := by
    have :=
      P.one_lt_exteriorVertex_card hregion
    omega
  obtain ⟨B, hvB⟩ :=
    GraphBlock.exists_of_vertex
      P.exteriorGraph_connected horder v
  obtain ⟨i, hi⟩ :=
    O.chain.blocks_exhaustive B
  exact ⟨i, by simpa [hi] using hvB⟩

/--
Terminal branch of the block-chain argument.

If the selected index is the final block, Claim 3.16 excludes attachments
on every earlier block and equation (3.4) excludes them on the selected
block away from `y`.  Block coverage then excludes every exterior
attachment away from `y`.
-/
theorem not_hasExteriorAttachmentAwayFrom_of_selected_last
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (terminals : Finset V)
    (p : Fin (O.chain.cutCount + 1))
    (hpLast : p.1 = O.chain.cutCount)
    (hbefore :
      ∀ (i : Fin (O.chain.cutCount + 1)),
        i.1 < p.1 →
          ∀ d ∈ (O.chain.blocks i).carrier,
            ∀ t ∈ terminals, ¬G.Adj t d.1)
    (hselected :
      ∀ d ∈ (O.chain.blocks p).carrier,
        d.1 ≠ y →
          ∀ t ∈ terminals, ¬G.Adj t d.1) :
    ¬P.HasExteriorAttachmentAwayFrom terminals y := by
  rintro ⟨a, haRegion, hay, t, ht, hta⟩
  let d : P.ExteriorVertex :=
    ⟨a, haRegion⟩
  obtain ⟨i, hdi⟩ :=
    O.exists_block_index_of_vertex hregion d
  by_cases hip : i.1 < p.1
  · exact hbefore i hip d hdi t ht hta
  · have hiEq : i = p := by
      apply Fin.ext
      have hiBound : i.1 ≤ O.chain.cutCount := by
        omega
      omega
    have hdp :
        d ∈ (O.chain.blocks p).carrier := by
      simpa [hiEq] using hdi
    exact
      hselected d hdp (by simpa [d] using hay)
        t ht hta

/--
Penultimate branch of the block-chain argument.

Here the selected block is immediately before the final block.  Equation
(3.4) excludes attachments away from the terminal cut, a separate
hypothesis excludes that cut itself, and the two-vertex description of the
last block leaves only `y`.
-/
theorem not_hasExteriorAttachmentAwayFrom_of_selected_penultimate
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (terminals : Finset V)
    (p : Fin (O.chain.cutCount + 1))
    (hpPenultimate :
      p.1 + 1 = O.chain.cutCount)
    (terminalCut : P.ExteriorVertex)
    (hfinalCarrier :
      (O.chain.blocks O.lastIndex).carrier =
        {terminalCut, P.exteriorY})
    (hterminalCut :
      ∀ t ∈ terminals,
        ¬G.Adj t terminalCut.1)
    (hbefore :
      ∀ (i : Fin (O.chain.cutCount + 1)),
        i.1 < p.1 →
          ∀ d ∈ (O.chain.blocks i).carrier,
            ∀ t ∈ terminals, ¬G.Adj t d.1)
    (hselected :
      ∀ d ∈ (O.chain.blocks p).carrier,
        d ≠ terminalCut →
          ∀ t ∈ terminals, ¬G.Adj t d.1) :
    ¬P.HasExteriorAttachmentAwayFrom terminals y := by
  rintro ⟨a, haRegion, hay, t, ht, hta⟩
  let d : P.ExteriorVertex :=
    ⟨a, haRegion⟩
  obtain ⟨i, hdi⟩ :=
    O.exists_block_index_of_vertex hregion d
  by_cases hiBefore : i.1 < p.1
  · exact hbefore i hiBefore d hdi t ht hta
  by_cases hiSelected : i.1 = p.1
  · have hiEq : i = p :=
      Fin.ext hiSelected
    have hdp :
        d ∈ (O.chain.blocks p).carrier := by
      simpa [hiEq] using hdi
    by_cases hdCut : d = terminalCut
    · have haCut :
          a = terminalCut.1 := by
        simpa [d] using congrArg Subtype.val hdCut
      apply hterminalCut t ht
      rw [← haCut]
      exact hta
    · exact hselected d hdp hdCut t ht hta
  · have hiLastValue :
        i.1 = O.chain.cutCount := by
      have hiBound : i.1 ≤ O.chain.cutCount := by
        omega
      omega
    have hiLast :
        i = O.lastIndex := by
      apply Fin.ext
      exact hiLastValue
    have hdFinal :
        d ∈
          (O.chain.blocks O.lastIndex).carrier := by
      simpa [hiLast] using hdi
    rw [hfinalCarrier] at hdFinal
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hdFinal
    rcases hdFinal with hdCut | hdY
    · have haCut :
          a = terminalCut.1 := by
        simpa [d] using congrArg Subtype.val hdCut
      apply hterminalCut t ht
      rw [← haCut]
      exact hta
    · apply hay
      exact congrArg Subtype.val hdY

/--
If the selected block lies at least two positions before the end, the final
cut vertex cannot occur in the selected block.
-/
theorem finalCut_not_mem_selected_of_add_one_lt
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hbefore : p.1 + 1 < O.chain.cutCount) :
    (O.chain.cuts
        ⟨O.chain.cutCount - 1, by omega⟩).1 ∉
      (O.chain.blocks p).carrier := by
  let finalCutIndex : Fin O.chain.cutCount :=
    ⟨O.chain.cutCount - 1, by omega⟩
  let finalCut : P.ExteriorVertex :=
    (O.chain.cuts finalCutIndex).1
  have hfinalMem :
      finalCut ∈
        (O.chain.blocks O.lastIndex).carrier := by
    have hmem :=
      O.chain.cut_mem_right finalCutIndex
    have hindex :
        (⟨finalCutIndex.1 + 1, by omega⟩ :
          Fin (O.chain.cutCount + 1)) =
        O.lastIndex := by
      apply Fin.ext
      dsimp [finalCutIndex,
        ExteriorOrderedBlockChain.lastIndex]
      omega
    rw [hindex] at hmem
    exact hmem
  have hinter :
      (O.chain.blocks p).carrier ∩
          (O.chain.blocks O.lastIndex).carrier =
        ∅ := by
    apply O.nonconsecutive_inter_eq_empty
    left
    simpa [ExteriorOrderedBlockChain.lastIndex] using
      hbefore
  intro hselected
  have hboth :
      finalCut ∈
        (O.chain.blocks p).carrier ∩
          (O.chain.blocks O.lastIndex).carrier :=
    Finset.mem_inter.mpr ⟨hselected, hfinalMem⟩
  rw [hinter] at hboth
  simp at hboth

end ExteriorOrderedBlockChain

end PreferredWorkingCoreData

end COY

end DeanK5
