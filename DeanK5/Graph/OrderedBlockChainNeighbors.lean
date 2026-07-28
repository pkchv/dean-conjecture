import DeanK5.Graph.OrderedBlockChain

/-!
# Neighbours in an ordered block chain

An edge belongs to a graph block.  Consequently a non-cut vertex has all
of its neighbours in its unique block, while a displayed cut vertex has
all of its neighbours in the two consecutive blocks incident with it.
The final lemmas specialize these facts to two-vertex terminal blocks.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace GraphBlock

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
A vertex that is not a cut vertex belongs to at most one block of a
connected graph.
-/
theorem eq_of_common_noncut_vertex
    (hconnected : G.Connected)
    (B C : GraphBlock G)
    {v : V}
    (hvB : v ∈ B.carrier)
    (hvC : v ∈ C.carrier)
    (hnotCut : ¬IsCutVertex G v) :
    C = B := by
  by_contra hCB
  apply hnotCut
  exact
    B.isCutVertex_of_mem_inter
      hconnected C (fun h => hCB h.symm) hvB hvC

/-- Every neighbour of a non-cut block vertex stays in that block. -/
theorem neighbor_mem_carrier_of_not_cut
    (hconnected : G.Connected)
    (B : GraphBlock G)
    {v w : V}
    (hvB : v ∈ B.carrier)
    (hnotCut : ¬IsCutVertex G v)
    (hvw : G.Adj v w) :
    w ∈ B.carrier := by
  obtain ⟨C, hvC, hwC⟩ :=
    GraphBlock.exists_of_adj hvw
  have hCB :
      C = B :=
    B.eq_of_common_noncut_vertex
      hconnected C hvB hvC hnotCut
  rw [hCB] at hwC
  exact hwC

omit [Fintype V] in
/-- A two-vertex block containing two distinct named vertices is their pair. -/
theorem carrier_eq_pair_of_card_eq_two
    (B : GraphBlock G)
    {u v : V}
    (hcard : B.carrier.card = 2)
    (hu : u ∈ B.carrier)
    (hv : v ∈ B.carrier)
    (huv : u ≠ v) :
    B.carrier = {u, v} := by
  have hpSubset :
      ({u, v} : Finset V) ⊆ B.carrier := by
    intro w hw
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  have hEq :
      ({u, v} : Finset V) = B.carrier :=
    Finset.eq_of_subset_of_card_le
      hpSubset (by simp [hcard, huv])
  exact hEq.symm

end GraphBlock

namespace BlockCutIncidence.OrderedBlockChain

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Finiteness of block--cut nodes used in the chain-neighbor arguments. -/
noncomputable local instance orderedBlockNeighborNodeFintype
    (G : SimpleGraph V) :
    Fintype (BlockCutNode G) :=
  Fintype.ofFinite _

/-- Decidable incidence adjacency used in the chain-neighbor arguments. -/
noncomputable local instance orderedBlockNeighborAdjDecidable
    (G : SimpleGraph V) :
    DecidableRel (blockCutIncidence G).Adj :=
  Classical.decRel _

/--
Every neighbour of a displayed cut vertex belongs to one of its two
incident consecutive blocks.
-/
theorem neighbor_mem_left_or_right
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    (i : Fin chain.cutCount)
    {w : V}
    (hadj : G.Adj (chain.cuts i).1 w) :
    w ∈
        (chain.blocks ⟨i.1, by omega⟩).carrier ∪
          (chain.blocks
            ⟨i.1 + 1, by omega⟩).carrier := by
  obtain ⟨B, hcutB, hwB⟩ :=
    GraphBlock.exists_of_adj hadj
  rcases
      chain.block_eq_left_or_right_of_cut_mem
        hdegree i B hcutB with
    hleft | hright
  · exact Finset.mem_union_left _ (by
      simpa [hleft] using hwB)
  · exact Finset.mem_union_right _ (by
      simpa [hright] using hwB)

/--
If the last block has two vertices, all neighbours of its non-cut endpoint
are the final displayed cut vertex.
-/
theorem lastBlock_neighborSet_subset_lastCut
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    {y : V}
    (hy :
      y ∈
        (chain.blocks
          ⟨chain.cutCount, by omega⟩).carrier)
    (hyNotCut : ¬IsCutVertex G y)
    (hcard :
      (chain.blocks
        ⟨chain.cutCount, by omega⟩).carrier.card = 2) :
    G.neighborSet y ⊆
      ({(chain.cuts
        ⟨chain.cutCount - 1, by
          have := chain.one_le_cutCount
          omega⟩).1} : Set V) := by
  have hcutPositive := chain.one_le_cutCount
  let lastCut : Fin chain.cutCount :=
    ⟨chain.cutCount - 1, by omega⟩
  have hlastValue :
      lastCut.1 + 1 = chain.cutCount := by
    dsimp [lastCut]
    omega
  have hcutLast :
      (chain.cuts lastCut).1 ∈
        (chain.blocks
          ⟨chain.cutCount, by omega⟩).carrier := by
    have hmem := chain.cut_mem_right lastCut
    have hindex :
        (⟨lastCut.1 + 1, by omega⟩ :
          Fin (chain.cutCount + 1)) =
          ⟨chain.cutCount, by omega⟩ := by
      apply Fin.ext
      exact hlastValue
    simpa [hindex] using hmem
  have hyCutNe :
      y ≠ (chain.cuts lastCut).1 := by
    intro h
    apply hyNotCut
    simpa [h] using (chain.cuts lastCut).2
  have hcarrier :
      (chain.blocks
        ⟨chain.cutCount, by omega⟩).carrier =
          {y, (chain.cuts lastCut).1} :=
    (chain.blocks
      ⟨chain.cutCount, by omega⟩
      ).carrier_eq_pair_of_card_eq_two
        hcard hy hcutLast hyCutNe
  intro w hyw
  have hwCarrier :
      w ∈
        (chain.blocks
          ⟨chain.cutCount, by omega⟩).carrier :=
    (chain.blocks
      ⟨chain.cutCount, by omega⟩
      ).neighbor_mem_carrier_of_not_cut
        hconnected hy hyNotCut hyw
  rw [hcarrier] at hwCarrier
  have hwy : w ≠ y := hyw.ne'
  simpa [hwy, lastCut] using hwCarrier

/--
If the last two blocks both have order two, the final cut vertex has no
exterior neighbours other than the endpoint of the chain and the preceding
cut vertex.
-/
theorem penultimateCut_neighborSet_subset
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    (htwoCuts : 2 ≤ chain.cutCount)
    {y : V}
    (hy :
      y ∈
        (chain.blocks
          ⟨chain.cutCount, by omega⟩).carrier)
    (hyNotCut : ¬IsCutVertex G y)
    (hlastCard :
      (chain.blocks
        ⟨chain.cutCount, by omega⟩).carrier.card = 2)
    (hpreviousCard :
      (chain.blocks
        ⟨chain.cutCount - 1, by omega⟩).carrier.card = 2) :
    G.neighborSet
        (chain.cuts
          ⟨chain.cutCount - 1, by omega⟩).1 ⊆
      ({y,
        (chain.cuts
          ⟨chain.cutCount - 2, by omega⟩).1} : Set V) := by
  let lastCut : Fin chain.cutCount :=
    ⟨chain.cutCount - 1, by omega⟩
  let previousCut : Fin chain.cutCount :=
    ⟨chain.cutCount - 2, by omega⟩
  have hlastValue :
      lastCut.1 + 1 = chain.cutCount := by
    dsimp [lastCut]
    omega
  have hpreviousValue :
      previousCut.1 + 1 = chain.cutCount - 1 := by
    dsimp [previousCut]
    omega
  have hlastMemFinal :
      (chain.cuts lastCut).1 ∈
        (chain.blocks
          ⟨chain.cutCount, by omega⟩).carrier := by
    have hmem := chain.cut_mem_right lastCut
    have hindex :
        (⟨lastCut.1 + 1, by omega⟩ :
          Fin (chain.cutCount + 1)) =
          ⟨chain.cutCount, by omega⟩ := by
      apply Fin.ext
      exact hlastValue
    simpa [hindex] using hmem
  have hlastNeY :
      (chain.cuts lastCut).1 ≠ y := by
    intro h
    apply hyNotCut
    simpa [← h] using (chain.cuts lastCut).2
  have hfinalCarrier :
      (chain.blocks
        ⟨chain.cutCount, by omega⟩).carrier =
          {(chain.cuts lastCut).1, y} :=
    (chain.blocks
      ⟨chain.cutCount, by omega⟩
      ).carrier_eq_pair_of_card_eq_two
        hlastCard hlastMemFinal hy hlastNeY
  have hlastMemPrevious :
      (chain.cuts lastCut).1 ∈
        (chain.blocks
          ⟨chain.cutCount - 1, by omega⟩).carrier := by
    have hmem := chain.cut_mem_left lastCut
    simpa [lastCut] using hmem
  have hpreviousMem :
      (chain.cuts previousCut).1 ∈
        (chain.blocks
          ⟨chain.cutCount - 1, by omega⟩).carrier := by
    have hmem := chain.cut_mem_right previousCut
    have hindex :
        (⟨previousCut.1 + 1, by omega⟩ :
          Fin (chain.cutCount + 1)) =
          ⟨chain.cutCount - 1, by omega⟩ := by
      apply Fin.ext
      exact hpreviousValue
    simpa [hindex] using hmem
  have hcutsNe :
      (chain.cuts lastCut).1 ≠
        (chain.cuts previousCut).1 := by
    intro h
    have hindices :
        lastCut = previousCut :=
      chain.cuts_injective (Subtype.ext h)
    have hvalues :=
      congrArg (fun i : Fin chain.cutCount => i.1) hindices
    dsimp [lastCut, previousCut] at hvalues
    omega
  have hpreviousCarrier :
      (chain.blocks
        ⟨chain.cutCount - 1, by omega⟩).carrier =
          {(chain.cuts lastCut).1,
            (chain.cuts previousCut).1} :=
    (chain.blocks
      ⟨chain.cutCount - 1, by omega⟩
      ).carrier_eq_pair_of_card_eq_two
        hpreviousCard hlastMemPrevious hpreviousMem hcutsNe
  intro w hw
  have hwUnion :=
    chain.neighbor_mem_left_or_right
      hdegree lastCut hw
  have hleftIndex :
      (⟨lastCut.1, by omega⟩ :
        Fin (chain.cutCount + 1)) =
        ⟨chain.cutCount - 1, by omega⟩ := by
    apply Fin.ext
    rfl
  have hrightIndex :
      (⟨lastCut.1 + 1, by omega⟩ :
        Fin (chain.cutCount + 1)) =
        ⟨chain.cutCount, by omega⟩ := by
    apply Fin.ext
    exact hlastValue
  rw [hleftIndex, hrightIndex,
    hpreviousCarrier, hfinalCarrier] at hwUnion
  have hwNeLast :
      w ≠ (chain.cuts lastCut).1 :=
    hw.ne'
  simp only [Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hwUnion
  rcases hwUnion with
    (hwLast | hwPrevious) | (hwLast | hwY)
  · exact False.elim (hwNeLast hwLast)
  · exact Or.inr (by
      simpa [previousCut] using hwPrevious)
  · exact False.elim (hwNeLast hwLast)
  · exact Or.inl hwY

end BlockCutIncidence.OrderedBlockChain

end DeanK5
