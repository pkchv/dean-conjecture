import DeanK5.COYExteriorBlockEndpoints
import DeanK5.Graph.OrderedBlockChain

/-!
# The ordered block chain of the selected COY exterior

The two marked leaf blocks of the exterior block--cut tree determine an
orientation of its Hamiltonian incidence path: the block containing `z` is
first and the block containing `y` is last.  This file packages that oriented
order and exposes the incidence, intersection, and disjointness properties
used in the remaining COY argument.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace BlockCutIncidence

namespace OrderedBlockChain

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

omit [Fintype V] in
/-- The chain extracted from a Hamiltonian path begins at its first block. -/
theorem ofHamiltonianPath_first_block
    {B C : GraphBlock G}
    (hBC : B ≠ C)
    (p :
      (blockCutIncidence G).Walk
        (.inl B) (.inl C))
    (hp : p.IsPath)
    (hall :
      ∀ n : BlockCutNode G, n ∈ p.support) :
    let chain :=
      ofHamiltonianPath hBC p hp hall
    chain.blocks
        ⟨0, Nat.zero_lt_succ chain.cutCount⟩ =
      B := by
  simp [ofHamiltonianPath]

omit [Fintype V] in
/-- The chain extracted from a Hamiltonian path ends at its last block. -/
theorem ofHamiltonianPath_last_block
    {B C : GraphBlock G}
    (hBC : B ≠ C)
    (p :
      (blockCutIncidence G).Walk
        (.inl B) (.inl C))
    (hp : p.IsPath)
    (hall :
      ∀ n : BlockCutNode G, n ∈ p.support) :
    let chain :=
      ofHamiltonianPath hBC p hp hall
    chain.blocks
        ⟨chain.cutCount,
          Nat.lt_succ_self chain.cutCount⟩ =
      C := by
  let t : ℕ :=
    Classical.choose
      (walk_length_even_between_blocks p)
  have ht :
      p.length = t + t :=
    Classical.choose_spec
      (walk_length_even_between_blocks p)
  have hbound :
      2 * t ≤ p.length := by
    omega
  have heven :
      Even (2 * t) :=
    ⟨t, by omega⟩
  let D : GraphBlock G :=
    Classical.choose
      (exists_block_getVert_of_even
        p hbound heven)
  have hD :
      p.getVert (2 * t) = .inl D :=
    Classical.choose_spec
      (exists_block_getVert_of_even
        p hbound heven)
  have hDC : D = C := by
    apply Sum.inl.inj
    rw [← hD]
    rw [show 2 * t = p.length by omega]
    simp
  simp only [ofHamiltonianPath]
  exact hDC

/-- Finiteness of block--cut nodes used to orient a chain between two leaves. -/
noncomputable local instance exteriorOrderedNodeFintype
    (G : SimpleGraph V) :
    Fintype (BlockCutNode G) :=
  Fintype.ofFinite _

/-- Decidable incidence adjacency used to orient a chain between two leaves. -/
noncomputable local instance exteriorOrderedAdjDecidable
    (G : SimpleGraph V) :
    DecidableRel (blockCutIncidence G).Adj :=
  Classical.decRel _

/-- The chain selected from two ordered leaf blocks begins at the first one. -/
theorem ofTwoLeafBlocks_first_block
    (hTree : (blockCutIncidence G).IsTree)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    (B C : GraphBlock G)
    (hBC : B ≠ C)
    (hB :
      (blockCutIncidence G).degree
        (.inl B : BlockCutNode G) = 1)
    (hC :
      (blockCutIncidence G).degree
        (.inl C : BlockCutNode G) = 1) :
    let chain :=
      ofTwoLeafBlocks
        hTree hdegree B C hBC hB hC
    chain.blocks
        ⟨0, Nat.zero_lt_succ chain.cutCount⟩ =
      B := by
  simp [ofTwoLeafBlocks, ofHamiltonianPath]

/-- The chain selected from two ordered leaf blocks ends at the second one. -/
theorem ofTwoLeafBlocks_last_block
    (hTree : (blockCutIncidence G).IsTree)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    (B C : GraphBlock G)
    (hBC : B ≠ C)
    (hB :
      (blockCutIncidence G).degree
        (.inl B : BlockCutNode G) = 1)
    (hC :
      (blockCutIncidence G).degree
        (.inl C : BlockCutNode G) = 1) :
    let chain :=
      ofTwoLeafBlocks
        hTree hdegree B C hBC hB hC
    chain.blocks
        ⟨chain.cutCount,
          Nat.lt_succ_self chain.cutCount⟩ =
      C := by
  classical
  let hnodes :
      (Sum.inl B : BlockCutNode G) ≠ .inl C := by
    simpa using hBC
  let hex :=
    existsUnique_leafPath_containing_every_node
      hTree hdegree hnodes hB hC
  let p :
      (blockCutIncidence G).Walk
        (.inl B) (.inl C) :=
    Classical.choose hex
  have hp :
      p.IsPath :=
    (Classical.choose_spec hex).1.1
  have hall :
      ∀ n : BlockCutNode G, n ∈ p.support :=
    (Classical.choose_spec hex).1.2
  simpa only [ofTwoLeafBlocks] using
    ofHamiltonianPath_last_block
      hBC p hp hall

end OrderedBlockChain

end BlockCutIncidence

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- Finiteness of the selected exterior's block--cut nodes. -/
noncomputable local instance exteriorOrderedNodeFintype
    (P : PreferredWorkingCoreData G x y z) :
    Fintype (BlockCutNode P.exteriorGraph) :=
  Fintype.ofFinite _

/-- Decidable adjacency in the selected exterior's block--cut incidence graph. -/
noncomputable local instance exteriorOrderedAdjDecidable
    (P : PreferredWorkingCoreData G x y z) :
    DecidableRel
      (blockCutIncidence P.exteriorGraph).Adj :=
  Classical.decRel _

/--
The selected exterior block chain, oriented from the leaf block containing
`z` to the leaf block containing `y`.
-/
structure ExteriorOrderedBlockChain
    (P : PreferredWorkingCoreData G x y z) where
  /-- The two marked endpoint blocks. -/
  endpoints : P.ExteriorBlockEndpoints
  /-- The ordered list of every exterior block and cut vertex. -/
  chain :
    BlockCutIncidence.OrderedBlockChain
      P.exteriorGraph
  /-- The exterior incidence graph is a tree. -/
  incidence_isTree :
    (blockCutIncidence P.exteriorGraph).IsTree
  /-- Every exterior incidence node has degree at most two. -/
  incidence_degree_le_two :
    ∀ n : BlockCutNode P.exteriorGraph,
      (blockCutIncidence P.exteriorGraph).degree n ≤ 2
  /-- The first chain block is the block containing `z`. -/
  first_block_eq_z :
    chain.blocks
        ⟨0, Nat.zero_lt_succ chain.cutCount⟩ =
      endpoints.zBlock
  /-- The last chain block is the block containing `y`. -/
  last_block_eq_y :
    chain.blocks
        ⟨chain.cutCount,
          Nat.lt_succ_self chain.cutCount⟩ =
      endpoints.yBlock

namespace ExteriorOrderedBlockChain

variable {P : PreferredWorkingCoreData G x y z}

/-- The index of the first block in an exterior ordered chain. -/
def firstIndex
    (O : P.ExteriorOrderedBlockChain) :
    Fin (O.chain.cutCount + 1) :=
  ⟨0, Nat.zero_lt_succ O.chain.cutCount⟩

/-- The index of the last block in an exterior ordered chain. -/
def lastIndex
    (O : P.ExteriorOrderedBlockChain) :
    Fin (O.chain.cutCount + 1) :=
  ⟨O.chain.cutCount,
    Nat.lt_succ_self O.chain.cutCount⟩

/-- The first block of the chain contains the exterior copy of `z`. -/
theorem z_mem_first_block
    (O : P.ExteriorOrderedBlockChain) :
    P.exteriorZ O.endpoints.z_mem_otherRegion ∈
      (O.chain.blocks O.firstIndex).carrier := by
  change
    P.exteriorZ O.endpoints.z_mem_otherRegion ∈
      (O.chain.blocks
        ⟨0, Nat.zero_lt_succ O.chain.cutCount⟩).carrier
  rw [O.first_block_eq_z]
  exact O.endpoints.z_mem_block

/-- The last block of the chain contains the exterior copy of `y`. -/
theorem y_mem_last_block
    (O : P.ExteriorOrderedBlockChain) :
    P.exteriorY ∈
      (O.chain.blocks O.lastIndex).carrier := by
  change
    P.exteriorY ∈
      (O.chain.blocks
        ⟨O.chain.cutCount,
          Nat.lt_succ_self O.chain.cutCount⟩).carrier
  rw [O.last_block_eq_y]
  exact O.endpoints.y_mem_block

/-- The exterior copy of `z` is not a cut vertex. -/
theorem z_not_cut
    (O : P.ExteriorOrderedBlockChain) :
    ¬IsCutVertex P.exteriorGraph
      (P.exteriorZ O.endpoints.z_mem_otherRegion) :=
  O.endpoints.z_not_cut

/-- The exterior copy of `y` is not a cut vertex. -/
theorem y_not_cut
    (O : P.ExteriorOrderedBlockChain) :
    ¬IsCutVertex P.exteriorGraph P.exteriorY :=
  O.endpoints.y_not_cut

/-- The two marked ambient vertices are distinct. -/
theorem y_ne_z
    (O : P.ExteriorOrderedBlockChain) :
    y ≠ z :=
  O.endpoints.y_ne_z

/-- Every displayed cut vertex belongs to the block on its left. -/
theorem cut_mem_left
    (O : P.ExteriorOrderedBlockChain)
    (i : Fin O.chain.cutCount) :
    (O.chain.cuts i).1 ∈
      (O.chain.blocks ⟨i.1, by omega⟩).carrier :=
  O.chain.cut_mem_left i

/-- Every displayed cut vertex belongs to the block on its right. -/
theorem cut_mem_right
    (O : P.ExteriorOrderedBlockChain)
    (i : Fin O.chain.cutCount) :
    (O.chain.cuts i).1 ∈
      (O.chain.blocks
        ⟨i.1 + 1, by omega⟩).carrier :=
  O.chain.cut_mem_right i

/-- Consecutive chain blocks intersect in exactly their displayed cut. -/
theorem consecutive_inter
    (O : P.ExteriorOrderedBlockChain)
    (i : Fin O.chain.cutCount) :
    (O.chain.blocks ⟨i.1, by omega⟩).carrier ∩
        (O.chain.blocks
          ⟨i.1 + 1, by omega⟩).carrier =
      {(O.chain.cuts i).1} :=
  O.chain.consecutive_inter i

/-- Nonconsecutive chain blocks are vertex-disjoint. -/
theorem nonconsecutive_inter_eq_empty
    (O : P.ExteriorOrderedBlockChain)
    (i j : Fin (O.chain.cutCount + 1))
    (hfar :
      i.1 + 1 < j.1 ∨
        j.1 + 1 < i.1) :
    (O.chain.blocks i).carrier ∩
        (O.chain.blocks j).carrier = ∅ :=
  O.chain.nonconsecutive_inter_eq_empty
    P.exteriorGraph_connected
    O.incidence_degree_le_two i j hfar

/-- Every exterior block occurs exactly once in the displayed chain. -/
theorem existsUnique_block_index
    (O : P.ExteriorOrderedBlockChain)
    (B : GraphBlock P.exteriorGraph) :
    ∃! i, O.chain.blocks i = B :=
  O.chain.existsUnique_block_index B

/-- Every exterior cut vertex occurs exactly once in the displayed chain. -/
theorem existsUnique_cut_index
    (O : P.ExteriorOrderedBlockChain)
    (c :
      {v : P.ExteriorVertex //
        IsCutVertex P.exteriorGraph v}) :
    ∃! i, O.chain.cuts i = c :=
  O.chain.existsUnique_cut_index c

end ExteriorOrderedBlockChain

/--
Construct the exterior ordered block chain from Claim 3.15 and orient it
from the protected `z`-leaf to the protected `y`-leaf.
-/
noncomputable def exteriorOrderedBlockChain
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    P.ExteriorOrderedBlockChain := by
  let E :=
    P.exteriorBlockEndpoints
      M D hregion hall
  let hTree :=
    P.exteriorBlockCutIncidence_isTree hregion
  let hdegree :
      ∀ n : BlockCutNode P.exteriorGraph,
        (blockCutIncidence P.exteriorGraph).degree n ≤ 2 :=
    P.exteriorBlockCutIncidence_degree_le_two
      M D hregion hall
  let chain :=
    BlockCutIncidence.OrderedBlockChain.ofTwoLeafBlocks
      hTree hdegree E.zBlock E.yBlock
      E.zBlock_ne_yBlock
      E.zBlock_degree_eq_one
      E.yBlock_degree_eq_one
  refine {
    endpoints := E
    chain := chain
    incidence_isTree := hTree
    incidence_degree_le_two := hdegree
    first_block_eq_z := ?_
    last_block_eq_y := ?_
  }
  · exact
      BlockCutIncidence.OrderedBlockChain.ofTwoLeafBlocks_first_block
        hTree hdegree E.zBlock E.yBlock
        E.zBlock_ne_yBlock
        E.zBlock_degree_eq_one
        E.yBlock_degree_eq_one
  · exact
      BlockCutIncidence.OrderedBlockChain.ofTwoLeafBlocks_last_block
        hTree hdegree E.zBlock E.yBlock
        E.zBlock_ne_yBlock
        E.zBlock_degree_eq_one
        E.yBlock_degree_eq_one

end PreferredWorkingCoreData

end COY

end DeanK5
