import DeanK5.Graph.BlockCutChain
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Ordered block chains

A Hamiltonian path of the block--cut incidence tree whose ends are block
nodes canonically orders all blocks and cut vertices:

`B₀, b₀, B₁, b₁, ..., bₜ₋₁, Bₜ`.

This file packages that order without appealing to an informal block-tree
picture.  Even positions of the incidence path are block nodes, odd
positions are cut nodes, and path simplicity gives injectivity.  Incidence
at consecutive positions then identifies the intersection of consecutive
blocks.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace BlockCutIncidence

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Finiteness of block--cut nodes used to construct an ordered chain. -/
noncomputable local instance orderedBlockChainNodeFintype
    (G : SimpleGraph V) :
    Fintype (BlockCutNode G) :=
  Fintype.ofFinite _

/-- Decidable incidence adjacency used to construct an ordered chain. -/
noncomputable local instance orderedBlockChainAdjDecidable
    (G : SimpleGraph V) :
    DecidableRel (blockCutIncidence G).Adj :=
  Classical.decRel _

/-- The canonical two-coloring of the block--cut incidence graph. -/
def blockCutColoring :
    (blockCutIncidence G).Coloring Bool :=
  SimpleGraph.Coloring.mk
    (fun n =>
      match n with
      | .inl _ => true
      | .inr _ => false)
    (by
      intro m n hmn
      cases m with
      | inl B =>
          cases n with
          | inl C =>
              exact False.elim
                (not_blockCutIncidence_adj_block_block
                  G B C hmn)
          | inr _ =>
              simp
      | inr c =>
          cases n with
          | inl _ =>
              simp
          | inr d =>
              exact False.elim
                (not_blockCutIncidence_adj_cut_cut
                  G c d hmn))

omit [Fintype V] in
@[simp] theorem blockCutColoring_block
    (B : GraphBlock G) :
    blockCutColoring (G := G) (.inl B) = true :=
  rfl

omit [Fintype V] in
@[simp] theorem blockCutColoring_cut
    (c : {v : V // IsCutVertex G v}) :
    blockCutColoring (G := G) (.inr c) = false :=
  rfl

omit [Fintype V] in
/--
Every even position of an incidence walk starting at a block node is a
block node.
-/
theorem exists_block_getVert_of_even
    {B : GraphBlock G}
    {n : BlockCutNode G}
    (p : (blockCutIncidence G).Walk (.inl B) n)
    {i : ℕ}
    (hi : i ≤ p.length)
    (heven : Even i) :
    ∃ C : GraphBlock G,
      p.getVert i = .inl C := by
  have htakeLength :
      (p.take i).length = i := by
    simp [Nat.min_eq_left hi]
  have hevenTake :
      Even (p.take i).length := by
    rw [htakeLength]
    exact heven
  have hcolor :
      blockCutColoring
          (G := G) (p.getVert i) = true := by
    have hcongr :=
      ((blockCutColoring (G := G)).even_length_iff_congr
        (p.take i)).1
        hevenTake
    simpa using hcongr.symm
  cases hnode : p.getVert i with
  | inl C =>
      exact ⟨C, rfl⟩
  | inr c =>
      simp [hnode] at hcolor

omit [Fintype V] in
/--
Every odd position of an incidence walk starting at a block node is a cut
node.
-/
theorem exists_cut_getVert_of_odd
    {B : GraphBlock G}
    {n : BlockCutNode G}
    (p : (blockCutIncidence G).Walk (.inl B) n)
    {i : ℕ}
    (hi : i ≤ p.length)
    (hodd : Odd i) :
    ∃ c : {v : V // IsCutVertex G v},
      p.getVert i = .inr c := by
  have htakeLength :
      (p.take i).length = i := by
    simp [Nat.min_eq_left hi]
  have hoddTake :
      Odd (p.take i).length := by
    rw [htakeLength]
    exact hodd
  have hcolor :
      blockCutColoring
          (G := G) (p.getVert i) = false := by
    have hcongr :=
      ((blockCutColoring (G := G)).odd_length_iff_not_congr
        (p.take i)).1
        hoddTake
    simpa using hcongr
  cases hnode : p.getVert i with
  | inl C =>
      simp [hnode] at hcolor
  | inr c =>
      exact ⟨c, rfl⟩

omit [Fintype V] in
/-- An incidence walk between block nodes has even length. -/
theorem walk_length_even_between_blocks
    {B C : GraphBlock G}
    (p :
      (blockCutIncidence G).Walk
        (.inl B) (.inl C)) :
    Even p.length := by
  apply
    ((blockCutColoring (G := G)).even_length_iff_congr
      p).2
  simp

/--
The checked data extracted from a Hamiltonian incidence path.

`cutCount` is the number of cut nodes.  Thus the blocks are indexed by
`Fin (cutCount + 1)`, and the cut vertex at index `i` lies in blocks `i`
and `i+1`.  The final two fields state that these lists contain every
ambient block and every ambient cut vertex.
-/
structure OrderedBlockChain (G : SimpleGraph V) where
  /-- The number of cut vertices in the chain. -/
  cutCount : ℕ
  one_le_cutCount : 1 ≤ cutCount
  /-- The chain's blocks, in incidence-path order. -/
  blocks : Fin (cutCount + 1) → GraphBlock G
  /-- The chain's cut vertices, in incidence-path order. -/
  cuts : Fin cutCount → {v : V // IsCutVertex G v}
  blocks_injective : Function.Injective blocks
  cuts_injective : Function.Injective cuts
  cut_mem_left :
    ∀ i : Fin cutCount,
      (cuts i).1 ∈ (blocks ⟨i.1, by omega⟩).carrier
  cut_mem_right :
    ∀ i : Fin cutCount,
      (cuts i).1 ∈
        (blocks ⟨i.1 + 1, by omega⟩).carrier
  consecutive_inter :
    ∀ i : Fin cutCount,
      (blocks ⟨i.1, by omega⟩).carrier ∩
          (blocks ⟨i.1 + 1, by omega⟩).carrier =
        {(cuts i).1}
  blocks_exhaustive :
    ∀ B : GraphBlock G, ∃ i, blocks i = B
  cuts_exhaustive :
    ∀ c : {v : V // IsCutVertex G v}, ∃ i, cuts i = c

namespace OrderedBlockChain

/-- The number of blocks in an ordered block chain. -/
def blockCount
    (chain : OrderedBlockChain G) :
    ℕ :=
  chain.cutCount + 1

omit [Fintype V] in
/-- Every ordered block chain has at least two blocks. -/
theorem two_le_blockCount
    (chain : OrderedBlockChain G) :
    2 ≤ chain.blockCount := by
  exact Nat.succ_le_succ chain.one_le_cutCount

omit [Fintype V] in
/-- Every ambient block occurs at a unique chain index. -/
theorem existsUnique_block_index
    (chain : OrderedBlockChain G)
    (B : GraphBlock G) :
    ∃! i, chain.blocks i = B := by
  obtain ⟨i, hi⟩ :=
    chain.blocks_exhaustive B
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact
    chain.blocks_injective
      (hj.trans hi.symm)

omit [Fintype V] in
/-- Every ambient cut vertex occurs at a unique chain index. -/
theorem existsUnique_cut_index
    (chain : OrderedBlockChain G)
    (c : {v : V // IsCutVertex G v}) :
    ∃! i, chain.cuts i = c := by
  obtain ⟨i, hi⟩ :=
    chain.cuts_exhaustive c
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact
    chain.cuts_injective
      (hj.trans hi.symm)

/--
At a cut position of an ordered chain, every block containing that cut
vertex is one of the two displayed consecutive blocks, provided incidence
degrees are at most two.
-/
theorem block_eq_left_or_right_of_cut_mem
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    (i : Fin chain.cutCount)
    (D : GraphBlock G)
    (hmem :
      (chain.cuts i).1 ∈ D.carrier) :
    D = chain.blocks ⟨i.1, by omega⟩ ∨
      D = chain.blocks ⟨i.1 + 1, by omega⟩ := by
  classical
  let left :
      GraphBlock G :=
    chain.blocks ⟨i.1, by omega⟩
  let right :
      GraphBlock G :=
    chain.blocks ⟨i.1 + 1, by omega⟩
  by_contra hnot
  have hDLeft : D ≠ left := by
    intro h
    exact hnot (Or.inl h)
  have hDRight : D ≠ right := by
    intro h
    exact hnot (Or.inr h)
  have hleftRight : left ≠ right := by
    intro h
    have hindex :=
      chain.blocks_injective h
    have hval :
        i.1 = i.1 + 1 :=
      congrArg
        (fun j : Fin (chain.cutCount + 1) => j.1)
        hindex
    omega
  have hneighbors :
      ({(Sum.inl D : BlockCutNode G),
          .inl left, .inl right} :
          Finset (BlockCutNode G)) ⊆
        (blockCutIncidence G).neighborFinset
          (.inr (chain.cuts i)) := by
    intro n hn
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · simpa using hmem
    · simpa [left] using chain.cut_mem_left i
    · simpa [right] using chain.cut_mem_right i
  have hthree :
      ({(Sum.inl D : BlockCutNode G),
          .inl left, .inl right} :
          Finset (BlockCutNode G)).card = 3 := by
    simp [hDLeft, hDRight, hleftRight]
  have hcard :=
    Finset.card_le_card hneighbors
  rw [hthree] at hcard
  have hupper :=
    hdegree (.inr (chain.cuts i))
  rw [SimpleGraph.degree] at hupper
  omega

/--
Blocks at nonconsecutive positions of an ordered chain are disjoint.

The ambient connectedness turns a common vertex of two distinct blocks
into a cut vertex.  Exhaustivity locates its cut position in the chain,
and the incidence degree bound then forces both blocks to be the two
consecutive blocks at that position.
-/
theorem nonconsecutive_inter_eq_empty
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    (i j : Fin (chain.cutCount + 1))
    (hfar :
      i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) :
    (chain.blocks i).carrier ∩
        (chain.blocks j).carrier = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hij : i ≠ j := by
    intro h
    have hval :
        i.1 = j.1 :=
      congrArg
        (fun k : Fin (chain.cutCount + 1) => k.1) h
    omega
  have hblocksNe :
      chain.blocks i ≠ chain.blocks j := by
    intro h
    exact hij (chain.blocks_injective h)
  have hcut :
      IsCutVertex G v :=
    GraphBlock.isCutVertex_of_mem_inter
      hconnected
      (chain.blocks i)
      (chain.blocks j)
      hblocksNe
      (Finset.mem_inter.mp hv).1
      (Finset.mem_inter.mp hv).2
  let c : {v : V // IsCutVertex G v} :=
    ⟨v, hcut⟩
  obtain ⟨k, hk⟩ :=
    chain.cuts_exhaustive c
  have hmemI :
      (chain.cuts k).1 ∈
        (chain.blocks i).carrier := by
    rw [hk]
    exact (Finset.mem_inter.mp hv).1
  have hmemJ :
      (chain.cuts k).1 ∈
        (chain.blocks j).carrier := by
    rw [hk]
    exact (Finset.mem_inter.mp hv).2
  have hiCase :=
    chain.block_eq_left_or_right_of_cut_mem
      hdegree k (chain.blocks i) hmemI
  have hjCase :=
    chain.block_eq_left_or_right_of_cut_mem
      hdegree k (chain.blocks j) hmemJ
  rcases hiCase with hiLeft | hiRight
  · have hiIndex :=
      chain.blocks_injective hiLeft
    rcases hjCase with hjLeft | hjRight
    · have hjIndex :=
        chain.blocks_injective hjLeft
      have hiVal :
          i.1 = k.1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hiIndex
      have hjVal :
          j.1 = k.1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hjIndex
      omega
    · have hjIndex :=
        chain.blocks_injective hjRight
      have hiVal :
          i.1 = k.1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hiIndex
      have hjVal :
          j.1 = k.1 + 1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hjIndex
      omega
  · have hiIndex :=
      chain.blocks_injective hiRight
    rcases hjCase with hjLeft | hjRight
    · have hjIndex :=
        chain.blocks_injective hjLeft
      have hiVal :
          i.1 = k.1 + 1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hiIndex
      have hjVal :
          j.1 = k.1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hjIndex
      omega
    · have hjIndex :=
        chain.blocks_injective hjRight
      have hiVal :
          i.1 = k.1 + 1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hiIndex
      have hjVal :
          j.1 = k.1 + 1 :=
        congrArg
          (fun q : Fin (chain.cutCount + 1) => q.1)
          hjIndex
      omega

omit [Fintype V] in
/--
A nontrivial Hamiltonian incidence path between block nodes determines an
ordered block chain.

The construction records `t + 1` block nodes at the even positions and
`t` cut nodes at the odd positions of a path of length `2t`.
-/
noncomputable def ofHamiltonianPath
    {B C : GraphBlock G}
    (hBC : B ≠ C)
    (p :
      (blockCutIncidence G).Walk
        (.inl B) (.inl C))
    (hp : p.IsPath)
    (hall :
      ∀ n : BlockCutNode G, n ∈ p.support) :
    OrderedBlockChain G := by
  classical
  have heven :
      Even p.length :=
    walk_length_even_between_blocks p
  let t : ℕ :=
    Classical.choose heven
  have ht :
      p.length = t + t :=
    Classical.choose_spec heven
  have hstartEnd :
      (Sum.inl B : BlockCutNode G) ≠ .inl C := by
    simpa using hBC
  have hpNotNil : ¬p.Nil :=
    p.not_nil_of_ne hstartEnd
  have hpLengthPositive : 0 < p.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hpNotNil
  have htPositive : 1 ≤ t := by
    omega
  let blocks :
      Fin (t + 1) → GraphBlock G :=
    fun i =>
      Classical.choose
        (exists_block_getVert_of_even
          p
          (i := 2 * i.1)
          (by omega)
          ⟨i.1, by omega⟩)
  let cuts :
      Fin t → {v : V // IsCutVertex G v} :=
    fun i =>
      Classical.choose
        (exists_cut_getVert_of_odd
          p
          (i := 2 * i.1 + 1)
          (by omega)
          ⟨i.1, by omega⟩)
  have hblocks :
      ∀ i : Fin (t + 1),
        p.getVert (2 * i.1) =
          .inl (blocks i) := by
    intro i
    exact
      Classical.choose_spec
        (exists_block_getVert_of_even
          p
          (i := 2 * i.1)
          (by omega)
          ⟨i.1, by omega⟩)
  have hcuts :
      ∀ i : Fin t,
        p.getVert (2 * i.1 + 1) =
          .inr (cuts i) := by
    intro i
    exact
      Classical.choose_spec
        (exists_cut_getVert_of_odd
          p
          (i := 2 * i.1 + 1)
          (by omega)
          ⟨i.1, by omega⟩)
  have hblocksInjective :
      Function.Injective blocks := by
    intro i j hij
    apply Fin.ext
    have hget :
        p.getVert (2 * i.1) =
          p.getVert (2 * j.1) := by
      rw [hblocks i, hblocks j, hij]
    have hindex :
        2 * i.1 = 2 * j.1 :=
      hp.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        hget
    omega
  have hcutsInjective :
      Function.Injective cuts := by
    intro i j hij
    apply Fin.ext
    have hget :
        p.getVert (2 * i.1 + 1) =
          p.getVert (2 * j.1 + 1) := by
      rw [hcuts i, hcuts j, hij]
    have hindex :
        2 * i.1 + 1 = 2 * j.1 + 1 :=
      hp.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        hget
    omega
  have hcutLeft :
      ∀ i : Fin t,
        (cuts i).1 ∈
          (blocks ⟨i.1, by omega⟩).carrier := by
    intro i
    have hadj :=
      p.adj_getVert_succ
        (i := 2 * i.1)
        (by omega)
    rw [hblocks ⟨i.1, by omega⟩,
      hcuts i] at hadj
    exact hadj
  have hcutRight :
      ∀ i : Fin t,
        (cuts i).1 ∈
          (blocks ⟨i.1 + 1, by omega⟩).carrier := by
    intro i
    have hadj :=
      p.adj_getVert_succ
        (i := 2 * i.1 + 1)
        (by omega)
    have hright :=
      hblocks ⟨i.1 + 1, by omega⟩
    have hposition :
        2 * (i.1 + 1) =
          (2 * i.1 + 1) + 1 := by
      omega
    rw [hposition] at hright
    rw [hcuts i, hright] at hadj
    exact hadj
  have hinter :
      ∀ i : Fin t,
        (blocks ⟨i.1, by omega⟩).carrier ∩
            (blocks ⟨i.1 + 1, by omega⟩).carrier =
          {(cuts i).1} := by
    intro i
    have hindices :
        (⟨i.1, by omega⟩ : Fin (t + 1)) ≠
          ⟨i.1 + 1, by omega⟩ := by
      intro h
      have hval :
          i.1 = i.1 + 1 :=
        congrArg
          (fun j : Fin (t + 1) => j.1) h
      omega
    have hne :
        blocks ⟨i.1, by omega⟩ ≠
          blocks ⟨i.1 + 1, by omega⟩ := by
      intro h
      exact hindices (hblocksInjective h)
    exact
      GraphBlock.inter_eq_singleton_of_mem_of_ne
        (blocks ⟨i.1, by omega⟩)
        (blocks ⟨i.1 + 1, by omega⟩)
        hne
        (hcutLeft i)
        (hcutRight i)
  have hblocksExhaustive :
      ∀ D : GraphBlock G,
        ∃ i, blocks i = D := by
    intro D
    obtain ⟨k, hk, hkLength⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
        (hall (.inl D))
    have hkEven : Even k := by
      by_contra hkNotEven
      have hkOdd : Odd k :=
        Nat.not_even_iff_odd.mp hkNotEven
      obtain ⟨c, hc⟩ :=
        exists_cut_getVert_of_odd
          p hkLength hkOdd
      rw [hk] at hc
      simp at hc
    obtain ⟨j, hj⟩ := hkEven
    have hjBound : j < t + 1 := by
      omega
    let index : Fin (t + 1) :=
      ⟨j, hjBound⟩
    refine ⟨index, ?_⟩
    have hposition :
        2 * index.1 = k := by
      dsimp [index]
      omega
    have hnodes :
        (Sum.inl (blocks index) :
            BlockCutNode G) =
          .inl D := by
      rw [← hblocks index, hposition, hk]
    exact Sum.inl_injective hnodes
  have hcutsExhaustive :
      ∀ c : {v : V // IsCutVertex G v},
        ∃ i, cuts i = c := by
    intro c
    obtain ⟨k, hk, hkLength⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
        (hall (.inr c))
    have hkOdd : Odd k := by
      rw [← Nat.not_even_iff_odd]
      intro hkEven
      obtain ⟨D, hD⟩ :=
        exists_block_getVert_of_even
          p hkLength hkEven
      rw [hk] at hD
      simp at hD
    obtain ⟨j, hj⟩ := hkOdd
    have hjBound : j < t := by
      omega
    let index : Fin t :=
      ⟨j, hjBound⟩
    refine ⟨index, ?_⟩
    have hposition :
        2 * index.1 + 1 = k := by
      dsimp [index]
      omega
    have hnodes :
        (Sum.inr (cuts index) :
            BlockCutNode G) =
          .inr c := by
      rw [← hcuts index, hposition, hk]
    exact Sum.inr_injective hnodes
  exact {
    cutCount := t
    one_le_cutCount := htPositive
    blocks := blocks
    cuts := cuts
    blocks_injective := hblocksInjective
    cuts_injective := hcutsInjective
    cut_mem_left := hcutLeft
    cut_mem_right := hcutRight
    consecutive_inter := hinter
    blocks_exhaustive := hblocksExhaustive
    cuts_exhaustive := hcutsExhaustive
  }

/--
The canonical ordered chain selected from two distinct block leaves of a
path-like block--cut incidence tree.
-/
noncomputable def ofTwoLeafBlocks
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
    OrderedBlockChain G := by
  classical
  have hnodes :
      (Sum.inl B : BlockCutNode G) ≠
        .inl C := by
    simpa using hBC
  have hex :=
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
  exact
    ofHamiltonianPath hBC p hp hall

end OrderedBlockChain

end BlockCutIncidence

end DeanK5
