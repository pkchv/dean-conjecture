import DeanK5.Graph.OrderedBlockChain

/-!
# Paths along an ordered block chain

An ordered block chain lists its blocks as

`B₀, b₀, B₁, b₁, ..., bₜ₋₁, Bₜ`.

This file turns a contiguous interval of that list into an actual connected
vertex carrier.  It then extracts simple ambient paths whose support stays in
the interval.  The prefix and suffix specializations are the forms used in
the exterior-block argument: a prefix path can run from any earlier block to
a specified cut, while a suffix path runs from a cut through the block on its
right to the final block.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace BlockCutIncidence.OrderedBlockChain

variable [DecidableEq V]
  {G : SimpleGraph V}

/-- Finiteness of block--cut nodes used in the interval-path arguments. -/
noncomputable local instance orderedBlockChainPathsNodeFintype
    [Fintype V] (G : SimpleGraph V) :
    Fintype (BlockCutNode G) :=
  Fintype.ofFinite _

/-- Decidable incidence adjacency used in the interval-path arguments. -/
noncomputable local instance orderedBlockChainPathsAdjDecidable
    [Fintype V] (G : SimpleGraph V) :
    DecidableRel (blockCutIncidence G).Adj :=
  Classical.decRel _

/--
The carrier of the block at a natural-number index, and the empty carrier
outside the block-index range.
-/
def blockCarrierAt
    (chain : OrderedBlockChain G)
    (i : ℕ) :
    Finset V :=
  if hi : i < chain.cutCount + 1 then
    (chain.blocks ⟨i, hi⟩).carrier
  else
    ∅

@[simp] theorem blockCarrierAt_eq
    (chain : OrderedBlockChain G)
    {i : ℕ}
    (hi : i < chain.cutCount + 1) :
    chain.blockCarrierAt i =
      (chain.blocks ⟨i, hi⟩).carrier := by
  simp [blockCarrierAt, hi]

@[simp] theorem blockCarrierAt_eq_empty
    (chain : OrderedBlockChain G)
    {i : ℕ}
    (hi : chain.cutCount + 1 ≤ i) :
    chain.blockCarrierAt i = ∅ := by
  simp [blockCarrierAt, Nat.not_lt.mpr hi]

/--
The union of `len + 1` consecutive block carriers, beginning at `start`.

The definition is recursive in the interval length so that extending an
interval by its next block is definitionally a union.
-/
def intervalCarrier
    (chain : OrderedBlockChain G)
    (start : ℕ) :
    ℕ → Finset V
  | 0 => chain.blockCarrierAt start
  | len + 1 =>
      chain.intervalCarrier start len ∪
        chain.blockCarrierAt (start + len + 1)

@[simp] theorem intervalCarrier_zero
    (chain : OrderedBlockChain G)
    (start : ℕ) :
    chain.intervalCarrier start 0 =
      chain.blockCarrierAt start :=
  rfl

@[simp] theorem intervalCarrier_succ
    (chain : OrderedBlockChain G)
    (start len : ℕ) :
    chain.intervalCarrier start (len + 1) =
      chain.intervalCarrier start len ∪
        chain.blockCarrierAt (start + len + 1) :=
  rfl

/--
Every block at an offset in an interval contributes its whole carrier to
that interval.
-/
theorem blockCarrierAt_add_subset_intervalCarrier
    (chain : OrderedBlockChain G)
    {start len k : ℕ}
    (hk : k ≤ len) :
    chain.blockCarrierAt (start + k) ⊆
      chain.intervalCarrier start len := by
  induction len with
  | zero =>
      have hkZero : k = 0 := by omega
      subst k
      simp
  | succ len ih =>
      by_cases hkLast : k = len + 1
      · subst k
        exact Finset.subset_union_right
      · have hkPrevious : k ≤ len := by omega
        exact
          (ih hkPrevious).trans
            Finset.subset_union_left

/--
The actual chain block at an offset in a valid interval is contained in the
interval carrier.
-/
theorem block_subset_intervalCarrier
    (chain : OrderedBlockChain G)
    {start len k : ℕ}
    (hk : k ≤ len)
    (hbound : start + len ≤ chain.cutCount) :
    (chain.blocks
        ⟨start + k, by omega⟩).carrier ⊆
      chain.intervalCarrier start len := by
  have hindex :
      start + k < chain.cutCount + 1 := by
    omega
  rw [← chain.blockCarrierAt_eq hindex]
  exact
    chain.blockCarrierAt_add_subset_intervalCarrier hk

/--
A valid contiguous interval of blocks induces a connected graph.

At the induction step, the cut vertex between the old final block and the
new block witnesses a nonempty intersection.
-/
theorem intervalCarrier_connected
    (chain : OrderedBlockChain G)
    {start len : ℕ}
    (hbound : start + len ≤ chain.cutCount) :
    (G.induce
      (↑(chain.intervalCarrier start len) : Set V)).Connected := by
  induction len with
  | zero =>
      have hstart :
          start < chain.cutCount + 1 := by
        omega
      rw [intervalCarrier_zero,
        chain.blockCarrierAt_eq hstart]
      exact
        (chain.blocks ⟨start, hstart⟩).connected
  | succ len ih =>
      have hprevious :
          start + len ≤ chain.cutCount := by
        omega
      have hcutIndex :
          start + len < chain.cutCount := by
        omega
      let i : Fin chain.cutCount :=
        ⟨start + len, hcutIndex⟩
      have hnewIndex :
          start + len + 1 < chain.cutCount + 1 := by
        omega
      have hcutOld :
          (chain.cuts i).1 ∈
            chain.intervalCarrier start len := by
        apply
          chain.block_subset_intervalCarrier
            (start := start) (len := len) (k := len)
            (by omega) hprevious
        simpa [i] using chain.cut_mem_left i
      have hcutNew :
          (chain.cuts i).1 ∈
            chain.blockCarrierAt (start + len + 1) := by
        rw [chain.blockCarrierAt_eq hnewIndex]
        simpa [i] using chain.cut_mem_right i
      have hinter :
          ((↑(chain.intervalCarrier start len) : Set V) ∩
            (↑(chain.blockCarrierAt
              (start + len + 1)) : Set V)).Nonempty :=
        ⟨(chain.cuts i).1, hcutOld, hcutNew⟩
      have hnewConnected :
          (G.induce
            (↑(chain.blockCarrierAt
              (start + len + 1)) : Set V)).Connected := by
        rw [chain.blockCarrierAt_eq hnewIndex]
        exact
          (chain.blocks
            ⟨start + len + 1, hnewIndex⟩).connected
      rw [intervalCarrier_succ]
      have hset :
          (↑(chain.intervalCarrier start len ∪
            chain.blockCarrierAt
              (start + len + 1)) : Set V) =
            (↑(chain.intervalCarrier start len) : Set V) ∪
              (↑(chain.blockCarrierAt
                (start + len + 1)) : Set V) := by
        ext v
        simp
      rw [hset]
      exact
        G.induce_union_connected
          (ih hprevious).preconnected
          hnewConnected.preconnected
          hinter

/--
Any two vertices of a valid block interval are joined by a simple ambient
path supported entirely on that interval.
-/
theorem exists_path_in_intervalCarrier
    (chain : OrderedBlockChain G)
    {start len : ℕ}
    (hbound : start + len ≤ chain.cutCount)
    {a b : V}
    (ha : a ∈ chain.intervalCarrier start len)
    (hb : b ∈ chain.intervalCarrier start len) :
    ∃ P : SimplePath G a b,
      ∀ v ∈ P.walk.support,
        v ∈ chain.intervalCarrier start len := by
  let carrier : Set V :=
    ↑(chain.intervalCarrier start len)
  let aCarrier : carrier :=
    ⟨a, ha⟩
  let bCarrier : carrier :=
    ⟨b, hb⟩
  obtain ⟨p, hp⟩ :=
    (chain.intervalCarrier_connected hbound).preconnected.exists_isPath
      aCarrier bCarrier
  let inclusion :
      G.induce carrier →g G :=
    (Embedding.induce carrier).toHom
  let P : SimplePath G a b := {
    walk := p.map inclusion
    isPath := hp.map Subtype.val_injective
  }
  refine ⟨P, ?_⟩
  intro v hv
  change v ∈ (p.map inclusion).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨w, hw, hwv⟩ :=
    List.mem_map.mp hv
  change w.1 = v at hwv
  rw [← hwv]
  exact w.2

/--
Prefix specialization: a vertex in any block no later than cut `j` can be
joined to that cut by a simple path supported on blocks `0,...,j`.
-/
theorem exists_prefix_path_to_cut
    (chain : OrderedBlockChain G)
    (i : Fin (chain.cutCount + 1))
    (j : Fin chain.cutCount)
    (hij : i.1 ≤ j.1)
    {a : V}
    (ha :
      a ∈ (chain.blocks i).carrier) :
    ∃ P : SimplePath G a (chain.cuts j).1,
      ∀ v ∈ P.walk.support,
        v ∈ chain.intervalCarrier 0 j.1 := by
  have hbound :
      0 + j.1 ≤ chain.cutCount := by
    omega
  have hiOffset :
      i.1 ≤ j.1 := hij
  have haInterval :
      a ∈ chain.intervalCarrier 0 j.1 := by
    apply
      chain.block_subset_intervalCarrier
        (start := 0) (len := j.1) (k := i.1)
        hiOffset hbound
    simpa using ha
  have hcutInterval :
      (chain.cuts j).1 ∈
        chain.intervalCarrier 0 j.1 := by
    apply
      chain.block_subset_intervalCarrier
        (start := 0) (len := j.1) (k := j.1)
        (by omega) hbound
    simpa using chain.cut_mem_left j
  exact
    chain.exists_path_in_intervalCarrier
      hbound haInterval hcutInterval

/--
Suffix specialization: a cut can be joined to a vertex of the final block
using only blocks strictly to the right of that cut.
-/
theorem exists_cut_to_lastBlock_path
    (chain : OrderedBlockChain G)
    (i : Fin chain.cutCount)
    {y : V}
    (hy :
      y ∈
        (chain.blocks
          ⟨chain.cutCount, by omega⟩).carrier) :
    ∃ P : SimplePath G (chain.cuts i).1 y,
      ∀ v ∈ P.walk.support,
        v ∈
          chain.intervalCarrier
            (i.1 + 1)
            (chain.cutCount - (i.1 + 1)) := by
  let len :=
    chain.cutCount - (i.1 + 1)
  have hiRight :
      i.1 + 1 ≤ chain.cutCount := by
    omega
  have hbound :
      i.1 + 1 + len ≤ chain.cutCount := by
    dsimp [len]
    omega
  have hsum :
      i.1 + 1 + len = chain.cutCount := by
    dsimp [len]
    omega
  have hcutInterval :
      (chain.cuts i).1 ∈
        chain.intervalCarrier (i.1 + 1) len := by
    apply
      chain.block_subset_intervalCarrier
        (start := i.1 + 1) (len := len) (k := 0)
        (by omega) hbound
    simpa using chain.cut_mem_right i
  have hyInterval :
      y ∈
        chain.intervalCarrier (i.1 + 1) len := by
    have hlastSubset :=
      chain.block_subset_intervalCarrier
        (start := i.1 + 1) (len := len) (k := len)
        (by omega) hbound
    have hlastIndex :
        (⟨i.1 + 1 + len, by omega⟩ :
          Fin (chain.cutCount + 1)) =
          ⟨chain.cutCount, by omega⟩ := by
      apply Fin.ext
      exact hsum
    rw [hlastIndex] at hlastSubset
    exact hlastSubset hy
  exact
    chain.exists_path_in_intervalCarrier
      hbound hcutInterval hyInterval

section Finite

variable [Fintype V]

/--
A block lying at least one full block to the left or right of an interval
is disjoint from the interval carrier.

The hypotheses say that the external block is nonconsecutive to every
block in the interval.  This is the support-exclusion form used when paths
from separated portions of a block chain are assembled.
-/
theorem intervalCarrier_inter_block_eq_empty
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {start len : ℕ}
    (hbound : start + len ≤ chain.cutCount)
    (j : Fin (chain.cutCount + 1))
    (hfar :
      j.1 + 1 < start ∨
        start + len + 1 < j.1) :
    chain.intervalCarrier start len ∩
        (chain.blocks j).carrier = ∅ := by
  induction len with
  | zero =>
      have hstart :
          start < chain.cutCount + 1 := by
        omega
      rw [intervalCarrier_zero,
        chain.blockCarrierAt_eq hstart]
      exact
        chain.nonconsecutive_inter_eq_empty
          hconnected hdegree
          ⟨start, hstart⟩ j
          (by
            rcases hfar with hleft | hright
            · exact Or.inr hleft
            · exact Or.inl hright)
  | succ len ih =>
      have hprevious :
          start + len ≤ chain.cutCount := by
        omega
      have hnewIndex :
          start + len + 1 < chain.cutCount + 1 := by
        omega
      have hfarPrevious :
          j.1 + 1 < start ∨
            start + len + 1 < j.1 := by
        rcases hfar with hleft | hright
        · exact Or.inl hleft
        · exact Or.inr (by omega)
      have hfarNew :
          (start + len + 1) + 1 < j.1 ∨
            j.1 + 1 < start + len + 1 := by
        rcases hfar with hleft | hright
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      have hpreviousEmpty :=
        ih hprevious hfarPrevious
      have hnewEmpty :
          (chain.blocks
              ⟨start + len + 1, hnewIndex⟩).carrier ∩
            (chain.blocks j).carrier = ∅ :=
        chain.nonconsecutive_inter_eq_empty
          hconnected hdegree
          ⟨start + len + 1, hnewIndex⟩ j
          hfarNew
      rw [intervalCarrier_succ,
        chain.blockCarrierAt_eq hnewIndex]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hvUnion :
          v ∈ chain.intervalCarrier start len ∨
            v ∈
              (chain.blocks
                ⟨start + len + 1, hnewIndex⟩).carrier :=
        Finset.mem_union.mp
          (Finset.mem_inter.mp hv).1
      have hvJ :=
        (Finset.mem_inter.mp hv).2
      rcases hvUnion with hvPrevious | hvNew
      · have :
            v ∈ chain.intervalCarrier start len ∩
              (chain.blocks j).carrier :=
          Finset.mem_inter.mpr ⟨hvPrevious, hvJ⟩
        rw [hpreviousEmpty] at this
        simp at this
      · have :
            v ∈
              (chain.blocks
                ⟨start + len + 1, hnewIndex⟩).carrier ∩
                (chain.blocks j).carrier :=
          Finset.mem_inter.mpr ⟨hvNew, hvJ⟩
        rw [hnewEmpty] at this
        simp at this

/--
An interval meets the block immediately to its right exactly in their
displayed boundary cut.
-/
theorem intervalCarrier_inter_nextBlock_eq_singleton
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {start len : ℕ}
    (hbound : start + len < chain.cutCount) :
    chain.intervalCarrier start len ∩
        (chain.blocks
          ⟨start + len + 1, by omega⟩).carrier =
      {(chain.cuts
        ⟨start + len, hbound⟩).1} := by
  cases len with
  | zero =>
      have hstart :
          start < chain.cutCount + 1 := by
        omega
      rw [intervalCarrier_zero,
        chain.blockCarrierAt_eq hstart]
      exact
        chain.consecutive_inter
          ⟨start, hbound⟩
  | succ len =>
      have hpreviousBound :
          start + len ≤ chain.cutCount := by
        omega
      have hlastIndex :
          start + len + 1 < chain.cutCount + 1 := by
        omega
      let nextIndex : Fin (chain.cutCount + 1) :=
        ⟨start + len + 2, by omega⟩
      have hpreviousEmpty :
          chain.intervalCarrier start len ∩
              (chain.blocks nextIndex).carrier =
            ∅ := by
        apply
          chain.intervalCarrier_inter_block_eq_empty
            hconnected hdegree hpreviousBound
            nextIndex
        exact Or.inr (by
          dsimp [nextIndex]
          omega)
      have hlastInter :
          (chain.blocks
              ⟨start + len + 1, hlastIndex⟩).carrier ∩
              (chain.blocks nextIndex).carrier =
            {(chain.cuts
              ⟨start + len + 1, by omega⟩).1} := by
        simpa [nextIndex, Nat.add_assoc] using
          chain.consecutive_inter
            ⟨start + len + 1, by omega⟩
      rw [intervalCarrier_succ,
        chain.blockCarrierAt_eq hlastIndex]
      apply Finset.ext
      intro v
      simp only [Finset.mem_inter, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hvPrevious | hvLast, hvNext⟩
        · have hvNext' :
              v ∈ (chain.blocks nextIndex).carrier := by
            simpa [nextIndex, Nat.add_assoc] using hvNext
          have hvInter :
              v ∈ chain.intervalCarrier start len ∩
                (chain.blocks nextIndex).carrier :=
            Finset.mem_inter.mpr
              ⟨hvPrevious, hvNext'⟩
          rw [hpreviousEmpty] at hvInter
          simp at hvInter
        · have hvNext' :
              v ∈ (chain.blocks nextIndex).carrier := by
            simpa [nextIndex, Nat.add_assoc] using hvNext
          have hvInter :
              v ∈
                (chain.blocks
                  ⟨start + len + 1, hlastIndex⟩).carrier ∩
                  (chain.blocks nextIndex).carrier :=
            Finset.mem_inter.mpr
              ⟨hvLast, hvNext'⟩
          rw [hlastInter] at hvInter
          simpa [Nat.add_assoc] using hvInter
      · intro hv
        have hv' :
            v =
              (chain.cuts
                ⟨start + len + 1, by omega⟩).1 := by
          simpa [Nat.add_assoc] using hv
        subst v
        constructor
        · exact Or.inr
            (chain.cut_mem_left
              ⟨start + len + 1, by omega⟩)
        · simpa [nextIndex, Nat.add_assoc] using
            chain.cut_mem_right
              ⟨start + len + 1, by omega⟩

/--
An interval beginning after block zero meets the block immediately to its
left exactly in their displayed boundary cut.
-/
theorem previousBlock_inter_intervalCarrier_eq_singleton
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {start len : ℕ}
    (hstart : 0 < start)
    (hbound : start + len ≤ chain.cutCount) :
    (chain.blocks
        ⟨start - 1, by omega⟩).carrier ∩
        chain.intervalCarrier start len =
      {(chain.cuts
        ⟨start - 1, by omega⟩).1} := by
  induction len with
  | zero =>
      have hcurrentIndex :
          start < chain.cutCount + 1 := by
        omega
      rw [intervalCarrier_zero,
        chain.blockCarrierAt_eq hcurrentIndex]
      have hcut :=
        chain.consecutive_inter
          ⟨start - 1, by omega⟩
      simpa [Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (by omega : start ≠ 0))] using hcut
  | succ len ih =>
      have hpreviousBound :
          start + len ≤ chain.cutCount := by
        omega
      have hnewIndex :
          start + len + 1 < chain.cutCount + 1 := by
        omega
      let previousIndex : Fin (chain.cutCount + 1) :=
        ⟨start - 1, by omega⟩
      let newBlockIndex : Fin (chain.cutCount + 1) :=
        ⟨start + len + 1, hnewIndex⟩
      have hnewEmpty :
          (chain.blocks previousIndex).carrier ∩
              (chain.blocks newBlockIndex).carrier =
            ∅ :=
        chain.nonconsecutive_inter_eq_empty
          hconnected hdegree
          previousIndex newBlockIndex
          (Or.inl (by
            dsimp [previousIndex, newBlockIndex]
            omega))
      have hnewEmpty' :
          (chain.blocks
              ⟨start - 1, by omega⟩).carrier ∩
              (chain.blocks
                ⟨start + len + 1, hnewIndex⟩).carrier =
            ∅ := by
        simpa [previousIndex, newBlockIndex] using
          hnewEmpty
      rw [intervalCarrier_succ,
        chain.blockCarrierAt_eq hnewIndex,
        Finset.inter_union_distrib_left,
        ih hpreviousBound, hnewEmpty',
        Finset.union_empty]

/--
Every path supplied by `exists_path_in_intervalCarrier` avoids every block
nonconsecutive to its interval.
-/
theorem path_support_disjoint_block_of_mem_interval
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {start len : ℕ}
    (hbound : start + len ≤ chain.cutCount)
    {a b : V}
    (P : SimplePath G a b)
    (hP :
      ∀ v ∈ P.walk.support,
        v ∈ chain.intervalCarrier start len)
    (j : Fin (chain.cutCount + 1))
    (hfar :
      j.1 + 1 < start ∨
        start + len + 1 < j.1) :
    Disjoint P.walk.support.toFinset
      (chain.blocks j).carrier := by
  apply Finset.disjoint_left.mpr
  intro v hvP hvJ
  have hinter :=
    chain.intervalCarrier_inter_block_eq_empty
      hconnected hdegree hbound j hfar
  have hvInter :
      v ∈ chain.intervalCarrier start len ∩
        (chain.blocks j).carrier :=
    Finset.mem_inter.mpr
      ⟨hP v (by simpa using hvP), hvJ⟩
  rw [hinter] at hvInter
  simp at hvInter

/--
A path supported on an interval can meet the next block only at the
boundary cut.
-/
theorem path_meets_nextBlock_only_at_cut
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {start len : ℕ}
    (hbound : start + len < chain.cutCount)
    {a b v : V}
    (P : SimplePath G a b)
    (hP :
      ∀ w ∈ P.walk.support,
        w ∈ chain.intervalCarrier start len)
    (hvP : v ∈ P.walk.support)
    (hvNext :
      v ∈
        (chain.blocks
          ⟨start + len + 1, by omega⟩).carrier) :
    v =
      (chain.cuts
        ⟨start + len, hbound⟩).1 := by
  have hinter :=
    chain.intervalCarrier_inter_nextBlock_eq_singleton
      hconnected hdegree hbound
  have hvInter :
      v ∈ chain.intervalCarrier start len ∩
        (chain.blocks
          ⟨start + len + 1, by omega⟩).carrier :=
    Finset.mem_inter.mpr ⟨hP v hvP, hvNext⟩
  rw [hinter] at hvInter
  simpa using hvInter

/--
A path supported on an interval can meet the preceding block only at the
boundary cut.
-/
theorem path_meets_previousBlock_only_at_cut
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {start len : ℕ}
    (hstart : 0 < start)
    (hbound : start + len ≤ chain.cutCount)
    {a b v : V}
    (P : SimplePath G a b)
    (hP :
      ∀ w ∈ P.walk.support,
        w ∈ chain.intervalCarrier start len)
    (hvP : v ∈ P.walk.support)
    (hvPrevious :
      v ∈
        (chain.blocks
          ⟨start - 1, by omega⟩).carrier) :
    v =
      (chain.cuts
        ⟨start - 1, by omega⟩).1 := by
  have hinter :=
    chain.previousBlock_inter_intervalCarrier_eq_singleton
      hconnected hdegree hstart hbound
  have hvInter :
      v ∈
        (chain.blocks
          ⟨start - 1, by omega⟩).carrier ∩
          chain.intervalCarrier start len :=
    Finset.mem_inter.mpr ⟨hvPrevious, hP v hvP⟩
  rw [hinter] at hvInter
  simpa using hvInter

end Finite

end BlockCutIncidence.OrderedBlockChain

end DeanK5
