import DeanK5.Graph.OrderedBlockChainPaths

/-!
# Membership in ordered block-chain intervals

The recursive definition of `OrderedBlockChain.intervalCarrier` is convenient
for connectivity arguments.  This file records the converse bookkeeping:
every vertex in an interval carrier belongs to one of the blocks in that
interval.  The final results specialize this description to the prefix
`B₀, ..., Bₚ₋₁`.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace BlockCutIncidence.OrderedBlockChain

variable [DecidableEq V]
  {G : SimpleGraph V}

/--
A vertex in an interval carrier belongs to the carrier of a block at some
offset in that interval.

This version does not require the interval to lie in the chain: out-of-range
block carriers are empty by definition.
-/
theorem exists_blockCarrierAt_of_mem_intervalCarrier
    (chain : OrderedBlockChain G)
    {start len : ℕ}
    {v : V}
    (hv : v ∈ chain.intervalCarrier start len) :
    ∃ k : ℕ,
      k ≤ len ∧
        v ∈ chain.blockCarrierAt (start + k) := by
  induction len with
  | zero =>
      exact ⟨0, by omega, by simpa using hv⟩
  | succ len ih =>
      rw [intervalCarrier_succ] at hv
      rcases Finset.mem_union.mp hv with hvPrevious | hvLast
      · obtain ⟨k, hk, hvBlock⟩ := ih hvPrevious
        exact ⟨k, by omega, hvBlock⟩
      · exact ⟨len + 1, by omega, by simpa [Nat.add_assoc] using hvLast⟩

/--
For a valid interval, membership yields an actual block at an offset
`k ≤ len`.
-/
theorem exists_blockAt_add_of_mem_intervalCarrier
    (chain : OrderedBlockChain G)
    {start len : ℕ}
    (hbound : start + len ≤ chain.cutCount)
    {v : V}
    (hv : v ∈ chain.intervalCarrier start len) :
    ∃ k : ℕ, ∃ hk : k ≤ len,
      v ∈
        (chain.blocks
          ⟨start + k, by omega⟩).carrier := by
  obtain ⟨k, hk, hvBlock⟩ :=
    chain.exists_blockCarrierAt_of_mem_intervalCarrier hv
  have hindex :
      start + k < chain.cutCount + 1 := by
    omega
  refine ⟨k, hk, ?_⟩
  rw [chain.blockCarrierAt_eq hindex] at hvBlock
  simpa using hvBlock

/--
Membership in a valid interval carrier is equivalent to membership in one
of its displayed blocks.
-/
theorem mem_intervalCarrier_iff_exists_blockAt_add
    (chain : OrderedBlockChain G)
    {start len : ℕ}
    (hbound : start + len ≤ chain.cutCount)
    {v : V} :
    v ∈ chain.intervalCarrier start len ↔
      ∃ k : ℕ, ∃ hk : k ≤ len,
        v ∈
          (chain.blocks
            ⟨start + k, by omega⟩).carrier := by
  constructor
  · exact chain.exists_blockAt_add_of_mem_intervalCarrier hbound
  · rintro ⟨k, hk, hv⟩
    exact
      chain.block_subset_intervalCarrier
        (start := start) (len := len) (k := k)
        hk hbound hv

/--
Membership in the prefix carrier `B₀ ∪ ... ∪ Bₚ₋₁` is equivalent to
membership in a block whose index is strictly less than `p`.
-/
theorem mem_prefixInterval_iff_exists_block_index_lt
    (chain : OrderedBlockChain G)
    {p : ℕ}
    (hp : 0 < p)
    (hbound : p ≤ chain.cutCount + 1)
    {v : V} :
    v ∈ chain.intervalCarrier 0 (p - 1) ↔
      ∃ i : Fin (chain.cutCount + 1),
        i.1 < p ∧
          v ∈ (chain.blocks i).carrier := by
  have hintervalBound :
      0 + (p - 1) ≤ chain.cutCount := by
    omega
  constructor
  · intro hv
    obtain ⟨k, hk, hvBlock⟩ :=
      (chain.mem_intervalCarrier_iff_exists_blockAt_add
        hintervalBound).1 hv
    let i : Fin (chain.cutCount + 1) :=
      ⟨k, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · change k < p
      omega
    simpa [i] using hvBlock
  · rintro ⟨i, hi, hv⟩
    have hiOffset :
        i.1 ≤ p - 1 := by
      omega
    have hsubset :=
      chain.block_subset_intervalCarrier
        (start := 0) (len := p - 1) (k := i.1)
        hiOffset hintervalBound
    have hindex :
        (⟨0 + i.1, by omega⟩ :
          Fin (chain.cutCount + 1)) = i := by
      apply Fin.ext
      simp
    rw [hindex] at hsubset
    exact hsubset hv

/--
The union of the carriers of all blocks with index less than `p`.
-/
def blocksBeforeCarrier
    (chain : OrderedBlockChain G)
    (p : ℕ) :
    Finset V :=
  (Finset.univ.filter fun i : Fin (chain.cutCount + 1) =>
      i.1 < p).biUnion fun i =>
    (chain.blocks i).carrier

@[simp] theorem mem_blocksBeforeCarrier
    (chain : OrderedBlockChain G)
    {p : ℕ}
    {v : V} :
    v ∈ chain.blocksBeforeCarrier p ↔
      ∃ i : Fin (chain.cutCount + 1),
        i.1 < p ∧
          v ∈ (chain.blocks i).carrier := by
  simp [blocksBeforeCarrier]

/--
For `0 < p ≤ blockCount`, the union of the first `p` block carriers is the
recursive interval carrier beginning at block zero and ending at block
`p - 1`.
-/
theorem blocksBeforeCarrier_eq_intervalCarrier
    (chain : OrderedBlockChain G)
    {p : ℕ}
    (hp : 0 < p)
    (hbound : p ≤ chain.cutCount + 1) :
    chain.blocksBeforeCarrier p =
      chain.intervalCarrier 0 (p - 1) := by
  ext v
  rw [mem_blocksBeforeCarrier]
  exact
    (chain.mem_prefixInterval_iff_exists_block_index_lt
      hp hbound).symm

/--
Raw finite-union form of `blocksBeforeCarrier_eq_intervalCarrier`.
-/
theorem biUnion_blocks_lt_eq_intervalCarrier
    (chain : OrderedBlockChain G)
    {p : ℕ}
    (hp : 0 < p)
    (hbound : p ≤ chain.cutCount + 1) :
    ((Finset.univ.filter fun i : Fin (chain.cutCount + 1) =>
        i.1 < p).biUnion fun i =>
      (chain.blocks i).carrier) =
      chain.intervalCarrier 0 (p - 1) := by
  exact chain.blocksBeforeCarrier_eq_intervalCarrier hp hbound

end BlockCutIncidence.OrderedBlockChain

end DeanK5
