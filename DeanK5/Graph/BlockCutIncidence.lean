import DeanK5.Graph.BlockIntersection

/-!
# The block--cut incidence graph

The block nodes are the maximal nonseparable carriers of a graph, and the
cut nodes are its cut vertices.  A block node is adjacent to a cut node
exactly when the cut vertex belongs to the block.

This file establishes the finite type and connectedness parts of the
classical block--cut tree construction.  Acyclicity and the resulting chain
structure are developed separately.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace GraphBlock

variable [DecidableEq V] {G : SimpleGraph V}

/-- A finite graph has only finitely many graph blocks. -/
noncomputable instance [Finite V] :
    Finite (GraphBlock G) :=
  Finite.of_injective
    (fun B : GraphBlock G => B.carrier)
    (fun _ _ h => GraphBlock.ext h)

end GraphBlock

/-- The two kinds of vertices in the block--cut incidence graph. -/
abbrev BlockCutNode
    [DecidableEq V] (G : SimpleGraph V) :=
  GraphBlock G ⊕ {c : V // IsCutVertex G c}

/--
The bipartite incidence graph between graph blocks and cut vertices.
-/
def blockCutIncidence
    [DecidableEq V] (G : SimpleGraph V) :
    SimpleGraph (BlockCutNode G) where
  Adj a b :=
    match a, b with
    | .inl B, .inr c => c.1 ∈ B.carrier
    | .inr c, .inl B => c.1 ∈ B.carrier
    | .inl _, .inl _ => False
    | .inr _, .inr _ => False
  symm := by
    constructor
    intro a b h
    cases a <;> cases b <;> exact h
  loopless := by
    constructor
    intro a
    cases a <;> simp

@[simp] theorem blockCutIncidence_adj_block_cut
    [DecidableEq V]
    (G : SimpleGraph V)
    (B : GraphBlock G)
    (c : {c : V // IsCutVertex G c}) :
    (blockCutIncidence G).Adj (.inl B) (.inr c) ↔
      c.1 ∈ B.carrier :=
  Iff.rfl

@[simp] theorem blockCutIncidence_adj_cut_block
    [DecidableEq V]
    (G : SimpleGraph V)
    (c : {c : V // IsCutVertex G c})
    (B : GraphBlock G) :
    (blockCutIncidence G).Adj (.inr c) (.inl B) ↔
      c.1 ∈ B.carrier :=
  Iff.rfl

@[simp] theorem not_blockCutIncidence_adj_block_block
    [DecidableEq V]
    (G : SimpleGraph V)
    (B C : GraphBlock G) :
    ¬(blockCutIncidence G).Adj (.inl B) (.inl C) := by
  simp [blockCutIncidence]

@[simp] theorem not_blockCutIncidence_adj_cut_cut
    [DecidableEq V]
    (G : SimpleGraph V)
    (c d : {c : V // IsCutVertex G c}) :
    ¬(blockCutIncidence G).Adj (.inr c) (.inr d) := by
  simp [blockCutIncidence]

namespace BlockCutIncidence

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
Two block nodes that contain a common vertex are connected in the incidence
graph.  If the blocks are distinct, the common vertex is the intermediate
cut node.
-/
theorem reachable_blocks_of_common_vertex
    (hconnected : G.Connected)
    (B C : GraphBlock G)
    {v : V}
    (hvB : v ∈ B.carrier)
    (hvC : v ∈ C.carrier) :
    (blockCutIncidence G).Reachable
      (.inl B) (.inl C) := by
  by_cases hBC : B = C
  · subst C
    exact SimpleGraph.Reachable.refl
      (Sum.inl B : BlockCutNode G)
  · have hcut :
        IsCutVertex G v :=
      B.isCutVertex_of_mem_inter
        hconnected C hBC hvB hvC
    let cutNode :
        {c : V // IsCutVertex G c} :=
      ⟨v, hcut⟩
    have hBcut :
        (blockCutIncidence G).Adj
          (.inl B) (.inr cutNode) := by
      exact hvB
    have hcutC :
        (blockCutIncidence G).Adj
          (.inr cutNode) (.inl C) := by
      exact hvC
    exact hBcut.reachable.trans hcutC.reachable

/--
Blocks containing the endpoints of an ambient walk lie in the same
component of the incidence graph.
-/
theorem reachable_blocks_of_walk
    (hconnected : G.Connected)
    {u v : V}
    (B C : GraphBlock G)
    (huB : u ∈ B.carrier)
    (hvC : v ∈ C.carrier)
    (p : G.Walk u v) :
    (blockCutIncidence G).Reachable
      (.inl B) (.inl C) := by
  induction p generalizing B with
  | nil =>
      exact reachable_blocks_of_common_vertex
        hconnected B C huB hvC
  | @cons u w v huw p ih =>
      obtain ⟨E, huE, hwE⟩ :=
        GraphBlock.exists_of_adj huw
      exact
        (reachable_blocks_of_common_vertex
          hconnected B E huB huE).trans
            (ih E hwE hvC)

/-- Every incidence node can reach an incident block node. -/
theorem exists_reachable_block
    (hconnected : G.Connected)
    (n : BlockCutNode G) :
    ∃ B : GraphBlock G,
      (blockCutIncidence G).Reachable n (.inl B) := by
  cases n with
  | inl B =>
      exact
        ⟨B, SimpleGraph.Reachable.refl
          (Sum.inl B : BlockCutNode G)⟩
  | inr c =>
      obtain ⟨B, C, hBC, hcB, hcC⟩ :=
        GraphBlock.exists_two_distinct_of_isCutVertex
          hconnected c.2
      have hcutB :
          (blockCutIncidence G).Adj
            (.inr c) (.inl B) := by
        exact hcB
      exact ⟨B, hcutB.reachable⟩

/--
The block--cut incidence graph of a finite connected graph of order at
least two is connected.
-/
theorem connected
    (hconnected : G.Connected)
    (horder : 2 ≤ Fintype.card V) :
    (blockCutIncidence G).Connected := by
  have hnodeNonempty :
      Nonempty (BlockCutNode G) := by
    let v : V := Classical.choice hconnected.nonempty
    obtain ⟨B, hvB⟩ :=
      GraphBlock.exists_of_vertex hconnected horder v
    exact ⟨.inl B⟩
  letI : Nonempty (BlockCutNode G) :=
    hnodeNonempty
  apply SimpleGraph.Connected.mk
  intro a b
  obtain ⟨A, haA⟩ :=
    exists_reachable_block hconnected a
  obtain ⟨B, hbB⟩ :=
    exists_reachable_block hconnected b
  have hAne :
      A.carrier.Nonempty :=
    Finset.card_pos.mp (by
      have := A.card_ge_two
      omega)
  have hBne :
      B.carrier.Nonempty :=
    Finset.card_pos.mp (by
      have := B.card_ge_two
      omega)
  obtain ⟨u, huA⟩ := hAne
  obtain ⟨v, hvB⟩ := hBne
  obtain ⟨p⟩ :=
    hconnected.preconnected u v
  exact
    haA.trans
      ((reachable_blocks_of_walk
        hconnected A B huA hvB p).trans hbB.symm)

end BlockCutIncidence

end DeanK5
