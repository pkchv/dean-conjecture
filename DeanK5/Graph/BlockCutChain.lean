import DeanK5.Graph.BlockCutTree
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Path structure of the block--cut incidence tree

A finite tree of maximum degree two is a path.  More precisely, the unique
simple path between two distinct degree-one vertices contains every graph
vertex.  The first part of this file proves that statement for an arbitrary
finite tree.  The second part specializes it to the block--cut incidence
graph and records its block/cut alternation.

The proof does not appeal to an informal picture of a tree.  If a vertex
outside the chosen path were adjacent to a path vertex, it would add one
ambient neighbour beyond the path subgraph.  At an endpoint this contradicts
degree one; at an internal vertex it contradicts the maximum-degree-two
hypothesis.  The path support is therefore adjacency-closed, and
connectedness makes it the whole vertex set.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace TreePath

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/--
An ambient neighbour outside a path contributes one more neighbour than
the path subgraph records.
-/
private theorem pathNeighbor_ncard_add_one_le_degree
    {a b u w : V}
    (p : G.Walk a b)
    (huw : G.Adj u w)
    (hw : w ∉ p.support) :
    (p.toSubgraph.neighborSet u).ncard + 1 ≤ G.degree u := by
  have hwNotSubgraph :
      w ∉ p.toSubgraph.neighborSet u := by
    intro hwu
    exact hw
      (Walk.mem_support_of_adj_toSubgraph hwu.symm)
  have hsubset :
      insert w (p.toSubgraph.neighborSet u) ⊆
        G.neighborSet u := by
    apply Set.insert_subset
    · exact huw
    · exact p.toSubgraph.neighborSet_subset u
  calc
    (p.toSubgraph.neighborSet u).ncard + 1 =
        (insert w
          (p.toSubgraph.neighborSet u)).ncard := by
      symm
      exact Set.ncard_insert_of_notMem hwNotSubgraph
    _ ≤ (G.neighborSet u).ncard :=
      Set.ncard_le_ncard hsubset
    _ = G.degree u := by
      rw [← G.card_neighborSet_eq_degree]
      exact
        (Set.fintypeCard_eq_ncard
          (G.neighborSet u)).symm

/--
The unique path between two distinct leaves of a finite tree of maximum
degree two is Hamiltonian.
-/
theorem isHamiltonian_of_isPath_between_leaves
    (hTree : G.IsTree)
    (hdegree : ∀ v, G.degree v ≤ 2)
    {a b : V}
    (hab : a ≠ b)
    (ha : G.degree a = 1)
    (hb : G.degree b = 1)
    {p : G.Walk a b}
    (hp : p.IsPath) :
    p.IsHamiltonian := by
  have hpNotNil : ¬p.Nil :=
    p.not_nil_of_ne hab
  have hclosed :
      ∀ {u w : V}, u ∈ p.support →
        G.Adj u w → w ∈ p.support := by
    intro u w hu huw
    by_contra hw
    have hextra :=
      pathNeighbor_ncard_add_one_le_degree
        p huw hw
    by_cases hua : u = a
    · subst u
      have hpathDegree :
          (p.toSubgraph.neighborSet a).ncard = 1 := by
        rw [hp.neighborSet_toSubgraph_startpoint hpNotNil]
        simp
      rw [hpathDegree, ha] at hextra
      omega
    by_cases hub : u = b
    · subst u
      have hpathDegree :
          (p.toSubgraph.neighborSet b).ncard = 1 := by
        rw [hp.neighborSet_toSubgraph_endpoint hpNotNil]
        simp
      rw [hpathDegree, hb] at hextra
      omega
    obtain ⟨i, hiu, hiLength⟩ :=
      Walk.mem_support_iff_exists_getVert.mp hu
    have hiNeZero : i ≠ 0 := by
      intro hi
      apply hua
      simpa [hi] using hiu.symm
    have hiLt : i < p.length := by
      have hiNeLength : i ≠ p.length := by
        intro hi
        apply hub
        simpa [hi] using hiu.symm
      omega
    have hpathDegree :
        (p.toSubgraph.neighborSet u).ncard = 2 := by
      rw [← hiu]
      exact
        hp.ncard_neighborSet_toSubgraph_internal_eq_two
          hiNeZero hiLt
    rw [hpathDegree] at hextra
    have huDegree := hdegree u
    omega
  have hall :
      ∀ v : V, v ∈ p.support := by
    intro v
    obtain ⟨q⟩ :=
      hTree.connected.preconnected a v
    have hpropagate :
        ∀ {r s : V} (q : G.Walk r s),
          r ∈ p.support → s ∈ p.support := by
      intro r s q
      induction q with
      | nil =>
          intro hr
          exact hr
      | @cons r m s hrm q ih =>
          intro hr
          exact ih (hclosed hr hrm)
    exact hpropagate q p.start_mem_support
  exact hp.isHamiltonian_of_mem hall

/--
Existence-and-uniqueness form: a finite maximum-degree-two tree has a
unique Hamiltonian path between any two distinct leaves.
-/
theorem existsUnique_isPath_isHamiltonian_between_leaves
    (hTree : G.IsTree)
    (hdegree : ∀ v, G.degree v ≤ 2)
    {a b : V}
    (hab : a ≠ b)
    (ha : G.degree a = 1)
    (hb : G.degree b = 1) :
    ∃! p : G.Walk a b,
      p.IsPath ∧ p.IsHamiltonian := by
  obtain ⟨p, hp, hpUnique⟩ :=
    hTree.existsUnique_path a b
  refine ⟨p,
    ⟨hp,
      isHamiltonian_of_isPath_between_leaves
        hTree hdegree hab ha hb hp⟩, ?_⟩
  intro q hq
  exact hpUnique q hq.1

end TreePath

namespace BlockCutIncidence

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Finiteness of block--cut nodes used in the path-like tree arguments. -/
noncomputable local instance blockCutChainNodeFintype
    (G : SimpleGraph V) :
    Fintype (BlockCutNode G) :=
  Fintype.ofFinite _

/-- Decidable equality for block--cut nodes in the path-like tree arguments. -/
noncomputable local instance blockCutChainNodeDecidableEq
    (G : SimpleGraph V) :
    DecidableEq (BlockCutNode G) :=
  Classical.decEq _

/-- Decidable incidence adjacency used in the path-like tree arguments. -/
noncomputable local instance blockCutChainAdjDecidable
    (G : SimpleGraph V) :
    DecidableRel (blockCutIncidence G).Adj :=
  Classical.decRel _

/--
In a path-like block--cut tree, the unique path between two specified
distinct leaves contains every incidence node.
-/
theorem existsUnique_leafPath_containing_every_node
    (hTree : (blockCutIncidence G).IsTree)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {a b : BlockCutNode G}
    (hab : a ≠ b)
    (ha : (blockCutIncidence G).degree a = 1)
    (hb : (blockCutIncidence G).degree b = 1) :
    ∃! p : (blockCutIncidence G).Walk a b,
      p.IsPath ∧
        ∀ n : BlockCutNode G, n ∈ p.support := by
  obtain ⟨p, hp, hpUnique⟩ :=
    TreePath.existsUnique_isPath_isHamiltonian_between_leaves
      hTree hdegree hab ha hb
  refine ⟨p, ⟨hp.1, hp.2.mem_support⟩, ?_⟩
  intro q hq
  exact hpUnique q
    ⟨hq.1, hq.1.isHamiltonian_of_mem hq.2⟩

omit [Fintype V] in
/--
Every incidence edge joins a block node to a cut node, in one of the two
possible orientations.
-/
theorem exists_block_cut_of_adj
    {m n : BlockCutNode G}
    (hmn : (blockCutIncidence G).Adj m n) :
    (∃ (B : GraphBlock G)
        (c : {v : V // IsCutVertex G v}),
      m = .inl B ∧ n = .inr c) ∨
    (∃ (c : {v : V // IsCutVertex G v})
        (B : GraphBlock G),
      m = .inr c ∧ n = .inl B) := by
  cases m with
  | inl B =>
      cases n with
      | inl C =>
          exact False.elim
            (not_blockCutIncidence_adj_block_block G B C hmn)
      | inr c =>
          exact Or.inl ⟨B, c, rfl, rfl⟩
  | inr c =>
      cases n with
      | inl B =>
          exact Or.inr ⟨c, B, rfl, rfl⟩
      | inr d =>
          exact False.elim
            (not_blockCutIncidence_adj_cut_cut G c d hmn)

omit [Fintype V] in
/--
Consecutive vertices of any incidence walk alternate between block and
cut nodes.
-/
theorem walk_getVert_alternates
    {a b : BlockCutNode G}
    (p : (blockCutIncidence G).Walk a b)
    {i : ℕ} (hi : i < p.length) :
    (∃ (B : GraphBlock G)
        (c : {v : V // IsCutVertex G v}),
      p.getVert i = .inl B ∧
        p.getVert (i + 1) = .inr c) ∨
    (∃ (c : {v : V // IsCutVertex G v})
        (B : GraphBlock G),
      p.getVert i = .inr c ∧
        p.getVert (i + 1) = .inl B) :=
  exists_block_cut_of_adj
    (p.adj_getVert_succ hi)

end BlockCutIncidence

end DeanK5
