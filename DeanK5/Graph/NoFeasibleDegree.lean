import DeanK5.Graph.BlockCutSides
import DeanK5.Graph.CycleBlocks

/-!
# Degree bounds when no feasible block exists

Assume that at most two vertices are marked and that no graph block is
feasible relative to those vertices.  Two distinct neighbors of a vertex
cannot lie in the same component after that vertex is deleted: a path
between them avoiding the deleted vertex would close to a cycle, hence lie
in a block of order at least three, whereas the no-feasible-block argument
makes every block have order at most two.

Every deletion component contains a marked vertex.  Choosing one such
vertex for the component containing each neighbor therefore injects the
neighbor set into the marked vertices that survive the deletion.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace NoFeasibleDegree

variable [Fintype V]
  {G : SimpleGraph V}

/-- The finite set of neighbors, defined without a decidable adjacency
assumption in its public type. -/
private noncomputable def neighborVertices
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (G.neighborSet v).toFinset

@[simp]
private theorem mem_neighborVertices
    (G : SimpleGraph V) (v w : V) :
    w ∈ neighborVertices G v ↔ G.Adj v w := by
  classical
  simp [neighborVertices, SimpleGraph.mem_neighborSet]

@[simp]
private theorem card_neighborVertices
    (G : SimpleGraph V) (v : V) :
    (neighborVertices G v).card = finiteDegree G v := by
  classical
  simp [neighborVertices, finiteDegree,
    Set.ncard_eq_toFinset_card']

variable [DecidableEq V]

/-- A neighbor regarded as a surviving vertex after deleting its center. -/
private def deletedNeighbor
    (G : SimpleGraph V) (v : V)
    (w : ↑(neighborVertices G v)) :
    {x : V // x ∉ ({v} : Finset V)} :=
  ⟨w.1, by
    have hvw : G.Adj v w.1 :=
      (mem_neighborVertices G v w.1).1 w.2
    simpa using hvw.ne.symm⟩

/-- The component of `G - v` containing a specified neighbor of `v`. -/
private noncomputable def neighborDeletionComponent
    (G : SimpleGraph V) (v : V)
    (w : ↑(neighborVertices G v)) :
    (deleteVertices G {v}).ConnectedComponent :=
  (deleteVertices G {v}).connectedComponentMk
    (deletedNeighbor G v w)

/--
When every block has order at most two, distinct neighbors of `v` lie in
distinct components of `G - v`.
-/
private theorem neighborDeletionComponent_injective
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) :
    Function.Injective
      (neighborDeletionComponent G v) := by
  intro a b hab
  apply Subtype.ext
  by_contra habVertices
  have hreach :
      (deleteVertices G {v}).Reachable
        (deletedNeighbor G v a)
        (deletedNeighbor G v b) :=
    SimpleGraph.ConnectedComponent.exact hab
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  let inclusion :
      deleteVertices G {v} →g G :=
    (Embedding.induce
      {x : V | x ∉ ({v} : Finset V)}).toHom
  let P : SimplePath G a.1 b.1 := {
    walk := p.map inclusion
    isPath := hp.map (by
      intro x y hxy
      exact Subtype.ext hxy)
  }
  have hvAvoid : v ∉ P.walk.support := by
    intro hv
    change v ∈ (p.map inclusion).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨x, -, hx⟩ := List.mem_map.mp hv
    change x.1 = v at hx
    have hxv : x.1 ≠ v := by
      simpa using x.2
    exact hxv hx
  have hva : G.Adj v a.1 :=
    (mem_neighborVertices G v a.1).1 a.2
  have hvb : G.Adj v b.1 :=
    (mem_neighborVertices G v b.1).1 b.2
  obtain ⟨B, -, -, -, hBthree⟩ :=
    GraphBlock.exists_containing_center_and_path_ends
      habVertices hva hvb P hvAvoid
  have hBtwo :
      B.carrier.card ≤ 2 :=
    graphBlock_card_le_two_of_no_feasibleBlock
      hconnected marked hmarked hnoFeasible B
  omega

/--
A marked vertex chosen from the deletion component containing a neighbor.
-/
private noncomputable def neighborMarkedVertex
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) (w : ↑(neighborVertices G v)) : V :=
  Classical.choose
    (deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible v
      (neighborDeletionComponent G v w))

/-- The selected component label is marked. -/
private theorem neighborMarkedVertex_mem_marked
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) (w : ↑(neighborVertices G v)) :
    neighborMarkedVertex
      hconnected marked hnoFeasible v w ∈ marked :=
  (Classical.choose_spec
    (deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible v
      (neighborDeletionComponent G v w))).1

/-- The selected label lies in the neighbor's deletion component. -/
private theorem neighborMarkedVertex_mem_component
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) (w : ↑(neighborVertices G v)) :
    neighborMarkedVertex
        hconnected marked hnoFeasible v w ∈
      componentVertices G {v}
        (neighborDeletionComponent G v w) :=
  (Classical.choose_spec
    (deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible v
      (neighborDeletionComponent G v w))).2

/-- A selected deletion-component label is different from the deleted
center. -/
private theorem neighborMarkedVertex_ne_center
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) (w : ↑(neighborVertices G v)) :
    neighborMarkedVertex
      hconnected marked hnoFeasible v w ≠ v := by
  have hmem :=
    neighborMarkedVertex_mem_component
      hconnected marked hnoFeasible v w
  obtain ⟨hnotDeleted, -⟩ :=
    (mem_componentVertices_iff
      G {v} (neighborDeletionComponent G v w)
      (neighborMarkedVertex
        hconnected marked hnoFeasible v w)).1 hmem
  simpa using hnotDeleted

/--
Distinct neighbors receive distinct marked labels from their deletion
components.
-/
private theorem neighborMarkedVertex_injective
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) :
    Function.Injective
      (neighborMarkedVertex
        hconnected marked hnoFeasible v) := by
  intro a b hab
  apply neighborDeletionComponent_injective
    hconnected marked hmarked hnoFeasible v
  by_contra hcomponents
  have hdisjoint :=
    componentVertices_disjoint_of_ne
      G {v} hcomponents
  have ha :=
    neighborMarkedVertex_mem_component
      hconnected marked hnoFeasible v a
  have hb :=
    neighborMarkedVertex_mem_component
      hconnected marked hnoFeasible v b
  apply Finset.disjoint_left.mp hdisjoint ha
  rw [hab]
  exact hb

/--
The neighbors of any vertex inject into the marked vertices that survive
deletion of that vertex.
-/
private theorem card_neighborVertices_le_card_erase
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) :
    (neighborVertices G v).card ≤
      (marked.erase v).card := by
  let f :
      ↑(neighborVertices G v) →
        ↑(marked.erase v) :=
    fun w =>
      ⟨neighborMarkedVertex
          hconnected marked hnoFeasible v w,
        Finset.mem_erase.mpr ⟨
          neighborMarkedVertex_ne_center
            hconnected marked hnoFeasible v w,
          neighborMarkedVertex_mem_marked
            hconnected marked hnoFeasible v w⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply neighborMarkedVertex_injective
      hconnected marked hmarked hnoFeasible v
    exact congrArg Subtype.val hab
  exact Finset.card_le_card_of_injective hf

end NoFeasibleDegree

/--
If at most two vertices are marked and no feasible block exists, then the
degree of `v` is bounded by the number of marked vertices other than `v`.
-/
theorem finiteDegree_le_card_erase_of_no_feasibleBlock
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) :
    finiteDegree G v ≤ (marked.erase v).card := by
  rw [← NoFeasibleDegree.card_neighborVertices G v]
  exact
    NoFeasibleDegree.card_neighborVertices_le_card_erase
      hconnected marked hmarked hnoFeasible v

/-- Under the same hypotheses, every finite degree is at most the number of
marked vertices. -/
theorem finiteDegree_le_card_marked_of_no_feasibleBlock
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) :
    finiteDegree G v ≤ marked.card :=
  (finiteDegree_le_card_erase_of_no_feasibleBlock
    hconnected marked hmarked hnoFeasible v).trans
      Finset.card_erase_le

/-- In particular, every finite degree is at most two. -/
theorem finiteDegree_le_two_of_no_feasibleBlock
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (v : V) :
    finiteDegree G v ≤ 2 :=
  (finiteDegree_le_card_marked_of_no_feasibleBlock
    hconnected marked hmarked hnoFeasible v).trans
      hmarked

/--
A vertex of degree at least three forces a feasible block whenever at most
two vertices are marked.
-/
theorem exists_feasibleBlock_of_three_le_finiteDegree
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (v : V)
    (hdegree : 3 ≤ finiteDegree G v) :
    ∃ B : GraphBlock G,
      IsFeasibleBlock G marked B := by
  by_contra hno
  push Not at hno
  have hdegreeUpper :
      finiteDegree G v ≤ 2 :=
    finiteDegree_le_two_of_no_feasibleBlock
      hconnected marked hmarked hno v
  omega

/-- Mathlib's maximum degree is at most two under the no-feasible-block
hypothesis. -/
theorem maxDegree_le_two_of_no_feasibleBlock
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B) :
    G.maxDegree ≤ 2 := by
  apply G.maxDegree_le_of_forall_degree_le
  intro v
  have hdegree :
      G.degree v = finiteDegree G v := by
    unfold finiteDegree
    rw [← G.card_neighborSet_eq_degree]
    exact Set.fintypeCard_eq_ncard (G.neighborSet v)
  rw [hdegree]
  exact
    finiteDegree_le_two_of_no_feasibleBlock
      hconnected marked hmarked hnoFeasible v

end DeanK5
