import DeanK5.Graph.FeasibleBlocks

/-!
# Cut vertices with two protected vertices

Suppose that a finite connected graph has two distinct protected vertices
and no block is feasible relative to them.  Every component left after
deleting a cut vertex must contain a protected vertex.  Since neither
protected vertex is itself a cut vertex, the deleted vertex is different
from both of them, and its deletion has exactly two components: one
containing each protected vertex.

This file packages precisely that consequence for the block argument in
COY Claim 3.11.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace ProtectedCutPair

/--
The hypotheses for the two-protected-vertex consequence of the
no-feasible-block argument.
-/
structure Context
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (y z : V) : Prop where
  connected : G.Connected
  distinct : y ≠ z
  noFeasible :
    ∀ B : GraphBlock G,
      ¬IsFeasibleBlock G {y, z} B

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {y z : V}

/-- Neither of the two protected vertices is a cut vertex. -/
theorem Context.marked_not_cut
    (C : Context G y z)
    {v : V} (hv : v ∈ ({y, z} : Finset V)) :
    ¬IsCutVertex G v := by
  apply
    not_isCutVertex_of_mem_marked_of_no_feasibleBlock
      C.connected ({y, z} : Finset V)
  · simp [C.distinct]
  · exact C.noFeasible
  · exact hv

/-- A cut vertex is different from both protected vertices. -/
theorem Context.cut_ne_marked
    (C : Context G y z)
    {c : V} (hcut : IsCutVertex G c) :
    c ≠ y ∧ c ≠ z := by
  constructor
  · intro hcy
    apply C.marked_not_cut (v := c)
    · simp [hcy]
    · exact hcut
  · intro hcz
    apply C.marked_not_cut (v := c)
    · simp [hcz]
    · exact hcut

/--
Every component after deleting a cut vertex contains exactly one of the
two protected vertices.
-/
theorem Context.deletionComponent_contains_exactly_one
    (C : Context G y z)
    {c : V} (hcut : IsCutVertex G c)
    (Q : (deleteVertices G {c}).ConnectedComponent) :
    (y ∈ componentVertices G {c} Q ∧
        z ∉ componentVertices G {c} Q) ∨
      (z ∈ componentVertices G {c} Q ∧
        y ∉ componentVertices G {c} Q) := by
  obtain ⟨r, hrMarked, hrQ⟩ :=
    deletionComponent_meets_protected_of_no_feasibleBlock
      C.connected ({y, z} : Finset V) C.noFeasible c Q
  have hr : r = y ∨ r = z := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      hrMarked
  have hvertexCut :
      IsVertexCut G {c} :=
    (isCutVertex_iff_isVertexCut
      G c C.connected.preconnected).1 hcut
  obtain ⟨R, hRQ⟩ :=
    hvertexCut.exists_other_component Q
  obtain ⟨s, hsMarked, hsR⟩ :=
    deletionComponent_meets_protected_of_no_feasibleBlock
      C.connected ({y, z} : Finset V) C.noFeasible c R
  have hs : s = y ∨ s = z := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      hsMarked
  have hdisjoint :
      Disjoint
        (componentVertices G {c} R)
        (componentVertices G {c} Q) :=
    componentVertices_disjoint_of_ne G {c} hRQ
  rcases hr with rfl | rfl
  · left
    refine ⟨hrQ, ?_⟩
    intro hzQ
    rcases hs with rfl | rfl
    · exact
        Finset.disjoint_left.mp hdisjoint
          hsR hrQ
    · exact
        Finset.disjoint_left.mp hdisjoint
          hsR hzQ
  · right
    refine ⟨hrQ, ?_⟩
    intro hyQ
    rcases hs with rfl | rfl
    · exact
        Finset.disjoint_left.mp hdisjoint
          hsR hyQ
    · exact
        Finset.disjoint_left.mp hdisjoint
          hsR hrQ

/--
Deleting a cut vertex leaves exactly two connected components.
-/
theorem Context.deleteComponents_card_eq_two
    (C : Context G y z)
    {c : V} (hcut : IsCutVertex G c) :
    Fintype.card
        (deleteVertices G {c}).ConnectedComponent =
      2 := by
  obtain ⟨hcy, hcz⟩ := C.cut_ne_marked hcut
  let yD : {v : V // v ∉ ({c} : Finset V)} :=
    ⟨y, by simpa using hcy.symm⟩
  let zD : {v : V // v ∉ ({c} : Finset V)} :=
    ⟨z, by simpa using hcz.symm⟩
  let Cy : (deleteVertices G {c}).ConnectedComponent :=
    (deleteVertices G {c}).connectedComponentMk yD
  let Cz : (deleteVertices G {c}).ConnectedComponent :=
    (deleteVertices G {c}).connectedComponentMk zD
  have hyCy :
      y ∈ componentVertices G {c} Cy := by
    apply (mem_componentVertices_iff G {c} Cy y).2
    refine ⟨yD.2, ?_⟩
    change
      (deleteVertices G {c}).connectedComponentMk yD =
        Cy
    rfl
  have hzCz :
      z ∈ componentVertices G {c} Cz := by
    apply (mem_componentVertices_iff G {c} Cz z).2
    refine ⟨zD.2, ?_⟩
    change
      (deleteVertices G {c}).connectedComponentMk zD =
        Cz
    rfl
  have hzNotCy :
      z ∉ componentVertices G {c} Cy := by
    rcases
        C.deletionComponent_contains_exactly_one
          hcut Cy with
      hcase | hcase
    · exact hcase.2
    · exact False.elim (hcase.2 hyCy)
  have hCyCz : Cy ≠ Cz := by
    intro heq
    apply hzNotCy
    simpa [heq] using hzCz
  have hexhaust :
      ∀ Q : (deleteVertices G {c}).ConnectedComponent,
        Q = Cy ∨ Q = Cz := by
    intro Q
    rcases
        C.deletionComponent_contains_exactly_one
          hcut Q with
      hcase | hcase
    · left
      have hcomponent :=
        ((mem_componentVertices_iff
          G {c} Q y).1 hcase.1).2
      change Cy = Q at hcomponent
      exact hcomponent.symm
    · right
      have hcomponent :=
        ((mem_componentVertices_iff
          G {c} Q z).1 hcase.1).2
      change Cz = Q at hcomponent
      exact hcomponent.symm
  have hpair :
      ({Cy, Cz} : Set
          (deleteVertices G {c}).ConnectedComponent) =
        Set.univ := by
    ext Q
    simp only [
      Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact hexhaust Q
  have hnat :
      Nat.card
          (deleteVertices G {c}).ConnectedComponent =
        2 := by
    apply Nat.card_eq_two_iff.mpr
    exact ⟨Cy, Cz, hCyCz, hpair⟩
  simpa only [Nat.card_eq_fintype_card] using hnat

/--
The two protected vertices are unreachable from one another after any cut
vertex is deleted.
-/
theorem Context.marked_unreachable_after_delete
    (C : Context G y z)
    {c : V} (hcut : IsCutVertex G c) :
    ¬(deleteVertices G {c}).Reachable
      ⟨y, by
        obtain ⟨hcy, -⟩ := C.cut_ne_marked hcut
        simpa using hcy.symm⟩
      ⟨z, by
        obtain ⟨-, hcz⟩ := C.cut_ne_marked hcut
        simpa using hcz.symm⟩ := by
  intro hreach
  let yD : {v : V // v ∉ ({c} : Finset V)} :=
    ⟨y, by
      obtain ⟨hcy, -⟩ := C.cut_ne_marked hcut
      simpa using hcy.symm⟩
  let Cy : (deleteVertices G {c}).ConnectedComponent :=
    (deleteVertices G {c}).connectedComponentMk yD
  have hyCy :
      y ∈ componentVertices G {c} Cy := by
    apply (mem_componentVertices_iff G {c} Cy y).2
    refine ⟨yD.2, ?_⟩
    change
      (deleteVertices G {c}).connectedComponentMk yD =
        Cy
    rfl
  have hzCy :
      z ∈ componentVertices G {c} Cy := by
    apply (mem_componentVertices_iff G {c} Cy z).2
    refine ⟨by
      obtain ⟨-, hcz⟩ := C.cut_ne_marked hcut
      simpa using hcz.symm, ?_⟩
    change
      (deleteVertices G {c}).connectedComponentMk
          ⟨z, _⟩ =
        Cy
    exact
      (SimpleGraph.ConnectedComponent.sound hreach).symm
  rcases
      C.deletionComponent_contains_exactly_one
        hcut Cy with
    hcase | hcase
  · exact hcase.2 hzCy
  · exact hcase.2 hyCy

end ProtectedCutPair

end DeanK5
