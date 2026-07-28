import DeanK5.Graph.Separation

/-!
# Cut vertices

This file packages the component-based notion of a cut vertex used by the
block decomposition.  The definition is the standard one even when the
ambient graph is disconnected: deleting the vertex separates two vertices
that were connected beforehand.  For a preconnected graph this is equivalent
to the deletion having two distinct connected components.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
A cut vertex in the standard, component-local sense: deleting `v` separates
two surviving vertices that were connected in the original graph.
-/
def IsCutVertex [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Prop :=
  ∃ (a b : V) (ha : a ≠ v) (hb : b ≠ v),
    G.Reachable a b ∧
      ¬(deleteVertices G {v}).Reachable
        ⟨a, by simpa using ha⟩
        ⟨b, by simpa using hb⟩

/-- The cut vertices of a finite graph. -/
noncomputable def cutVertices
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (IsCutVertex G)

@[simp] theorem mem_cutVertices_iff
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    v ∈ cutVertices G ↔ IsCutVertex G v := by
  classical
  simp [cutVertices]

@[simp] theorem not_mem_cutVertices_iff
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    v ∉ cutVertices G ↔ ¬IsCutVertex G v := by
  simp

/--
A graph is preconnected exactly when its connected-component type has at
most one element.
-/
theorem preconnected_iff_subsingleton_connectedComponent
    (G : SimpleGraph V) :
    G.Preconnected ↔ Subsingleton G.ConnectedComponent := by
  constructor
  · exact fun h => h.subsingleton_connectedComponent
  · intro h u v
    exact SimpleGraph.ConnectedComponent.exact
      (h.elim (G.connectedComponentMk u) (G.connectedComponentMk v))

/--
For a graph on a nonempty carrier, connectedness is equivalent to having
at most one connected component.
-/
theorem connected_iff_subsingleton_connectedComponent
    [Nonempty V] (G : SimpleGraph V) :
    G.Connected ↔ Subsingleton G.ConnectedComponent := by
  constructor
  · exact fun h => h.preconnected.subsingleton_connectedComponent
  · intro h
    exact {
      preconnected :=
        (preconnected_iff_subsingleton_connectedComponent G).2 h
    }

/--
In a preconnected graph, the standard cut-vertex predicate is equivalent to
the deletion having at least two connected components.
-/
theorem isCutVertex_iff_isVertexCut
    [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (hpreconnected : G.Preconnected) :
    IsCutVertex G v ↔ IsVertexCut G {v} := by
  constructor
  · rintro ⟨a, b, ha, hb, -, hnotReachable⟩
    let a' : {w : V // w ∉ ({v} : Finset V)} :=
      ⟨a, by simpa using ha⟩
    let b' : {w : V // w ∉ ({v} : Finset V)} :=
      ⟨b, by simpa using hb⟩
    refine ⟨(deleteVertices G {v}).connectedComponentMk a',
      (deleteVertices G {v}).connectedComponentMk b', ?_⟩
    intro hcomponents
    exact hnotReachable
      (SimpleGraph.ConnectedComponent.exact hcomponents)
  · rintro ⟨C, D, hCD⟩
    obtain ⟨a, haC⟩ := C.nonempty_supp
    obtain ⟨b, hbD⟩ := D.nonempty_supp
    have ha : a.1 ≠ v := by
      simpa using a.2
    have hb : b.1 ≠ v := by
      simpa using b.2
    refine ⟨a.1, b.1, ha, hb, hpreconnected a.1 b.1, ?_⟩
    intro hab
    have hcomponent :
        (deleteVertices G {v}).connectedComponentMk a =
          (deleteVertices G {v}).connectedComponentMk b :=
      SimpleGraph.ConnectedComponent.sound hab
    have hC :
        (deleteVertices G {v}).connectedComponentMk a = C :=
      haC
    have hD :
        (deleteVertices G {v}).connectedComponentMk b = D :=
      hbD
    exact hCD (hC.symm.trans (hcomponent.trans hD))

/--
In a preconnected graph, failure to be a cut vertex is exactly the assertion
that the deletion has at most one connected component.  This remains valid
when deleting the vertex leaves an empty carrier.
-/
theorem not_isCutVertex_iff_subsingleton_deleteComponents
    [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (hpreconnected : G.Preconnected) :
    ¬IsCutVertex G v ↔
      Subsingleton (deleteVertices G {v}).ConnectedComponent := by
  rw [isCutVertex_iff_isVertexCut G v hpreconnected]
  unfold IsVertexCut
  constructor
  · intro h
    constructor
    intro C D
    by_contra hCD
    exact h ⟨C, D, hCD⟩
  · rintro h ⟨C, D, hCD⟩
    exact hCD (h.elim C D)

/--
If at least one vertex survives the deletion, a vertex is not a cut vertex
exactly when the deletion is connected.
-/
theorem not_isCutVertex_iff_delete_connected
    [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (hconnected : G.Connected)
    (hsurvives : Nonempty {w : V // w ≠ v}) :
    ¬IsCutVertex G v ↔ (deleteVertices G {v}).Connected := by
  have hnonempty :
      Nonempty {w : V // w ∉ ({v} : Finset V)} := by
    obtain ⟨w, hw⟩ := hsurvives
    exact ⟨⟨w, by simpa using hw⟩⟩
  constructor
  · intro hnot
    exact {
      preconnected :=
        (preconnected_iff_subsingleton_connectedComponent
          (deleteVertices G {v})).2
            ((not_isCutVertex_iff_subsingleton_deleteComponents
              G v hconnected.preconnected).1 hnot)
      nonempty := hnonempty
    }
  · intro hdeleteConnected
    exact
      (not_isCutVertex_iff_subsingleton_deleteComponents
        G v hconnected.preconnected).2
        hdeleteConnected.preconnected.subsingleton_connectedComponent

/--
If at least one vertex survives the deletion, being a cut vertex is
equivalent to disconnectedness after deleting it.
-/
theorem isCutVertex_iff_delete_not_connected
    [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (hconnected : G.Connected)
    (hsurvives : Nonempty {w : V // w ≠ v}) :
    IsCutVertex G v ↔ ¬(deleteVertices G {v}).Connected := by
  constructor
  · intro hcut hdeleteConnected
    exact
      ((not_isCutVertex_iff_delete_connected
        G v hconnected hsurvives).2 hdeleteConnected) hcut
  · intro hnot
    by_contra hcut
    exact hnot
      ((not_isCutVertex_iff_delete_connected
        G v hconnected hsurvives).1 hcut)

/-- A graph has no cut vertex. -/
def HasNoCutVertex [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ v, ¬IsCutVertex G v

/-- A finite graph has no cut vertex exactly when its cut-vertex set is empty. -/
theorem hasNoCutVertex_iff_cutVertices_eq_empty
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    HasNoCutVertex G ↔ cutVertices G = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v
    simpa using h v
  · intro h v
    have hv : v ∉ cutVertices G := by
      rw [h]
      simp
    simpa using hv

/-- The graph induced by a carrier has no cut vertex of its own. -/
def CarrierHasNoCutVertex
    [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) : Prop :=
  HasNoCutVertex (G.induce (↑B : Set V))

end DeanK5
