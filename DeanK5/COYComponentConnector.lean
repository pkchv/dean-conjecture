import DeanK5.Graph.Separation

/-!
# Component connectors for the COY core argument

COY Fact 3 joins a path inside a selected core to one fixed path through
the component containing the second root.  This file constructs that
outer path and records the support statement that makes the concatenation
formally simple.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace ComponentRegion

variable [DecidableEq V] {G : SimpleGraph V} {S Q : Finset V}

/-- A selected simple path in the induced graph on a component region. -/
noncomputable def pathInsideInduced
    (hQ : ComponentRegion G S Q)
    {a b : V} (ha : a ∈ Q) (hb : b ∈ Q) :
    SimplePath (G.induce (↑Q : Set V))
      (⟨a, ha⟩ : (↑Q : Set V))
      (⟨b, hb⟩ : (↑Q : Set V)) :=
  let existence :=
    hQ.connected.exists_isPath
      (⟨a, ha⟩ : (↑Q : Set V))
      (⟨b, hb⟩ : (↑Q : Set V))
  ⟨Classical.choose existence, Classical.choose_spec existence⟩

/-- A simple path inside the induced graph on a connected component region. -/
noncomputable def pathInside
    (hQ : ComponentRegion G S Q)
    {a b : V} (ha : a ∈ Q) (hb : b ∈ Q) :
    SimplePath G a b :=
  (hQ.pathInsideInduced ha hb).mapInjectiveHom
    (Embedding.induce (↑Q : Set V)).toHom
    Subtype.val_injective

/-- Every vertex of `pathInside` belongs to the component region. -/
theorem pathInside_support_subset
    (hQ : ComponentRegion G S Q)
    {a b z : V} (ha : a ∈ Q) (hb : b ∈ Q)
    (hz : z ∈ (hQ.pathInside ha hb).walk.support) :
    z ∈ Q := by
  have hzRange :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := hQ.pathInsideInduced ha hb)
      (f := (Embedding.induce (↑Q : Set V)).toHom)
      (hinj := Subtype.val_injective)
      (by simpa [pathInside] using hz)
  obtain ⟨w, rfl⟩ := hzRange
  exact w.2

/-- The initial boundary edge is disjoint from the rest of an internal path. -/
theorem ofAdj_pathInside_disjoint
    (hQ : ComponentRegion G S Q)
    {t a y : V}
    (ht : t ∈ S) (ha : a ∈ Q) (hy : y ∈ Q)
    (hta : G.Adj t a) :
    (SimplePath.ofAdj hta).walk.support.Disjoint
      (hQ.pathInside ha hy).walk.support.tail := by
  apply List.disjoint_left.mpr
  intro z hzEdge hzTail
  simp at hzEdge
  rcases hzEdge with hzt | hza
  · subst z
    have htQ : t ∈ Q :=
      hQ.pathInside_support_subset ha hy
        (List.mem_of_mem_tail hzTail)
    exact hQ.not_mem_separator htQ ht
  · subst z
    exact (hQ.pathInside ha hy).start_not_mem_tail hzTail

/--
Prepend one boundary edge to a path inside the component.  The separator
endpoint cannot reappear in the component, so the resulting walk is a
simple path.
-/
noncomputable def boundaryPath
    (hQ : ComponentRegion G S Q)
    {t a y : V}
    (ht : t ∈ S) (ha : a ∈ Q) (hy : y ∈ Q)
    (hta : G.Adj t a) :
    SimplePath G t y :=
  (SimplePath.ofAdj hta).appendDisjoint
    (hQ.pathInside ha hy)
    (hQ.ofAdj_pathInside_disjoint ht ha hy hta)

/-- The tail of a boundary path stays entirely inside the component. -/
theorem boundaryPath_tail_subset
    (hQ : ComponentRegion G S Q)
    {t a y z : V}
    (ht : t ∈ S) (ha : a ∈ Q) (hy : y ∈ Q)
    (hta : G.Adj t a)
    (hz : z ∈ (hQ.boundaryPath ht ha hy hta).walk.support.tail) :
    z ∈ Q := by
  have hzParts :
      z ∈ (SimplePath.ofAdj hta).walk.support.tail ∨
        z ∈ (hQ.pathInside ha hy).walk.support.tail := by
    exact
      (SimpleGraph.Walk.mem_tail_support_append_iff
        (SimplePath.ofAdj hta).walk
        (hQ.pathInside ha hy).walk).1
        (by simpa [boundaryPath, SimplePath.appendDisjoint] using hz)
  rcases hzParts with hzEdge | hzInside
  · have hza : z = a := by
      simpa using hzEdge
    exact hza ▸ ha
  · exact hQ.pathInside_support_subset ha hy
      (List.mem_of_mem_tail hzInside)

/--
In a connected ambient graph, every component of a one-vertex deletion
admits a path from the deleted vertex to any chosen vertex of the
component whose remaining support stays in that component.
-/
theorem exists_path_from_singleton_boundary
    [Fintype V]
    (hQ : ComponentRegion G {c} Q)
    (hconn : G.Connected)
    {y : V} (hy : y ∈ Q) :
    ∃ P : SimplePath G c y,
      ∀ z ∈ P.walk.support.tail, z ∈ Q := by
  obtain ⟨q, hqQ⟩ := hQ.nonempty
  obtain ⟨p⟩ := hconn.preconnected q c
  obtain ⟨a, haQ, -, s, hsS, -, has⟩ :=
    hQ.exists_boundary_edge_of_walk hqQ (by simp) p
  have hsc : s = c := by
    simpa using hsS
  subst s
  let P := hQ.boundaryPath (by simp) haQ hy has.symm
  refine ⟨P, ?_⟩
  intro z hz
  exact hQ.boundaryPath_tail_subset
    (by simp) haQ hy has.symm hz

/--
A path supported on the separator is disjoint from the component part of
a boundary path.  This is the exact simplicity certificate needed by the
one-outer-path form of COY Fact 1.
-/
theorem support_disjoint_boundaryPath_tail
    (hQ : ComponentRegion G S Q)
    {x t a y : V}
    (P : SimplePath G x t)
    (hP : ∀ z ∈ P.walk.support, z ∈ S)
    (ht : t ∈ S) (ha : a ∈ Q) (hy : y ∈ Q)
    (hta : G.Adj t a) :
    P.walk.support.Disjoint
      (hQ.boundaryPath ht ha hy hta).walk.support.tail := by
  apply List.disjoint_left.mpr
  intro z hzP hzOuter
  have hzS : z ∈ S := hP z hzP
  have hzQ : z ∈ Q :=
    hQ.boundaryPath_tail_subset ht ha hy hta hzOuter
  exact hQ.not_mem_separator hzQ hzS

end ComponentRegion

end DeanK5
