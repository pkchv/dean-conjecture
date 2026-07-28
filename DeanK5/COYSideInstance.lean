import DeanK5.COYProtectedEdge

/-!
# Induced sides for the COY cut-vertex induction

If `Q` is a component region of `G - c`, the recursive graph in COY
Claim 3.2 is the graph induced by `Q ∪ {c}`.  This file packages its
carrier, its two rooted vertices, the inclusion into `G`, and the
degree and complexity bookkeeping needed for the recursive call.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace CutSide

/-- One component side together with its cut vertex. -/
def vertices [DecidableEq V] (Q : Finset V) (c : V) : Finset V :=
  insert c Q

/-- The vertex type of one component side together with its cut vertex. -/
abbrev Vertex [DecidableEq V] (Q : Finset V) (c : V) :=
  (↑(vertices Q c) : Set V)

/-- The ambient graph induced by one component side and its cut vertex. -/
def graph [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (c : V) :
    SimpleGraph (Vertex Q c) :=
  G.induce (↑(vertices Q c) : Set V)

/-- A vertex of `Q`, regarded as a vertex of the induced side. -/
def innerVertex [DecidableEq V]
    (Q : Finset V) (c v : V) (hv : v ∈ Q) :
    Vertex Q c :=
  ⟨v, Finset.mem_insert_of_mem hv⟩

/-- The root lying in the chosen component side. -/
def root [DecidableEq V]
    (Q : Finset V) (c x : V) (hx : x ∈ Q) :
    Vertex Q c :=
  innerVertex Q c x hx

/-- The cut vertex, regarded as the second root of the induced side. -/
def cut [DecidableEq V]
    (Q : Finset V) (c : V) :
    Vertex Q c :=
  ⟨c, Finset.mem_insert_self c Q⟩

/-- Forgetting the subtype embeds the induced side in the ambient graph. -/
def embedding [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (c : V) :
    graph G Q c ↪g G :=
  SimpleGraph.Embedding.induce (↑(vertices Q c) : Set V)

@[simp] theorem innerVertex_val [DecidableEq V]
    (Q : Finset V) (c v : V) (hv : v ∈ Q) :
    (innerVertex Q c v hv : V) = v :=
  rfl

@[simp] theorem root_val [DecidableEq V]
    (Q : Finset V) (c x : V) (hx : x ∈ Q) :
    (root Q c x hx : V) = x :=
  rfl

@[simp] theorem cut_val [DecidableEq V]
    (Q : Finset V) (c : V) :
    (cut Q c : V) = c :=
  rfl

@[simp] theorem embedding_apply [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (c : V)
    (v : Vertex Q c) :
    embedding G Q c v = v.1 :=
  rfl

/-- A component vertex and the cut root are distinct. -/
theorem root_ne_cut
    [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} {c x : V}
    (hQ : ComponentRegion G {c} Q)
    (hx : x ∈ Q) :
    root Q c x hx ≠ cut Q c := by
  intro h
  have hxc : x = c :=
    congrArg Subtype.val h
  exact hQ.not_mem_separator hx (by simp [hxc])

/-- Every non-cut vertex of the side carrier belongs to its component. -/
theorem mem_component_of_ne_cut
    [DecidableEq V]
    {Q : Finset V} {c : V}
    (v : Vertex Q c)
    (hv : v ≠ cut Q c) :
    v.1 ∈ Q := by
  have hvMember : v.1 ∈ insert c Q := by
    exact v.2
  have hvClass : v.1 = c ∨ v.1 ∈ Q :=
    Finset.mem_insert.mp hvMember
  rcases hvClass with hvc | hvQ
  · exfalso
    apply hv
    apply Subtype.ext
    exact hvc
  · exact hvQ

/--
Every ambient neighbor of a component vertex survives in the induced
side, so its finite degree is preserved exactly.
-/
theorem finiteDegree_graph_inner_eq
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} {c v : V}
    (hQ : ComponentRegion G {c} Q)
    (hv : v ∈ Q) :
    finiteDegree (graph G Q c) (innerVertex Q c v hv) =
      finiteDegree G v := by
  let U : Set V := ↑(vertices Q c)
  let vU : U := innerVertex Q c v hv
  let N : Set V := G.neighborSet v
  let NI : Set U := (G.induce U).neighborSet vU
  have hinside :
      ∀ w, G.Adj v w → w ∈ U := by
    intro w hvw
    by_cases hwc : w = c
    · simp [U, vertices, hwc]
    · have hwQ : w ∈ Q :=
        hQ.closed hv hvw (by simpa using hwc)
      simp [U, vertices, hwQ]
  have himage : Subtype.val '' NI = N := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hw
      exact ⟨⟨w, hinside w hw⟩, hw, rfl⟩
  unfold finiteDegree
  change NI.ncard = N.ncard
  rw [← himage,
    Set.ncard_image_of_injective _ Subtype.val_injective]

/-- The exact degree-preservation statement for an arbitrary non-cut side vertex. -/
theorem finiteDegree_graph_eq_of_ne_cut
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} {c : V}
    (hQ : ComponentRegion G {c} Q)
    (v : Vertex Q c)
    (hv : v ≠ cut Q c) :
    finiteDegree (graph G Q c) v =
      finiteDegree G v.1 := by
  have hvQ := mem_component_of_ne_cut v hv
  have hveq : v = innerVertex Q c v.1 hvQ := by
    apply Subtype.ext
    rfl
  rw [hveq]
  exact finiteDegree_graph_inner_eq hQ hvQ

/--
The side carrier is strictly smaller than the ambient carrier whenever
there is a nonempty disjoint component region on the other side of `c`.
-/
theorem card_lt_of_disjoint_component
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q R : Finset V} {c : V}
    (hR : ComponentRegion G {c} R)
    (hQR : Disjoint Q R) :
    Fintype.card (Vertex Q c) < Fintype.card V := by
  obtain ⟨w, hwR⟩ := hR.nonempty
  apply Fintype.card_subtype_lt
  intro hwSide
  have hwcOrQ : w = c ∨ w ∈ Q := by
    simpa [vertices] using hwSide
  rcases hwcOrQ with rfl | hwQ
  · exact hR.not_mem_separator hwR (by simp)
  · exact Finset.disjoint_left.mp hQR hwQ hwR

/-- Omitting one named ambient vertex makes the side carrier strictly smaller. -/
theorem card_lt_of_not_mem
    [Fintype V] [DecidableEq V]
    {Q : Finset V} {c z : V}
    (hz : z ∉ vertices Q c) :
    Fintype.card (Vertex Q c) < Fintype.card V :=
  Fintype.card_subtype_lt hz

/-- The induced side has no more edges than its ambient graph. -/
theorem edgeSet_ncard_le
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (c : V) :
    (graph G Q c).edgeSet.ncard ≤ G.edgeSet.ncard := by
  let e := embedding G Q c
  have hsubset :
      Sym2.map e '' (graph G Q c).edgeSet ⊆ G.edgeSet :=
    e.toHom.image_edgeSet_subset
  calc
    (graph G Q c).edgeSet.ncard =
        (Sym2.map e '' (graph G Q c).edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective e.injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/--
The induced side has strictly smaller COY complexity whenever a disjoint
component region survives on the other side of the cut.
-/
theorem rootedComplexity_lt_of_disjoint_component
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q R : Finset V} {c : V}
    (hR : ComponentRegion G {c} R)
    (hQR : Disjoint Q R) :
    rootedComplexity (graph G Q c) < rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    (card_lt_of_disjoint_component hR hQR)
    (edgeSet_ncard_le G Q c)

end CutSide

end COY

end DeanK5
