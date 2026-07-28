import DeanK5.COYSingletonExterior
import DeanK5.COYCoreAttachment
import DeanK5.COYCoreAttachmentNatural
import DeanK5.COYCoreModification
import DeanK5.Contraction

/-!
# Other components beside a singleton COY exterior

This file formalizes COY Claim 3.6.  The proof keeps the source contraction
explicit: all vertices of the core side `T`, except one retained attachment,
are represented by one new root.  The resulting graph is proved rooted
2-connected, its degree loss is counted vertex by vertex, its smaller
complexity is certified, and every recursively obtained path is lifted before
the final use of COY Fact 1.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

/--
A surjective vertex map that sends every edge either to an equality or to
an edge sends a connected graph to a connected graph.  This is the walk
version of quotient connectivity, with equal consecutive images suppressed.
-/
private theorem connected_of_surjective_mapOrContract
    {A B : Type*} [DecidableEq B]
    {H : SimpleGraph A} {K : SimpleGraph B}
    (hH : H.Connected)
    (f : A → B) (hsurj : Function.Surjective f)
    (hedge : ∀ ⦃u v⦄, H.Adj u v →
      f u = f v ∨ K.Adj (f u) (f v)) :
    K.Connected := by
  rw [connected_iff_exists_forall_reachable] at hH ⊢
  obtain ⟨r, hr⟩ := hH
  refine ⟨f r, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := hsurj w
  obtain ⟨p⟩ := hr v
  exact ⟨p.mapOrContract f hedge⟩

namespace PreferredOrientationData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
The vertex set of a deletion component different from the component
containing the second root.
-/
private noncomputable def otherDeletionRegion
    (D : PreferredOrientationData G x y z)
    (K :
      (deleteVertices G D.chosen.rooted.core.carrier).ConnectedComponent) :
    Finset V :=
  componentVertices G D.chosen.rooted.core.carrier K

/-- The named deletion component is a component region. -/
private theorem otherDeletionRegion_componentRegion
    (D : PreferredOrientationData G x y z)
    (K :
      (deleteVertices G D.chosen.rooted.core.carrier).ConnectedComponent) :
    ComponentRegion G D.chosen.rooted.core.carrier
      (D.otherDeletionRegion K) := by
  exact componentRegion_componentVertices
    G D.chosen.rooted.core.carrier K

/--
A component different from the singleton component containing `y` does not
contain `y`.
-/
private theorem other_root_not_mem_otherDeletionRegion
    (D : PreferredOrientationData G x y z)
    (K :
      (deleteVertices G D.chosen.rooted.core.carrier).ConnectedComponent)
    (hK : K ≠ D.chosen.rooted.otherComponent) :
    y ∉ D.otherDeletionRegion K := by
  intro hyK
  exact Finset.disjoint_left.mp
    (componentVertices_disjoint_of_ne
      G D.chosen.rooted.core.carrier hK)
    hyK D.chosen.rooted.other_root_mem_otherRegion

/--
Under the negation of the Claim 3.6 conclusion, every core endpoint of an
edge leaving the selected component belongs to `T`.  The root is excluded
by Claim 3.5, and an endpoint in `S` is precisely the forbidden conclusion.
-/
private theorem boundary_mem_T_of_no_S_attachment
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype :
      D.chosen.rooted.core.typeNumber = 1 ∨
        D.chosen.rooted.core.typeNumber = 3)
    (K :
      (deleteVertices G D.chosen.rooted.core.carrier).ConnectedComponent)
    (hnoS :
      ¬∃ d ∈ D.otherDeletionRegion K,
        ∃ s ∈ D.chosen.rooted.core.S, G.Adj s d)
    {d a : V}
    (hd : d ∈ D.otherDeletionRegion K)
    (hda : G.Adj d a)
    (ha : a ∈ D.chosen.rooted.core.carrier) :
    a ∈ D.chosen.rooted.core.T := by
  have hneRoot : a ≠ x := by
    intro hax
    subst a
    have hneighbors :=
      D.neighborSets_eq_T_of_natural_singleton
        M hnot hregion htype
    have hdT : d ∈ D.chosen.rooted.core.T := by
      have hdx : d ∈ G.neighborSet x := by
        simpa [SimpleGraph.mem_neighborSet] using hda.symm
      rw [hneighbors.1, hneighbors.2] at hdx
      exact hdx
    exact
      (D.otherDeletionRegion_componentRegion K).not_mem_separator
        hd (D.chosen.rooted.core.T_subset_carrier hdT)
  rcases
      D.chosen.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
        ha hneRoot with haS | haT
  · exact False.elim
      (hnoS ⟨d, hd, a, haS, hda.symm⟩)
  · exact haT

/--
If the desired `S`-attachment is absent, 2-connectivity supplies two
distinct `T`-attachments.  The first will be retained and the second
guarantees that the collapsed root is represented nontrivially.
-/
private theorem exists_two_T_attachments_of_no_S_attachment
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype :
      D.chosen.rooted.core.typeNumber = 1 ∨
        D.chosen.rooted.core.typeNumber = 3)
    (K :
      (deleteVertices G D.chosen.rooted.core.carrier).ConnectedComponent)
    (hnoS :
      ¬∃ d ∈ D.otherDeletionRegion K,
        ∃ s ∈ D.chosen.rooted.core.S, G.Adj s d) :
    ∃ d₀ ∈ D.otherDeletionRegion K,
      ∃ t₀ ∈ D.chosen.rooted.core.T,
        G.Adj t₀ d₀ ∧
        ∃ d₁ ∈ D.otherDeletionRegion K,
          ∃ t₁ ∈ D.chosen.rooted.core.T,
            t₁ ≠ t₀ ∧ G.Adj t₁ d₁ := by
  let C := D.chosen.rooted.core
  let Q := D.otherDeletionRegion K
  have hQ : ComponentRegion G C.carrier Q :=
    D.otherDeletionRegion_componentRegion K
  obtain ⟨d₀, hd₀, t₀, ht₀Carrier, ht₀x, ht₀d₀⟩ :=
    C.exists_nonroot_attachment
      hQ M.underlying_two_connected
  have ht₀T : t₀ ∈ C.T :=
    D.boundary_mem_T_of_no_S_attachment
      M hnot hregion htype K hnoS hd₀ ht₀d₀.symm
        ht₀Carrier
  obtain ⟨d₁, hd₁, t₁, ht₁Carrier, ht₁t₀, hd₁t₁⟩ :=
    hQ.exists_attachment_avoiding_boundary_vertex
      M.underlying_two_connected
      (C.T_subset_carrier ht₀T)
      C.root_mem_carrier
      (by
        intro h
        exact ht₀x h)
  have ht₁T : t₁ ∈ C.T :=
    D.boundary_mem_T_of_no_S_attachment
      M hnot hregion htype K hnoS hd₁ hd₁t₁
        ht₁Carrier
  exact ⟨d₀, hd₀, t₀, ht₀T, ht₀d₀,
    d₁, hd₁, t₁, ht₁T, ht₁t₀, hd₁t₁.symm⟩

end PreferredOrientationData

/-! ## The source contraction -/

/--
Vertices of the compressed component.  `none` is the collapsed boundary
root, `some none` is the retained attachment, and `some (some d)` is the
unchanged component vertex `d`.
-/
abbrev BoundaryCompressionVertex
    [DecidableEq V] (Q : Finset V) :=
  Option (Option (↥Q))

namespace BoundaryCompression

variable [DecidableEq V]
  {G : SimpleGraph V} {Q T : Finset V} {t : V}

/-- The root representing all boundary vertices except `t`. -/
def collapsedRoot : BoundaryCompressionVertex Q := none

/-- The root retaining the selected boundary vertex `t`. -/
def retainedRoot : BoundaryCompressionVertex Q := some none

/-- A component vertex in the compressed carrier. -/
def inner (d : ↥Q) : BoundaryCompressionVertex Q :=
  some (some d)

/-- The vertices used before taking the quotient image. -/
abbrev sourceVertices (Q T : Finset V) :=
  {v : V // v ∈ Q ∪ T}

/--
Collapse `T \ {t}` to one root, retain `t`, and retain every vertex of
`Q`.  The disjointness premise used later makes these three cases exclusive.
-/
def collapse (Q : Finset V) (t : V) :
    V → BoundaryCompressionVertex Q :=
  fun v =>
    if hvQ : v ∈ Q then
      inner ⟨v, hvQ⟩
    else if v = t then retainedRoot else collapsedRoot

/-- The collapse map on the induced source graph `G[Q ∪ T]`. -/
def collapseSource (Q T : Finset V) (t : V) :
    sourceVertices Q T → BoundaryCompressionVertex Q :=
  fun v => collapse Q t v.1

/--
The graph obtained from `G[Q ∪ T]` by identifying all vertices of
`T \ {t}`.  `SimpleGraph.map` suppresses the loops and parallel edges
created by the identification.
-/
def graph (G : SimpleGraph V) (Q T : Finset V) (t : V) :
    SimpleGraph (BoundaryCompressionVertex Q) :=
  (G.induce (↑(Q ∪ T) : Set V)).map
    (collapseSource Q T t)

/-- The graph used in the rooted-connectivity hypothesis. -/
def rootedGraph (G : SimpleGraph V) (Q T : Finset V) (t : V) :
    SimpleGraph (BoundaryCompressionVertex Q) :=
  graph G Q T t ⊔
    edge (collapsedRoot :
      BoundaryCompressionVertex Q) retainedRoot

@[simp] theorem collapse_of_mem_component
    (Q : Finset V) (t : V) {v : V} (hv : v ∈ Q) :
    collapse Q t v = inner ⟨v, hv⟩ := by
  simp [collapse, hv]

@[simp] theorem collapse_retained
    (Q : Finset V) (t : V) (htQ : t ∉ Q) :
    collapse Q t t = retainedRoot := by
  simp [collapse, htQ]

@[simp] theorem collapse_of_boundary_ne
    (Q : Finset V) (t : V) {v : V}
    (hvQ : v ∉ Q) (hvt : v ≠ t) :
    collapse Q t v = collapsedRoot := by
  simp [collapse, hvQ, hvt]

/-- The collapsed and retained roots are distinct. -/
theorem roots_ne :
    (collapsedRoot :
      BoundaryCompressionVertex Q) ≠ retainedRoot := by
  simp [collapsedRoot, retainedRoot]

/-- A component vertex is different from the collapsed root. -/
theorem inner_ne_collapsed (d : ↥Q) :
    inner d ≠ (collapsedRoot :
      BoundaryCompressionVertex Q) := by
  simp [inner, collapsedRoot]

/-- A component vertex is different from the retained root. -/
theorem inner_ne_retained (d : ↥Q) :
    inner d ≠ (retainedRoot :
      BoundaryCompressionVertex Q) := by
  simp [inner, retainedRoot]

/-- Distinct component vertices remain distinct under compression. -/
theorem inner_injective :
    Function.Injective
      (inner :
        ↥Q → BoundaryCompressionVertex Q) := by
  intro a b h
  exact Option.some.inj (Option.some.inj h)

/-- The compressed carrier has exactly `|Q| + 2` vertices. -/
theorem card_vertex [Fintype V] :
    Fintype.card (BoundaryCompressionVertex Q) = Q.card + 2 := by
  simp [BoundaryCompressionVertex]

/--
Away from the collapsed root, the quotient has a canonical ambient
representative.
-/
def uncollapseRetained (t : V) :
    {w : BoundaryCompressionVertex Q //
      w ≠ collapsedRoot} → V
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some none, _⟩ => t
  | ⟨some (some d), _⟩ => d.1

/--
The canonical representative of a noncollapsed vertex lies in `Q ∪ T`
when `t ∈ T`.
-/
theorem uncollapseRetained_mem
    (ht : t ∈ T)
    (w : {w : BoundaryCompressionVertex Q //
      w ≠ collapsedRoot}) :
    uncollapseRetained t w ∈ Q ∪ T := by
  cases w with
  | mk w hw =>
      cases w with
      | none => exact False.elim (hw rfl)
      | some w =>
          cases w with
          | none => simp [uncollapseRetained, ht]
          | some d => simp [uncollapseRetained, d.2]

/--
Collapsing the canonical representative recovers every noncollapsed
vertex.
-/
theorem collapse_uncollapseRetained
    (hQT : Disjoint Q T)
    (ht : t ∈ T)
    (w : {w : BoundaryCompressionVertex Q //
      w ≠ collapsedRoot}) :
    collapse Q t (uncollapseRetained t w) = w.1 := by
  cases w with
  | mk w hw =>
      cases w with
      | none => exact False.elim (hw rfl)
      | some w =>
          cases w with
          | none =>
              have htQ : t ∉ Q :=
                Finset.disjoint_right.mp hQT ht
              simp [uncollapseRetained, collapse, htQ,
                retainedRoot]
          | some d =>
              simp [uncollapseRetained, collapse, d.2, inner]

/-- A noncollapsed quotient image has its canonical unique source vertex. -/
theorem eq_uncollapseRetained_of_collapse_eq
    (w : {w : BoundaryCompressionVertex Q //
      w ≠ collapsedRoot})
    {v : V}
    (h : collapse Q t v = w.1) :
    v = uncollapseRetained t w := by
  cases w with
  | mk w hw =>
      cases w with
      | none => exact False.elim (hw rfl)
      | some w =>
          cases w with
          | none =>
              by_cases hvQ : v ∈ Q
              · simp [collapse, hvQ, inner] at h
              · by_cases hvt : v = t
                · exact hvt
                · simp [collapse, hvQ, hvt,
                    collapsedRoot] at h
          | some d =>
              by_cases hvQ : v ∈ Q
              · have hvd : v = d.1 := by
                  simpa [collapse, hvQ, inner,
                    Subtype.ext_iff] using h
                simpa [uncollapseRetained] using hvd
              · by_cases hvt : v = t
                · subst v
                  simp [collapse, hvQ,
                    retainedRoot] at h
                · simp [collapse, hvQ, hvt,
                    collapsedRoot] at h

/-- Canonical representatives of noncollapsed vertices are distinct. -/
theorem uncollapseRetained_injective
    (hQT : Disjoint Q T) (ht : t ∈ T) :
    Function.Injective
      (uncollapseRetained t :
        {w : BoundaryCompressionVertex Q //
          w ≠ collapsedRoot} → V) := by
  intro a b hab
  apply Subtype.ext
  have hcollapse :=
    congrArg (collapse Q t) hab
  rw [collapse_uncollapseRetained hQT ht a,
    collapse_uncollapseRetained hQT ht b] at hcollapse
  exact hcollapse

/--
After deleting the collapsed root, every compression edge is an ambient
edge between the canonical retained representatives.
-/
def retainedHom
    (G : SimpleGraph V) (Q T : Finset V) (t : V) :
    (graph G Q T t).induce
        {w | w ≠ (collapsedRoot :
          BoundaryCompressionVertex Q)} →g G where
  toFun w := uncollapseRetained t w
  map_rel' := by
    intro a b hab
    change (graph G Q T t).Adj a.1 b.1 at hab
    change
      ((G.induce (↑(Q ∪ T) : Set V)).map
        (collapseSource Q T t)).Adj a.1 b.1 at hab
    rcases hab with ⟨-, u, v, huv, hua, hvb⟩
    have hu :
        u.1 = uncollapseRetained t a :=
      eq_uncollapseRetained_of_collapse_eq
        a (by simpa [collapseSource] using hua)
    have hv :
        v.1 = uncollapseRetained t b :=
      eq_uncollapseRetained_of_collapse_eq
        b (by simpa [collapseSource] using hvb)
    simpa [hu, hv] using huv

/-- The retained-part homomorphism is injective. -/
theorem retainedHom_injective
    (hQT : Disjoint Q T) (ht : t ∈ T) :
    Function.Injective (retainedHom G Q T t) :=
  uncollapseRetained_injective hQT ht

/-- The collapsed root has precisely the expected source preimages. -/
theorem collapse_eq_collapsed_iff
    (Q : Finset V) (t v : V) :
    collapse Q t v = collapsedRoot ↔
      v ∉ Q ∧ v ≠ t := by
  by_cases hvQ : v ∈ Q
  · simp [collapse, hvQ, inner, collapsedRoot]
  · by_cases hvt : v = t
    · subst v
      simp [collapse, hvQ, retainedRoot, collapsedRoot]
    · simp [collapse, hvQ, hvt, collapsedRoot]

/-- The retained root has the unique source preimage `t`. -/
theorem collapse_eq_retained_iff
    (hQT : Disjoint Q T) (ht : t ∈ T) (v : V) :
    collapse Q t v = retainedRoot ↔ v = t := by
  constructor
  · intro h
    by_cases hvQ : v ∈ Q
    · simp [collapse, hvQ, inner, retainedRoot] at h
    · by_cases hvt : v = t
      · exact hvt
      · simp [collapse, hvQ, hvt,
          collapsedRoot, retainedRoot] at h
  · rintro rfl
    simp [collapse,
      Finset.disjoint_right.mp hQT ht,
      retainedRoot]

/-- Each component vertex has a unique source preimage. -/
theorem collapse_eq_inner_iff
    (Q : Finset V) (t : V) (d : ↥Q) (v : V) :
    collapse Q t v = inner d ↔ v = d.1 := by
  constructor
  · intro h
    by_cases hvQ : v ∈ Q
    · simp [collapse, hvQ, inner, Subtype.ext_iff] at h
      exact h
    · by_cases hvt : v = t
      · have htQ : t ∉ Q := by
          simpa [hvt] using hvQ
        subst v
        simp [collapse, htQ, inner,
          retainedRoot] at h
      · simp [collapse, hvQ, hvt, inner,
          collapsedRoot] at h
  · rintro rfl
    simp [collapse, d.2, inner]

/--
An ambient edge whose endpoints both lie in `Q ∪ T` maps to a compression
edge whenever its endpoint images are distinct.
-/
theorem graph_adj_of_adj
    {u v : V} (hu : u ∈ Q ∪ T) (hv : v ∈ Q ∪ T)
    (huv : G.Adj u v)
    (hne : collapse Q t u ≠ collapse Q t v) :
    (graph G Q T t).Adj
      (collapse Q t u) (collapse Q t v) := by
  let uU : sourceVertices Q T := ⟨u, hu⟩
  let vU : sourceVertices Q T := ⟨v, hv⟩
  have huvU :
      (G.induce (↑(Q ∪ T) : Set V)).Adj uU vU :=
    huv
  exact SimpleGraph.map_adj_apply'
    (G := G.induce (↑(Q ∪ T) : Set V))
    (f := collapseSource Q T t) huvU
    (by simpa [collapseSource, uU, vU] using hne)

/--
Mapping a finite simple graph along an arbitrary vertex map cannot increase
its number of edges.  Loops may disappear and parallel source edges may be
identified.
-/
private theorem edgeSet_map_ncard_le
    {A B : Type*} [Fintype A] [Fintype B]
    (H : SimpleGraph A) (f : A → B) :
    (H.map f).edgeSet.ncard ≤ H.edgeSet.ncard := by
  have hsubset :
      (H.map f).edgeSet ⊆
        Sym2.map f '' H.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        rcases he with ⟨-, u, v, huv, hua, hvb⟩
        refine ⟨s(u, v), huv, ?_⟩
        simp [hua, hvb]
  calc
    (H.map f).edgeSet.ncard
        ≤ (Sym2.map f '' H.edgeSet).ncard :=
      Set.ncard_le_ncard hsubset
    _ ≤ H.edgeSet.ncard :=
      Set.ncard_image_le H.edgeSet.toFinite

/-- The induced source graph has no more edges than the ambient graph. -/
private theorem induce_union_edgeSet_ncard_le
    [Fintype V]
    (G : SimpleGraph V) (Q T : Finset V) :
    (G.induce (↑(Q ∪ T) : Set V)).edgeSet.ncard ≤
      G.edgeSet.ncard := by
  let e :
      G.induce (↑(Q ∪ T) : Set V) ↪g G :=
    Embedding.induce (↑(Q ∪ T) : Set V)
  have hsubset :
      Sym2.map e ''
          (G.induce (↑(Q ∪ T) : Set V)).edgeSet ⊆
        G.edgeSet :=
    e.toHom.image_edgeSet_subset
  calc
    (G.induce (↑(Q ∪ T) : Set V)).edgeSet.ncard =
        (Sym2.map e ''
          (G.induce (↑(Q ∪ T) : Set V)).edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective e.injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/-- The boundary compression has no more edges than its ambient graph. -/
theorem graph_edgeSet_ncard_le
    [Fintype V]
    (G : SimpleGraph V) (Q T : Finset V) (t : V) :
    (graph G Q T t).edgeSet.ncard ≤ G.edgeSet.ncard := by
  exact
    (edgeSet_map_ncard_le
      (G.induce (↑(Q ∪ T) : Set V))
      (collapseSource Q T t)).trans
      (induce_union_edgeSet_ncard_le G Q T)

/--
The compression carrier is strictly smaller whenever `Q` is disjoint from
an ambient set of at least three vertices.  In Claim 3.6 that set is the
core carrier.
-/
theorem card_vertex_lt
    [Fintype V]
    {C : Finset V}
    (hQC : Disjoint Q C) (hC : 3 ≤ C.card) :
    Fintype.card (BoundaryCompressionVertex Q) <
      Fintype.card V := by
  have hunion :
      (Q ∪ C).card ≤ (Finset.univ : Finset V).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hQC,
    Finset.card_univ] at hunion
  rw [card_vertex]
  omega

/-- The boundary compression is strictly smaller in the COY measure. -/
theorem rootedComplexity_lt
    [Fintype V]
    {C : Finset V}
    (hQC : Disjoint Q C) (hC : 3 ≤ C.card) :
    COY.rootedComplexity (graph G Q T t) <
      COY.rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    (card_vertex_lt hQC hC)
    (graph_edgeSet_ncard_le G Q T t)

/-- The ambient collapse is onto when a second boundary vertex survives. -/
theorem collapse_surjective
    (hQT : Disjoint Q T)
    (ht : t ∈ T)
    {t' : V} (ht'T : t' ∈ T) (ht't : t' ≠ t) :
    Function.Surjective (collapse Q t) := by
  intro w
  cases w with
  | none =>
      refine ⟨t', ?_⟩
      exact collapse_of_boundary_ne Q t
        (Finset.disjoint_right.mp hQT ht'T) ht't
  | some w =>
      cases w with
      | none =>
          refine ⟨t, ?_⟩
          exact collapse_retained Q t
            (Finset.disjoint_right.mp hQT ht)
      | some d =>
          refine ⟨d.1, ?_⟩
          exact collapse_of_mem_component Q t d.2

/--
An ambient edge maps either to an equality or to an edge of the rooted
compression.  Edges leaving `Q` use the certified boundary containment in
`T`; edges wholly outside `Q` collapse, except for the retained/collapsed
root pair, which is the artificial rooted edge.
-/
theorem ambient_edge_maps
    [Fintype V]
    {S : Finset V}
    (hQ : ComponentRegion G S Q)
    (hboundary :
      ∀ {d a : V}, d ∈ Q → G.Adj d a →
        a ∈ S → a ∈ T)
    {u v : V} (huv : G.Adj u v) :
    collapse Q t u = collapse Q t v ∨
      (graph G Q T t ⊔
        edge (collapsedRoot :
          BoundaryCompressionVertex Q) retainedRoot).Adj
        (collapse Q t u) (collapse Q t v) := by
  let H := graph G Q T t
  have map_edge_of_mem
      {a b : V} (ha : a ∈ Q ∪ T) (hb : b ∈ Q ∪ T)
      (hab : G.Adj a b) :
      collapse Q t a = collapse Q t b ∨
        H.Adj (collapse Q t a) (collapse Q t b) := by
    by_cases heq :
        collapse Q t a = collapse Q t b
    · exact Or.inl heq
    · right
      let aU : sourceVertices Q T := ⟨a, ha⟩
      let bU : sourceVertices Q T := ⟨b, hb⟩
      have habU :
          (G.induce (↑(Q ∪ T) : Set V)).Adj aU bU :=
        hab
      exact SimpleGraph.map_adj_apply' habU
        (by simpa [collapseSource, aU, bU] using heq)
  by_cases huQ : u ∈ Q
  · have huU : u ∈ Q ∪ T :=
      Finset.mem_union_left T huQ
    by_cases hvQ : v ∈ Q
    · rcases map_edge_of_mem huU
          (Finset.mem_union_left T hvQ) huv with
        heq | hadj
      · exact Or.inl heq
      · exact Or.inr (Or.inl hadj)
    · have hvS : v ∈ S := by
        by_contra hvnotS
        exact hvQ (hQ.closed huQ huv hvnotS)
      have hvT : v ∈ T :=
        hboundary huQ huv hvS
      rcases map_edge_of_mem huU
          (Finset.mem_union_right Q hvT) huv with
        heq | hadj
      · exact Or.inl heq
      · exact Or.inr (Or.inl hadj)
  · by_cases hvQ : v ∈ Q
    · have huS : u ∈ S := by
        by_contra hunotS
        exact huQ (hQ.closed hvQ huv.symm hunotS)
      have huT : u ∈ T :=
        hboundary hvQ huv.symm huS
      rcases map_edge_of_mem
          (Finset.mem_union_right Q huT)
          (Finset.mem_union_left T hvQ) huv with
        heq | hadj
      · exact Or.inl heq
      · exact Or.inr (Or.inl hadj)
    · by_cases hut : u = t
      · subst u
        have hvt : v ≠ t := by
          intro h
          subst v
          exact G.loopless.irrefl t huv
        right
        have htQ : t ∉ Q := by
          intro htQ
          exact huQ htQ
        rw [collapse_retained Q t htQ,
          collapse_of_boundary_ne Q t hvQ hvt]
        exact Or.inr (by
          simp [SimpleGraph.edge_adj, roots_ne.symm])
      · by_cases hvt : v = t
        · subst v
          right
          have htQ : t ∉ Q := by
            intro htQ
            exact hvQ htQ
          rw [collapse_of_boundary_ne Q t huQ hut,
            collapse_retained Q t htQ]
          exact Or.inr (by
            simp [SimpleGraph.edge_adj, roots_ne])
        · left
          rw [collapse_of_boundary_ne Q t huQ hut,
            collapse_of_boundary_ne Q t hvQ hvt]

/-- The rooted boundary compression is connected. -/
theorem rooted_graph_connected
    [Fintype V]
    {S : Finset V}
    (hQ : ComponentRegion G S Q)
    (hboundary :
      ∀ {d a : V}, d ∈ Q → G.Adj d a →
        a ∈ S → a ∈ T)
    (ht : t ∈ T)
    {t' : V} (ht'T : t' ∈ T) (ht't : t' ≠ t)
    (hQT : Disjoint Q T)
    (hconn : G.Connected) :
    (rootedGraph G Q T t).Connected := by
  apply connected_of_surjective_mapOrContract
    hconn (collapse Q t)
    (collapse_surjective hQT ht ht'T ht't)
  intro u v huv
  exact ambient_edge_maps hQ hboundary huv

/--
Deleting the collapsed root leaves the connected component `Q` together
with the retained attachment `t`.
-/
theorem connected_delete_collapsed
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hQT : Disjoint Q T)
    (ht : t ∈ T)
    {d₀ : V} (hd₀ : d₀ ∈ Q)
    (htd₀ : G.Adj t d₀) :
    ((rootedGraph G Q T t).induce
      {w | w ≠ (collapsedRoot :
        BoundaryCompressionVertex Q)}).Connected := by
  let R := rootedGraph G Q T t
  let W :=
    {w : BoundaryCompressionVertex Q //
      w ≠ (collapsedRoot :
        BoundaryCompressionVertex Q)}
  let d₀Q : ↥Q := ⟨d₀, hd₀⟩
  let d₀W : W :=
    ⟨inner d₀Q, inner_ne_collapsed d₀Q⟩
  let f : G.induce (↑Q : Set V) →g R.induce
      {w | w ≠ (collapsedRoot :
        BoundaryCompressionVertex Q)} := {
    toFun := fun d =>
      ⟨inner ⟨d.1, d.2⟩,
        inner_ne_collapsed ⟨d.1, d.2⟩⟩
    map_rel' := by
      intro a b hab
      apply Or.inl
      have hne :
          collapse Q t a.1 ≠ collapse Q t b.1 := by
        intro h
        apply hab.ne
        apply Subtype.ext
        have hinner :
            inner (⟨a.1, a.2⟩ : ↥Q) =
              inner (⟨b.1, b.2⟩ : ↥Q) := by
          simpa [collapse_of_mem_component Q t a.2,
            collapse_of_mem_component Q t b.2] using h
        exact congrArg Subtype.val
          (inner_injective hinner)
      have hadj := graph_adj_of_adj
        (Finset.mem_union_left T a.2)
        (Finset.mem_union_left T b.2) hab hne
      rw [collapse_of_mem_component Q t a.2,
        collapse_of_mem_component Q t b.2] at hadj
      exact hadj
  }
  have hd₀t :
      R.Adj (inner d₀Q) retainedRoot := by
    apply Or.inl
    let dU : sourceVertices Q T :=
      ⟨d₀, Finset.mem_union_left T hd₀⟩
    let tU : sourceVertices Q T :=
      ⟨t, Finset.mem_union_right Q ht⟩
    have htQ : t ∉ Q :=
      Finset.disjoint_right.mp hQT ht
    have hne :
        collapseSource Q T t dU ≠
          collapseSource Q T t tU := by
      simpa [collapseSource, dU, tU,
        collapse_of_mem_component Q t hd₀,
        collapse_retained Q t htQ] using
        (inner_ne_retained d₀Q)
    have hadj := graph_adj_of_adj
      (Finset.mem_union_left T hd₀)
      (Finset.mem_union_right Q ht)
      htd₀.symm
      (by simpa [collapseSource, dU, tU] using hne)
    rw [collapse_of_mem_component Q t hd₀,
      collapse_retained Q t htQ] at hadj
    exact hadj
  rw [connected_iff_exists_forall_reachable]
  refine ⟨d₀W, ?_⟩
  rintro ⟨w, hw⟩
  cases w with
  | none => exact False.elim (hw rfl)
  | some w =>
      cases w with
      | none =>
          exact
            (show
              (R.induce
                {w | w ≠ (collapsedRoot :
                  BoundaryCompressionVertex Q)}).Reachable
                d₀W ⟨retainedRoot, roots_ne.symm⟩ from
              (show
                (R.induce
                  {w | w ≠ (collapsedRoot :
                    BoundaryCompressionVertex Q)}).Adj
                  d₀W ⟨retainedRoot, roots_ne.symm⟩
                from hd₀t).reachable)
      | some d =>
          let dQ : (↑Q : Set V) :=
            ⟨d.1, d.2⟩
          let d₀Q' : (↑Q : Set V) :=
            ⟨d₀, hd₀⟩
          have hreach :=
            (hQ.connected.preconnected d₀Q' dQ).map f
          convert hreach using 1 <;>
            apply Subtype.ext <;> rfl

/--
Deleting the retained root leaves `Q` together with the collapsed root,
which is attached through any second boundary vertex.
-/
theorem connected_delete_retained
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hQT : Disjoint Q T)
    {d₁ t₁ : V} (hd₁ : d₁ ∈ Q)
    (ht₁ : t₁ ∈ T) (ht₁t : t₁ ≠ t)
    (ht₁d₁ : G.Adj t₁ d₁) :
    ((rootedGraph G Q T t).induce
      {w | w ≠ (retainedRoot :
        BoundaryCompressionVertex Q)}).Connected := by
  let R := rootedGraph G Q T t
  let W :=
    {w : BoundaryCompressionVertex Q //
      w ≠ (retainedRoot :
        BoundaryCompressionVertex Q)}
  let d₁Q : ↥Q := ⟨d₁, hd₁⟩
  let d₁W : W :=
    ⟨inner d₁Q, inner_ne_retained d₁Q⟩
  let f : G.induce (↑Q : Set V) →g R.induce
      {w | w ≠ (retainedRoot :
        BoundaryCompressionVertex Q)} := {
    toFun := fun d =>
      ⟨inner ⟨d.1, d.2⟩,
        inner_ne_retained ⟨d.1, d.2⟩⟩
    map_rel' := by
      intro a b hab
      apply Or.inl
      have hne :
          collapse Q t a.1 ≠ collapse Q t b.1 := by
        intro h
        apply hab.ne
        apply Subtype.ext
        have hinner :
            inner (⟨a.1, a.2⟩ : ↥Q) =
              inner (⟨b.1, b.2⟩ : ↥Q) := by
          simpa [collapse_of_mem_component Q t a.2,
            collapse_of_mem_component Q t b.2] using h
        exact congrArg Subtype.val
          (inner_injective hinner)
      have hadj := graph_adj_of_adj
        (Finset.mem_union_left T a.2)
        (Finset.mem_union_left T b.2) hab hne
      rw [collapse_of_mem_component Q t a.2,
        collapse_of_mem_component Q t b.2] at hadj
      exact hadj
  }
  have hd₁c :
      R.Adj (inner d₁Q) collapsedRoot := by
    apply Or.inl
    let dU : sourceVertices Q T :=
      ⟨d₁, Finset.mem_union_left T hd₁⟩
    let tU : sourceVertices Q T :=
      ⟨t₁, Finset.mem_union_right Q ht₁⟩
    have ht₁Q : t₁ ∉ Q :=
      Finset.disjoint_right.mp hQT ht₁
    have hne :
        collapseSource Q T t dU ≠
          collapseSource Q T t tU := by
      simpa [collapseSource, dU, tU,
        collapse_of_mem_component Q t hd₁,
        collapse_of_boundary_ne Q t ht₁Q ht₁t] using
        (inner_ne_collapsed d₁Q)
    have hadj := graph_adj_of_adj
      (Finset.mem_union_left T hd₁)
      (Finset.mem_union_right Q ht₁)
      ht₁d₁.symm
      (by simpa [collapseSource, dU, tU] using hne)
    rw [collapse_of_mem_component Q t hd₁,
      collapse_of_boundary_ne Q t ht₁Q ht₁t] at hadj
    exact hadj
  rw [connected_iff_exists_forall_reachable]
  refine ⟨d₁W, ?_⟩
  rintro ⟨w, hw⟩
  cases w with
  | none =>
      exact
        (show
          (R.induce
            {w | w ≠ (retainedRoot :
              BoundaryCompressionVertex Q)}).Reachable
            d₁W ⟨collapsedRoot, roots_ne⟩ from
          (show
            (R.induce
              {w | w ≠ (retainedRoot :
                BoundaryCompressionVertex Q)}).Adj
              d₁W ⟨collapsedRoot, roots_ne⟩
            from hd₁c).reachable)
  | some w =>
      cases w with
      | none => exact False.elim (hw rfl)
      | some d =>
          let dQ : (↑Q : Set V) :=
            ⟨d.1, d.2⟩
          let d₁Q' : (↑Q : Set V) :=
            ⟨d₁, hd₁⟩
          have hreach :=
            (hQ.connected.preconnected d₁Q' dQ).map f
          convert hreach using 1 <;>
            apply Subtype.ext <;> rfl

/--
Deleting an unchanged component vertex is handled by deleting the same
ambient vertex and mapping the resulting connected graph through the
compression.  No other ambient vertex maps to that component vertex.
-/
theorem connected_delete_inner
    [Fintype V]
    {S : Finset V}
    (hQ : ComponentRegion G S Q)
    (hboundary :
      ∀ {d a : V}, d ∈ Q → G.Adj d a →
        a ∈ S → a ∈ T)
    (hQT : Disjoint Q T)
    (ht : t ∈ T)
    {t' : V} (ht'T : t' ∈ T) (ht't : t' ≠ t)
    (hconn : IsKConnected G 2)
    (d : ↥Q) :
    ((rootedGraph G Q T t).induce
      {w | w ≠ inner d}).Connected := by
  let A := G.induce {v : V | v ∉ ({d.1} : Finset V)}
  let R := rootedGraph G Q T t
  let B := R.induce {w | w ≠ inner d}
  have hA : A.Connected :=
    hconn.2 ({d.1} : Finset V) (by simp)
  let f :
      {v : V // v ∉ ({d.1} : Finset V)} →
        {w : BoundaryCompressionVertex Q // w ≠ inner d} :=
    fun v =>
    ⟨collapse Q t v.1, by
      intro h
      have hvd :
          v.1 = d.1 :=
        (collapse_eq_inner_iff Q t d v.1).1 h
      exact v.2 (by simp [hvd])⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    cases w with
    | none =>
        have ht'Q : t' ∉ Q :=
          Finset.disjoint_right.mp hQT ht'T
        have ht'd : t' ≠ d.1 := by
          intro h
          apply ht'Q
          exact h ▸ d.2
        let v : {v : V // v ∉ ({d.1} : Finset V)} :=
          ⟨t', by simp [ht'd]⟩
        refine ⟨v, ?_⟩
        apply Subtype.ext
        exact collapse_of_boundary_ne Q t ht'Q ht't
    | some w =>
        cases w with
        | none =>
            have htQ : t ∉ Q :=
              Finset.disjoint_right.mp hQT ht
            have htd : t ≠ d.1 := by
              intro h
              apply htQ
              exact h ▸ d.2
            let v :
                {v : V // v ∉ ({d.1} : Finset V)} :=
              ⟨t, by simp [htd]⟩
            refine ⟨v, ?_⟩
            apply Subtype.ext
            exact collapse_retained Q t htQ
        | some e =>
            have hed : e ≠ d := by
              intro h
              subst e
              exact hw rfl
            have heval : e.1 ≠ d.1 := by
              intro h
              exact hed (Subtype.ext h)
            let v :
                {v : V // v ∉ ({d.1} : Finset V)} :=
              ⟨e.1, by simp [heval]⟩
            refine ⟨v, ?_⟩
            apply Subtype.ext
            exact collapse_of_mem_component Q t e.2
  have hedge :
      ∀ ⦃u v : {v : V // v ∉ ({d.1} : Finset V)}⦄,
        A.Adj u v →
          f u = f v ∨ B.Adj (f u) (f v) := by
    intro u v huv
    rcases ambient_edge_maps hQ hboundary huv with
      heq | hadj
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr hadj
  exact connected_of_surjective_mapOrContract
    hA f hsurj hedge

/--
The rooted boundary compression is 2-connected.  The proof treats deletion
of each of its three kinds of vertices separately.
-/
theorem rooted_graph_two_connected
    [Fintype V]
    {S : Finset V}
    (hQ : ComponentRegion G S Q)
    (hboundary :
      ∀ {d a : V}, d ∈ Q → G.Adj d a →
        a ∈ S → a ∈ T)
    (hQT : Disjoint Q T)
    (ht : t ∈ T)
    {d₀ d₁ t₁ : V}
    (hd₀ : d₀ ∈ Q) (htd₀ : G.Adj t d₀)
    (hd₁ : d₁ ∈ Q) (ht₁ : t₁ ∈ T)
    (ht₁t : t₁ ≠ t) (ht₁d₁ : G.Adj t₁ d₁)
    (hconn : IsKConnected G 2) :
    IsTwoConnected (rootedGraph G Q T t) := by
  apply isTwoConnected_of_connected_delete_one
  · rw [card_vertex]
    have hQpos := Finset.card_pos.mpr hQ.nonempty
    omega
  · exact rooted_graph_connected
      hQ hboundary ht ht₁ ht₁t hQT
      (by
        have hdeleted :=
          hconn.2 (∅ : Finset V) (by simp)
        have hset :
            {v : V | v ∉ (∅ : Finset V)} =
              Set.univ := by
          ext v
          simp
        rw [hset] at hdeleted
        exact (G.induceUnivIso.connected_iff).1
          hdeleted)
  · intro w
    cases w with
    | none =>
        exact connected_delete_collapsed
          hQ hQT ht hd₀ htd₀
    | some w =>
        cases w with
        | none =>
            exact connected_delete_retained
              hQ hQT hd₁ ht₁ ht₁t ht₁d₁
        | some d =>
            exact connected_delete_inner
              hQ hboundary hQT ht ht₁ ht₁t
              hconn d

/-! ## Lifting paths out of the compression -/

/--
Data obtained by lifting one path from the collapsed root to the retained
root.  The endpoint is an explicit vertex of `T \ {t}`, and the support
statement records that the lifted path meets `T` exactly at its two ends.
-/
structure PathLift
    (G : SimpleGraph V) (Q T : Finset V) (t : V)
    (P : SimplePath (graph G Q T t)
      (collapsedRoot : BoundaryCompressionVertex Q) retainedRoot) where
  /-- The boundary vertex represented by the first quotient edge. -/
  endpoint : V
  /-- The boundary endpoint survives deletion of `t`. -/
  endpoint_mem : endpoint ∈ T.erase t
  /-- The lifted simple path in the ambient graph. -/
  path : SimplePath G endpoint t
  /-- Replacing the collapsed root preserves the path length. -/
  length_eq : path.length = P.length
  /-- Every lifted vertex is the new endpoint, the retained endpoint, or is in `Q`. -/
  support_class :
    ∀ v ∈ path.walk.support,
      v = endpoint ∨ v = t ∨ v ∈ Q
  /-- Equivalently, the lifted path meets `T` exactly at its two endpoints. -/
  support_meets_T :
    ∀ v ∈ path.walk.support, v ∈ T →
      v = endpoint ∨ v = t

/--
Every quotient path has a source-faithful simple lift.  Only its first edge
needs a chosen preimage; after that edge all quotient vertices have unique
ambient representatives.
-/
theorem exists_pathLift
    [Fintype V]
    (hQT : Disjoint Q T) (ht : t ∈ T)
    (P : SimplePath (graph G Q T t)
      (collapsedRoot : BoundaryCompressionVertex Q) retainedRoot) :
    Nonempty (PathLift G Q T t P) := by
  let H := graph G Q T t
  obtain ⟨a, hca, tail, hwalk⟩ :=
    P.walk.exists_eq_cons_of_ne
      (roots_ne :
        (collapsedRoot :
          BoundaryCompressionVertex Q) ≠ retainedRoot)
  have hconsPath :
      (SimpleGraph.Walk.cons hca tail).IsPath := by
    have h := P.isPath
    rw [hwalk] at h
    exact h
  have htailPath : tail.IsPath :=
    hconsPath.of_cons
  have hcTail :
      (collapsedRoot :
        BoundaryCompressionVertex Q) ∉ tail.support :=
    (SimpleGraph.Walk.cons_isPath_iff hca tail).1
      hconsPath |>.2
  have haCollapsed :
      a ≠ (collapsedRoot :
        BoundaryCompressionVertex Q) := by
    intro h
    subst a
    exact H.loopless.irrefl collapsedRoot hca
  let U : Set (BoundaryCompressionVertex Q) :=
    {w | w ≠ (collapsedRoot :
      BoundaryCompressionVertex Q)}
  have htailAvoid :
      ∀ w ∈ tail.support,
        w ∈ U := by
    intro w hw h
    exact hcTail (h ▸ hw)
  let tailI :=
    tail.induce U htailAvoid
  let aI :
      U :=
    ⟨a, haCollapsed⟩
  let tI :
      U :=
    ⟨retainedRoot, roots_ne.symm⟩
  let tailPath :
      SimplePath
        ((graph G Q T t).induce U)
        aI tI := {
    walk := tailI
    isPath := by
      apply SimpleGraph.Walk.IsPath.of_map
        (f := (Embedding.induce U).toHom)
      rw [SimpleGraph.Walk.map_induce]
      exact htailPath
  }
  let hom := retainedHom G Q T t
  let ambientTail :=
    tailPath.mapInjectiveHom hom
      (retainedHom_injective hQT ht)
  have hambientEnd :
      hom tI = t := by
    rfl
  let ambientTail' :=
    ambientTail.castEnd hambientEnd
  have hcaMap :
      ((G.induce (↑(Q ∪ T) : Set V)).map
        (collapseSource Q T t)).Adj
        collapsedRoot a := by
    exact hca
  obtain ⟨-, bU, aU, hba, hbCollapse, haCollapse⟩ :=
    hcaMap
  have hbNotQ : bU.1 ∉ Q :=
    (collapse_eq_collapsed_iff Q t bU.1).1
      (by simpa [collapseSource] using hbCollapse) |>.1
  have hbNeT : bU.1 ≠ t :=
    (collapse_eq_collapsed_iff Q t bU.1).1
      (by simpa [collapseSource] using hbCollapse) |>.2
  have hbT : bU.1 ∈ T := by
    rcases Finset.mem_union.mp bU.2 with hbQ | hbT
    · exact False.elim (hbNotQ hbQ)
    · exact hbT
  have haEq :
      aU.1 = uncollapseRetained t aI :=
    eq_uncollapseRetained_of_collapse_eq
      aI (by simpa [collapseSource, aI] using haCollapse)
  have hbaAmbient :
      G.Adj bU.1 (hom aI) := by
    have hhom :
        hom aI = uncollapseRetained t aI := by
      rfl
    rw [hhom]
    simpa [haEq] using hba
  have htailSupport :
      ∀ v ∈ ambientTail'.walk.support,
        v = t ∨ v ∈ Q := by
    intro v hv
    have hv' :
        v ∈ ambientTail.walk.support := by
      simpa only [ambientTail',
        SimplePath.castEnd_support] using hv
    change v ∈ (tailPath.walk.map hom).support at hv'
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨w, hw, hwv⟩ := List.mem_map.mp hv'
    rcases w with ⟨w, hwNot⟩
    cases w with
    | none => exact False.elim (hwNot rfl)
    | some w =>
        cases w with
        | none =>
            left
            simpa [hom, retainedHom,
              uncollapseRetained] using hwv.symm
        | some d =>
            right
            have hvd : v = d.1 := by
              simpa [hom, retainedHom,
                uncollapseRetained] using hwv.symm
            subst v
            exact d.2
  have hbNotTail :
      bU.1 ∉ ambientTail'.walk.support := by
    intro hb
    rcases htailSupport bU.1 hb with hbt | hbQ
    · exact hbNeT hbt
    · exact hbNotQ hbQ
  let lifted : SimplePath G bU.1 t := {
    walk := .cons hbaAmbient ambientTail'.walk
    isPath := ambientTail'.isPath.cons hbNotTail
  }
  refine ⟨{
    endpoint := bU.1
    endpoint_mem := Finset.mem_erase.mpr
      ⟨hbNeT, hbT⟩
    path := lifted
    length_eq := ?_
    support_class := ?_
    support_meets_T := ?_
  }⟩
  ·
    have htailILen :
        tailI.length = tail.length := by
      have h := congrArg SimpleGraph.Walk.length
        (SimpleGraph.Walk.map_induce tail htailAvoid)
      rw [SimpleGraph.Walk.length_map] at h
      exact h
    have htailLength :
        ambientTail'.length = tail.length := by
      calc
        ambientTail'.length = ambientTail.length := by
          simp [ambientTail']
        _ = tailPath.length := by
          simp [ambientTail]
        _ = tailI.length := rfl
        _ = tail.length := htailILen
    have hP :
        P.length = tail.length + 1 := by
      change P.walk.length = tail.length + 1
      rw [hwalk]
      simp
    have hlift :
        lifted.length =
          ambientTail'.length + 1 := by
      simp [lifted, SimplePath.length, Nat.add_comm]
    omega
  · intro v hv
    have hv' :
        v = bU.1 ∨
          v ∈ ambientTail'.walk.support := by
      simpa [lifted] using hv
    rcases hv' with rfl | hvTail
    · exact Or.inl rfl
    · rcases htailSupport v hvTail with rfl | hvQ
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr hvQ)
  · intro v hv hvT
    have hvClass :
        v = bU.1 ∨ v = t ∨ v ∈ Q := by
      have hv' :
          v = bU.1 ∨
            v ∈ ambientTail'.walk.support := by
        simpa [lifted] using hv
      rcases hv' with rfl | hvTail
      · exact Or.inl rfl
      · rcases htailSupport v hvTail with rfl | hvQ
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hvQ)
    rcases hvClass with h | h | hvQ
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim
        (Finset.disjoint_left.mp hQT hvQ hvT)

/-! ## Degree bookkeeping in the compression -/

/--
Any collection of neighbors on which the collapse map is injective gives
the same number of distinct neighbors of the corresponding inner vertex.
This isolates the only finite-cardinality argument used in the degree
ledger below.
-/
private theorem selected_neighbors_card_le_compressed_degree
    [Fintype V]
    {d : V} (hd : d ∈ Q)
    (hall :
      ∀ {v : V}, G.Adj d v → v ∈ Q ∪ T)
    (A : Finset V)
    (hAN : ∀ ⦃v : V⦄, v ∈ A → G.Adj d v)
    (hinj :
      Set.InjOn (collapse Q t) (↑A : Set V)) :
    A.card ≤
      finiteDegree (graph G Q T t) (inner ⟨d, hd⟩) := by
  let f := collapse Q t
  have himage :
      f '' (↑A : Set V) ⊆
        (graph G Q T t).neighborSet (inner ⟨d, hd⟩) := by
    rintro w ⟨v, hvA, rfl⟩
    have hvN : G.Adj d v :=
      hAN (by simpa using hvA)
    have hvUnion : v ∈ Q ∪ T :=
      hall hvN
    have hdUnion : d ∈ Q ∪ T :=
      Finset.mem_union_left T hd
    have hcollapseD :
        collapse Q t d = inner ⟨d, hd⟩ :=
      collapse_of_mem_component Q t hd
    have hne :
        collapse Q t d ≠ collapse Q t v := by
      intro h
      have hdv :
          d = v :=
        ((collapse_eq_inner_iff Q t ⟨d, hd⟩ v).1
          (h.symm.trans hcollapseD)).symm
      exact hvN.ne hdv
    have hadj :=
      graph_adj_of_adj hdUnion hvUnion hvN hne
    simpa [hcollapseD] using hadj
  unfold finiteDegree
  calc
    A.card = (↑A : Set V).ncard := by
      simp
    _ = (f '' (↑A : Set V)).ncard := by
      exact (hinj.ncard_image).symm
    _ ≤
        ((graph G Q T t).neighborSet
          (inner ⟨d, hd⟩)).ncard :=
      Set.ncard_le_ncard himage

/--
Retaining one boundary neighbor shows that identifying the remaining
boundary neighbors loses at most `r` degrees when their number is at most
`r+1`.
-/
theorem finiteDegree_le_compressed_add
    [Fintype V]
    (hQT : Disjoint Q T)
    {d : V} (hd : d ∈ Q)
    (hall :
      ∀ {v : V}, G.Adj d v → v ∈ Q ∪ T)
    (r : ℕ)
    (hboundaryDegree :
      (G.neighborSet d ∩ (↑T : Set V)).ncard ≤ r + 1) :
    finiteDegree G d ≤
      finiteDegree (graph G Q T t) (inner ⟨d, hd⟩) + r := by
  classical
  letI : Fintype (G.neighborSet d) :=
    Fintype.ofFinite _
  let N := G.neighborFinset d
  let NT := N ∩ T
  have hNTcard :
      NT.card =
        (G.neighborSet d ∩ (↑T : Set V)).ncard := by
    calc
      NT.card = (↑NT : Set V).ncard := by
        simp
      _ = (G.neighborSet d ∩ (↑T : Set V)).ncard := by
        congr 1
        ext v
        simp [NT, N]
  by_cases hNT : NT.Nonempty
  · let b := hNT.choose
    have hbNT : b ∈ NT := hNT.choose_spec
    let A := N \ (NT.erase b)
    have hAN : A ⊆ N :=
      Finset.sdiff_subset
    have hA_boundary_unique :
        ∀ {v : V}, v ∈ A → v ∈ T → v = b := by
      intro v hvA hvT
      have hvN : v ∈ N := hAN hvA
      have hvNT : v ∈ NT := by
        exact Finset.mem_inter.mpr ⟨hvN, hvT⟩
      have hvNotErase : v ∉ NT.erase b := by
        exact (Finset.mem_sdiff.mp hvA).2
      by_contra hvb
      exact hvNotErase (Finset.mem_erase.mpr ⟨hvb, hvNT⟩)
    have hcollapseInjective :
        Set.InjOn (collapse Q t) (↑A : Set V) := by
      intro u huA v hvA huv
      have huN : u ∈ N :=
        hAN (by simpa using huA)
      have hvN : v ∈ N :=
        hAN (by simpa using hvA)
      have huAdj : G.Adj d u := by
        simpa [N] using huN
      have hvAdj : G.Adj d v := by
        simpa [N] using hvN
      have huClass := Finset.mem_union.mp (hall huAdj)
      have hvClass := Finset.mem_union.mp (hall hvAdj)
      rcases huClass with huQ | huT <;>
        rcases hvClass with hvQ | hvT
      · have hinner :
            inner (⟨u, huQ⟩ : ↥Q) =
              inner (⟨v, hvQ⟩ : ↥Q) := by
          simpa [collapse_of_mem_component Q t huQ,
            collapse_of_mem_component Q t hvQ] using huv
        exact congrArg Subtype.val
          (inner_injective hinner)
      · have huImage :
            collapse Q t u =
              inner (⟨u, huQ⟩ : ↥Q) :=
          collapse_of_mem_component Q t huQ
        have hvNotQ :
            v ∉ Q :=
          Finset.disjoint_right.mp hQT hvT
        by_cases hvt : v = t
        · subst v
          rw [huImage,
            collapse_retained Q t hvNotQ] at huv
          exact False.elim (inner_ne_retained ⟨u, huQ⟩ huv)
        · rw [huImage,
            collapse_of_boundary_ne Q t hvNotQ hvt] at huv
          exact False.elim (inner_ne_collapsed ⟨u, huQ⟩ huv)
      · have hvImage :
            collapse Q t v =
              inner (⟨v, hvQ⟩ : ↥Q) :=
          collapse_of_mem_component Q t hvQ
        have huNotQ :
            u ∉ Q :=
          Finset.disjoint_right.mp hQT huT
        by_cases hut : u = t
        · subst u
          rw [collapse_retained Q t huNotQ,
            hvImage] at huv
          exact False.elim
            (inner_ne_retained ⟨v, hvQ⟩ huv.symm)
        · rw [collapse_of_boundary_ne Q t huNotQ hut,
            hvImage] at huv
          exact False.elim
            (inner_ne_collapsed ⟨v, hvQ⟩ huv.symm)
      · have hub : u = b :=
          hA_boundary_unique
            (by simpa using huA) huT
        have hvb : v = b :=
          hA_boundary_unique
            (by simpa using hvA) hvT
        exact hub.trans hvb.symm
    have hselected :
        A.card ≤
          finiteDegree (graph G Q T t)
            (inner ⟨d, hd⟩) :=
      selected_neighbors_card_le_compressed_degree
        hd hall A
          (fun _ hv => by
            simpa [N] using hAN hv)
          hcollapseInjective
    have heraseSubset :
        NT.erase b ⊆ N :=
      (Finset.erase_subset b NT).trans
        (Finset.inter_subset_left)
    have hcardSplit :
        A.card + (NT.erase b).card = N.card := by
      exact Finset.card_sdiff_add_card_eq_card heraseSubset
    have heraseCard :
        (NT.erase b).card = NT.card - 1 :=
      Finset.card_erase_of_mem hbNT
    have hNcard :
        N.card = finiteDegree G d := by
      unfold finiteDegree
      calc
        N.card = (↑N : Set V).ncard := by
          simp
        _ = (G.neighborSet d).ncard := by
          congr 1
          ext v
          simp [N]
    rw [hNTcard] at heraseCard
    omega
  · have hNTEmpty : NT = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hNT
    have hcollapseInjective :
        Set.InjOn (collapse Q t) (↑N : Set V) := by
      intro u huN v hvN huv
      have huAdj : G.Adj d u := by
        simpa [N] using huN
      have hvAdj : G.Adj d v := by
        simpa [N] using hvN
      have huClass := Finset.mem_union.mp (hall huAdj)
      have hvClass := Finset.mem_union.mp (hall hvAdj)
      have huNotT : u ∉ T := by
        intro huT
        have : u ∈ NT := Finset.mem_inter.mpr
          ⟨by simpa using huN, huT⟩
        simp [hNTEmpty] at this
      have hvNotT : v ∉ T := by
        intro hvT
        have : v ∈ NT := Finset.mem_inter.mpr
          ⟨by simpa using hvN, hvT⟩
        simp [hNTEmpty] at this
      have huQ : u ∈ Q :=
        huClass.resolve_right huNotT
      have hvQ : v ∈ Q :=
        hvClass.resolve_right hvNotT
      have hinner :
          inner (⟨u, huQ⟩ : ↥Q) =
            inner (⟨v, hvQ⟩ : ↥Q) := by
        simpa [collapse_of_mem_component Q t huQ,
          collapse_of_mem_component Q t hvQ] using huv
      exact congrArg Subtype.val
        (inner_injective hinner)
    have hselected :
        N.card ≤
          finiteDegree (graph G Q T t)
            (inner ⟨d, hd⟩) :=
      selected_neighbors_card_le_compressed_degree
        hd hall N
          (fun _ hv => by simpa [N] using hv)
          hcollapseInjective
    have hNcard :
        N.card = finiteDegree G d := by
      unfold finiteDegree
      calc
        N.card = (↑N : Set V).ncard := by
          simp
        _ = (G.neighborSet d).ncard := by
          congr 1
          ext v
          simp [N]
    omega

/--
In the tight case `|T| = r+1`, the retained vertex `t` gives one extra
surviving boundary neighbor.  If a vertex has all `r+1` boundary
neighbors, one further vertex is retained through the collapsed root; if
it has at most `r`, the preceding one-representative count is already
strong enough.
-/
theorem finiteDegree_add_one_le_compressed_add
    [Fintype V]
    (hQT : Disjoint Q T) (ht : t ∈ T)
    {d : V} (hd : d ∈ Q)
    (hall :
      ∀ {v : V}, G.Adj d v → v ∈ Q ∪ T)
    (r : ℕ) (hr : 1 ≤ r)
    (hTcard : T.card = r + 1)
    (hboundaryDegree :
      (G.neighborSet d ∩ (↑T : Set V)).ncard ≤ r + 1) :
    finiteDegree G d + 1 ≤
      finiteDegree (graph G Q T t) (inner ⟨d, hd⟩) + r := by
  classical
  by_cases hsmall :
      (G.neighborSet d ∩ (↑T : Set V)).ncard ≤ r
  · have hdegree :=
      finiteDegree_le_compressed_add
        (t := t) hQT hd hall (r - 1) (by
          simpa [Nat.sub_add_cancel hr] using hsmall)
    omega
  · have hboundaryEq :
        (G.neighborSet d ∩ (↑T : Set V)).ncard =
          r + 1 := by
      omega
    letI : Fintype (G.neighborSet d) :=
      Fintype.ofFinite _
    let N := G.neighborFinset d
    let NT := N ∩ T
    have hNTcard :
        NT.card =
          (G.neighborSet d ∩ (↑T : Set V)).ncard := by
      calc
        NT.card = (↑NT : Set V).ncard := by
          simp
        _ = (G.neighborSet d ∩ (↑T : Set V)).ncard := by
          congr 1
          ext v
          simp [NT, N]
    have hNTT : NT = T := by
      apply Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right
      rw [hNTcard, hboundaryEq, hTcard]
    have htNT : t ∈ NT := by
      rw [hNTT]
      exact ht
    have htwoNT : 2 ≤ NT.card := by
      rw [hNTcard, hboundaryEq]
      omega
    have hNTerase : (NT.erase t).Nonempty := by
      rw [← Finset.card_pos,
        Finset.card_erase_of_mem htNT]
      omega
    let b := hNTerase.choose
    have hbErase : b ∈ NT.erase t :=
      hNTerase.choose_spec
    have hbNT : b ∈ NT :=
      Finset.mem_of_mem_erase hbErase
    have hbt : b ≠ t :=
      (Finset.mem_erase.mp hbErase).1
    let R := (NT.erase t).erase b
    let A := N \ R
    have hAN : A ⊆ N :=
      Finset.sdiff_subset
    have hA_boundary_class :
        ∀ {v : V}, v ∈ A → v ∈ T →
          v = t ∨ v = b := by
      intro v hvA hvT
      have hvN : v ∈ N := hAN hvA
      have hvNT : v ∈ NT :=
        Finset.mem_inter.mpr ⟨hvN, hvT⟩
      by_cases hvt : v = t
      · exact Or.inl hvt
      by_cases hvb : v = b
      · exact Or.inr hvb
      have hvR : v ∈ R := by
        exact Finset.mem_erase.mpr
          ⟨hvb, Finset.mem_erase.mpr ⟨hvt, hvNT⟩⟩
      exact False.elim ((Finset.mem_sdiff.mp hvA).2 hvR)
    have hcollapseInjective :
        Set.InjOn (collapse Q t) (↑A : Set V) := by
      intro u huA v hvA huv
      have huN : u ∈ N :=
        hAN (by simpa using huA)
      have hvN : v ∈ N :=
        hAN (by simpa using hvA)
      have huAdj : G.Adj d u := by
        simpa [N] using huN
      have hvAdj : G.Adj d v := by
        simpa [N] using hvN
      have huClass := Finset.mem_union.mp (hall huAdj)
      have hvClass := Finset.mem_union.mp (hall hvAdj)
      rcases huClass with huQ | huT <;>
        rcases hvClass with hvQ | hvT
      · have hinner :
            inner (⟨u, huQ⟩ : ↥Q) =
              inner (⟨v, hvQ⟩ : ↥Q) := by
          simpa [collapse_of_mem_component Q t huQ,
            collapse_of_mem_component Q t hvQ] using huv
        exact congrArg Subtype.val
          (inner_injective hinner)
      · have huImage :
            collapse Q t u =
              inner (⟨u, huQ⟩ : ↥Q) :=
          collapse_of_mem_component Q t huQ
        have hvNotQ :
            v ∉ Q :=
          Finset.disjoint_right.mp hQT hvT
        by_cases hvt : v = t
        · subst v
          rw [huImage,
            collapse_retained Q t hvNotQ] at huv
          exact False.elim
            (inner_ne_retained ⟨u, huQ⟩ huv)
        · rw [huImage,
            collapse_of_boundary_ne Q t hvNotQ hvt] at huv
          exact False.elim
            (inner_ne_collapsed ⟨u, huQ⟩ huv)
      · have hvImage :
            collapse Q t v =
              inner (⟨v, hvQ⟩ : ↥Q) :=
          collapse_of_mem_component Q t hvQ
        have huNotQ :
            u ∉ Q :=
          Finset.disjoint_right.mp hQT huT
        by_cases hut : u = t
        · subst u
          rw [collapse_retained Q t huNotQ,
            hvImage] at huv
          exact False.elim
            (inner_ne_retained ⟨v, hvQ⟩ huv.symm)
        · rw [collapse_of_boundary_ne Q t huNotQ hut,
            hvImage] at huv
          exact False.elim
            (inner_ne_collapsed ⟨v, hvQ⟩ huv.symm)
      · rcases hA_boundary_class
          (by simpa using huA) huT with hut | hub
        · rcases hA_boundary_class
            (by simpa using hvA) hvT with hvt | hvb
          · exact hut.trans hvt.symm
          · have hbNotQ :
                b ∉ Q :=
              Finset.disjoint_right.mp hQT
                (by rw [← hNTT]; exact hbNT)
            rw [hut, hvb,
              collapse_retained Q t
                (Finset.disjoint_right.mp hQT ht),
              collapse_of_boundary_ne Q t hbNotQ hbt] at huv
            exact False.elim (roots_ne.symm huv)
        · rcases hA_boundary_class
            (by simpa using hvA) hvT with hvt | hvb
          · have hbNotQ :
                b ∉ Q :=
              Finset.disjoint_right.mp hQT
                (by rw [← hNTT]; exact hbNT)
            rw [hub, hvt,
              collapse_of_boundary_ne Q t hbNotQ hbt,
              collapse_retained Q t
                (Finset.disjoint_right.mp hQT ht)] at huv
            exact False.elim (roots_ne huv)
          · exact hub.trans hvb.symm
    have hselected :
        A.card ≤
          finiteDegree (graph G Q T t)
            (inner ⟨d, hd⟩) :=
      selected_neighbors_card_le_compressed_degree
        hd hall A
          (fun _ hv => by
            simpa [N] using hAN hv)
          hcollapseInjective
    have hRSubset : R ⊆ N :=
      (Finset.erase_subset b (NT.erase t)).trans
        ((Finset.erase_subset t NT).trans
          Finset.inter_subset_left)
    have hcardSplit :
        A.card + R.card = N.card :=
      Finset.card_sdiff_add_card_eq_card hRSubset
    have hRcard :
        R.card = NT.card - 2 := by
      rw [show R = (NT.erase t).erase b by rfl,
        Finset.card_erase_of_mem hbErase,
        Finset.card_erase_of_mem htNT]
      omega
    have hNcard :
        N.card = finiteDegree G d := by
      unfold finiteDegree
      calc
        N.card = (↑N : Set V).ncard := by
          simp
        _ = (G.neighborSet d).ncard := by
          congr 1
          ext v
          simp [N]
    rw [hNTcard, hboundaryEq] at hRcard
    omega

/-! ## Lifting a recursive family to the exterior root -/

/--
The lifted set-path family together with the stronger support statement
needed when it is joined to paths inside the old core.
-/
structure LiftedOuterData
    (G : SimpleGraph V) (Q T : Finset V)
    (t y : V) (s : ℕ) where
  /-- The semi-admissible family ending at the exterior root. -/
  family :
    SemiAdmissibleSetPathFamily G
      (↑(T.erase t) : Set V) y s
  /-- No lifted path re-enters the old core away from its two boundary ends. -/
  support_class :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = family.endpoint i ∨ v = t ∨ v ∈ Q ∨ v = y

/--
Lift a recursive family from the two quotient roots, then append the
retained edge `t y`.  The resulting paths meet `T \ {t}` only at their
explicit lifted endpoints, which is the exact set-path hypothesis used by
COY Fact 1.
-/
theorem exists_lifted_outer_data
    [Fintype V]
    (hQT : Disjoint Q T) (ht : t ∈ T)
    {y : V} (hyQ : y ∉ Q) (hyT : y ∉ T)
    (hty : G.Adj t y)
    {s : ℕ}
    (F : AdmissiblePathFamily
      (graph G Q T t)
      (collapsedRoot : BoundaryCompressionVertex Q)
      retainedRoot s) :
    Nonempty
      (LiftedOuterData G Q T t y s) := by
  classical
  let L (i : Fin s) :
      PathLift G Q T t (F.path i) :=
    Classical.choice
      (exists_pathLift hQT ht (F.path i))
  have hyLift (i : Fin s) :
      y ∉ (L i).path.walk.support := by
    intro hy
    rcases (L i).support_class y hy with
      hEndpoint | ht' | hyQ'
    · subst y
      exact hyT (Finset.mem_of_mem_erase
        (L i).endpoint_mem)
    · exact hyT (ht' ▸ ht)
    · exact hyQ hyQ'
  have hdisjoint (i : Fin s) :
      (L i).path.walk.support.Disjoint
        (SimplePath.ofAdj hty).walk.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvLift hvEdge
    have hvy : v = y := by
      simpa using hvEdge
    subst v
    exact hyLift i hvLift
  let P (i : Fin s) : SimplePath G (L i).endpoint y :=
    (L i).path.appendDisjoint
      (SimplePath.ofAdj hty) (hdisjoint i)
  have hlength (i : Fin s) :
      (P i).length =
        F.start + 1 + i.val * F.step := by
    calc
      (P i).length = (L i).path.length + 1 := by
        simp [P, SimplePath.appendDisjoint_length]
      _ = (F.path i).length + 1 := by
        rw [(L i).length_eq]
      _ = (F.start + i.val * F.step) + 1 := by
        rw [F.length_path i]
      _ = F.start + 1 + i.val * F.step := by
        omega
  let outer :
      SemiAdmissibleSetPathFamily G
        (↑(T.erase t) : Set V) y s := {
    start := F.start + 1
    step := F.step
    admissible_step := F.admissible_step
    start_ge_one := by
      have := F.start_ge_two
      omega
    endpoint := fun i => (L i).endpoint
    endpoint_mem := fun i => by
      exact (L i).endpoint_mem
    path := P
    length_path := hlength
    unique_endpoint := by
      intro i v hvPath hvErase
      have hvParts :
          v ∈ (L i).path.walk.support ∨
            v ∈ (SimplePath.ofAdj hty).walk.support.tail := by
        change v ∈
          (((L i).path.appendDisjoint
            (SimplePath.ofAdj hty) (hdisjoint i)).walk.support)
          at hvPath
        rw [SimplePath.appendDisjoint,
          SimpleGraph.Walk.support_append] at hvPath
        exact List.mem_append.mp hvPath
      rcases hvParts with hvLift | hvEdge
      · rcases (L i).support_meets_T v hvLift
            (Finset.mem_of_mem_erase hvErase) with
          hvEndpoint | hvt
        · exact hvEndpoint
        · exact False.elim
            ((Finset.mem_erase.mp hvErase).1 hvt)
      · have hvy : v = y := by
          simpa using hvEdge
        subst v
        exact False.elim
          (hyT (Finset.mem_of_mem_erase hvErase))
  }
  refine ⟨{
    family := outer
    support_class := ?_
  }⟩
  intro i v hvPath
  have hvPath' :
      v ∈ (P i).walk.support := by
    exact hvPath
  have hvParts :
      v ∈ (L i).path.walk.support ∨
        v ∈ (SimplePath.ofAdj hty).walk.support.tail := by
    change v ∈
      (((L i).path.appendDisjoint
        (SimplePath.ofAdj hty) (hdisjoint i)).walk.support)
      at hvPath'
    rw [SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hvPath'
    exact List.mem_append.mp hvPath'
  rcases hvParts with hvLift | hvEdge
  · rcases (L i).support_class v hvLift with
      hvEndpoint | hvt | hvQ
    · exact Or.inl hvEndpoint
    · exact Or.inr (Or.inl hvt)
    · exact Or.inr (Or.inr (Or.inl hvQ))
  · have hvy : v = y := by
      simpa using hvEdge
    exact Or.inr (Or.inr (Or.inr hvy))

/-- Forget the auxiliary support certificate when only the family is needed. -/
theorem exists_lifted_outer_family
    [Fintype V]
    (hQT : Disjoint Q T) (ht : t ∈ T)
    {y : V} (hyQ : y ∉ Q) (hyT : y ∉ T)
    (hty : G.Adj t y)
    {s : ℕ}
    (F : AdmissiblePathFamily
      (graph G Q T t)
      (collapsedRoot : BoundaryCompressionVertex Q)
      retainedRoot s) :
    Nonempty
      (SemiAdmissibleSetPathFamily G
        (↑(T.erase t) : Set V) y s) := by
  obtain ⟨L⟩ :=
    exists_lifted_outer_data hQT ht hyQ hyT hty F
  exact ⟨L.family⟩

/-! ## The recursive rooted instance -/

/--
Package the source contraction as a strictly smaller rooted instance.

The parameter `ε` is the source's indicator for the tight boundary case.
The displayed ledger is deliberately kept as an input: the loose and tight
degree-counting theorems above discharge it without hiding the one-degree
gain in the tight case.
-/
theorem exists_recursive_family
    [Fintype V]
    {q : ℕ} {x y z : V}
    (M : MinimalCounterexample q G x y z)
    {C Q T : Finset V}
    (hQ : ComponentRegion G C Q)
    (hQC : Disjoint Q C) (hCcard : 3 ≤ C.card)
    (hQT : Disjoint Q T)
    (hboundary :
      ∀ {d a : V}, d ∈ Q → G.Adj d a →
        a ∈ C → a ∈ T)
    (t : V) (ht : t ∈ T)
    {d₀ d₁ t₁ : V}
    (hd₀ : d₀ ∈ Q) (htd₀ : G.Adj t d₀)
    (hd₁ : d₁ ∈ Q) (ht₁ : t₁ ∈ T)
    (ht₁t : t₁ ≠ t) (ht₁d₁ : G.Adj t₁ d₁)
    (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hordinary : ∃ d ∈ Q, d ≠ z)
    (r ε : ℕ) (hrStrong : r + 1 < q)
    (hεr : ε ≤ r)
    (hdegreeLedger :
      ∀ d (hd : d ∈ Q),
        finiteDegree G d + ε ≤
          finiteDegree (graph G Q T t) (inner ⟨d, hd⟩) + r) :
    Nonempty
      (AdmissiblePathFamily
        (graph G Q T t)
        (collapsedRoot : BoundaryCompressionVertex Q)
        retainedRoot (q - r + ε)) := by
  let H := graph G Q T t
  let q' := q - r + ε
  let e : BoundaryCompressionVertex Q :=
    if hz : z ∈ Q then inner ⟨z, hz⟩ else collapsedRoot
  have hq'Pos : 1 ≤ q' := by
    dsimp [q']
    omega
  have hq'Four : q' ≤ 4 := by
    have hq'Le : q' ≤ q := by
      dsimp [q']
      omega
    exact hq'Le.trans M.q_le_four
  have hrooted :
      IsTwoConnected
        (H ⊔ edge
          (collapsedRoot : BoundaryCompressionVertex Q)
          retainedRoot) := by
    exact rooted_graph_two_connected
      hQ hboundary hQT ht hd₀ htd₀
      hd₁ ht₁ ht₁t ht₁d₁
      M.underlying_two_connected
  have hord :
      ∃ w : BoundaryCompressionVertex Q,
        w ≠ collapsedRoot ∧
        w ≠ retainedRoot ∧ w ≠ e := by
    obtain ⟨d, hd, hdz⟩ := hordinary
    refine ⟨inner ⟨d, hd⟩,
      inner_ne_collapsed ⟨d, hd⟩,
      inner_ne_retained ⟨d, hd⟩, ?_⟩
    dsimp [e]
    split_ifs with hzQ
    · intro h
      have hsub :
          (⟨d, hd⟩ : ↥Q) = ⟨z, hzQ⟩ :=
        inner_injective h
      exact hdz (congrArg Subtype.val hsub)
    · exact inner_ne_collapsed ⟨d, hd⟩
  let I :
      RootedInstance q' H
        (collapsedRoot : BoundaryCompressionVertex Q)
        retainedRoot e := {
    q_pos := hq'Pos
    q_le_four := hq'Four
    roots_ne := roots_ne
    rooted_two_connected := hrooted
    ordinary_nonempty := hord
    degree_lower := by
      intro w hwCollapsed hwRetained hwException
      cases w with
      | none =>
          exact False.elim (hwCollapsed rfl)
      | some w =>
          cases w with
          | none =>
              exact False.elim (hwRetained rfl)
          | some d =>
              have hdz : d.1 ≠ z := by
                dsimp [e] at hwException
                split_ifs at hwException with hzQ
                · intro h
                  subst z
                  exact hwException rfl
                · intro h
                  subst z
                  exact hzQ d.2
              have hdx : d.1 ≠ x := by
                intro h
                subst x
                exact hxQ d.2
              have hdy : d.1 ≠ y := by
                intro h
                subst y
                exact hyQ d.2
              have hambient :=
                M.degree_lower d.1 hdx hdy hdz
              have hledger :=
                hdegreeLedger d.1 d.2
              have hinnerEq :
                  inner (⟨d.1, d.2⟩ : ↥Q) = inner d := by
                congr 2
              rw [hinnerEq] at hledger
              change q' + 1 ≤
                finiteDegree (graph G Q T t)
                  (inner d)
              dsimp [q']
              omega
  }
  exact M.smaller_solvable I
    (rootedComplexity_lt hQC hCcard)

end BoundaryCompression

namespace TypeOneCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

/--
Delete one clique vertex from a type-1 core.  This is the local
configuration used in Claim 3.6; the rank drops by one and remains
positive when the original rank is at least two.
-/
private def eraseTerminalForClaim36
    (C : TypeOneCore G x ℓ)
    (t : V) (ht : t ∈ C.T)
    (hℓ : 2 ≤ ℓ) :
    TypeOneCore G x (ℓ - 1) where
  T := C.T.erase t
  rank_pos := by omega
  card_T := by
    rw [Finset.card_erase_of_mem ht, C.card_T]
    omega
  root_not_mem := by
    exact fun hx => C.root_not_mem
      (Finset.mem_of_mem_erase hx)
  root_adj := by
    intro v hv
    exact C.root_adj v (Finset.mem_of_mem_erase hv)
  clique_T := by
    intro a ha b hb hab
    exact C.clique_T
      (by
        change a ∈ C.T.erase t at ha
        exact Finset.mem_of_mem_erase ha)
      (by
        change b ∈ C.T.erase t at hb
        exact Finset.mem_of_mem_erase hb)
      hab

end TypeOneCore

/--
A core-side catalogue after one boundary vertex has been deleted.  The
explicit length formula makes the equality-across-endpoints premise of
COY Fact 1 independent of the proof-dependent enumeration of each pointed
core.
-/
structure DeletedInnerData
    (G : SimpleGraph V) (x u : V)
    (carrier : Finset V) (deleted : V)
    (n δ : ℕ) where
  /-- The semi-admissible paths from the old root to the chosen endpoint. -/
  family : SemiAdmissiblePathFamily G x u n
  /-- Their source-prescribed common length list. -/
  length_path :
    ∀ i, (family.path i).length = 1 + i.val * δ
  /-- Every selected path remains in the old core carrier. -/
  support_subset :
    ∀ i v, v ∈ (family.path i).walk.support →
      v ∈ carrier
  /-- The retained exterior attachment was deleted from the catalogue. -/
  avoids_deleted :
    ∀ i, deleted ∉ (family.path i).walk.support

namespace TypeOneCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

private theorem claim36_catalog_start
    (C : TypeOneCore G x ℓ) (u : V) (hu : u ∈ C.T)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsTo u hu n
      hnOne hnFour hnCore).start = 1 := by
  unfold semiAdmissiblePathsTo
  interval_cases n <;> rfl

private theorem claim36_catalog_step
    (C : TypeOneCore G x ℓ) (u : V) (hu : u ∈ C.T)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsTo u hu n
      hnOne hnFour hnCore).step = 1 := by
  unfold semiAdmissiblePathsTo
  interval_cases n <;> rfl

/--
The type-1 inner catalogue of Claim 3.6 after deleting the retained
boundary vertex.  The rank-one case is the direct root edge; higher ranks
are the standard type-1 catalogue in the smaller clique.
-/
noncomputable def deletedInnerDataForClaim36
    (C : TypeOneCore G x ℓ)
    (u t : V) (hu : u ∈ C.T.erase t)
    (ht : t ∈ C.T) (hℓFour : ℓ ≤ 4) :
    DeletedInnerData G x u
      (insert x C.T) t ℓ 1 := by
  classical
  by_cases hℓOne : ℓ = 1
  · subst ℓ
    have huT : u ∈ C.T :=
      Finset.mem_of_mem_erase hu
    have hut : u ≠ t :=
      (Finset.mem_erase.mp hu).1
    have hxt : x ≠ t := by
      intro h
      subst t
      exact C.root_not_mem ht
    let P : SimplePath G x u :=
      SimplePath.ofAdj (C.root_adj u huT)
    let F : SemiAdmissiblePathFamily G x u 1 := {
      start := 1
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := le_rfl
      path := fun _ => P
      length_path := by
        intro i
        fin_cases i
        simp [P]
    }
    exact {
      family := F
      length_path := by
        intro i
        fin_cases i
        simp [F, P]
      support_subset := by
        intro i v hv
        fin_cases i
        simp [F, P] at hv ⊢
        rcases hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr huT
      avoids_deleted := by
        intro i
        fin_cases i
        simp [F, P, hut.symm, hxt.symm]
    }
  · have hℓTwo : 2 ≤ ℓ := by
      have := C.rank_pos
      omega
    let C' :=
      C.eraseTerminalForClaim36 t ht hℓTwo
    have hu' : u ∈ C'.T := by
      exact hu
    have hcore : ℓ ≤ (ℓ - 1) + 1 := by
      omega
    let F :=
      C'.semiAdmissiblePathsTo u hu' ℓ
        C.rank_pos hℓFour hcore
    exact {
      family := F
      length_path := by
        intro i
        rw [F.length_path i,
          C'.claim36_catalog_start
            u hu' ℓ C.rank_pos hℓFour hcore,
          C'.claim36_catalog_step
            u hu' ℓ C.rank_pos hℓFour hcore]
      support_subset := by
        intro i v hv
        have hv' :=
          C'.semiAdmissiblePathsTo_support
            u hu' ℓ C.rank_pos hℓFour hcore i v hv
        change v ∈ insert x (C.T.erase t) at hv'
        simp only [Finset.mem_insert] at hv' ⊢
        rcases hv' with rfl | hvT
        · exact Or.inl rfl
        · exact Or.inr (Finset.mem_of_mem_erase hvT)
      avoids_deleted := by
        intro i hti
        have htSupport :=
          C'.semiAdmissiblePathsTo_support
            u hu' ℓ C.rank_pos hℓFour hcore i t hti
        have htx : t ≠ x := by
          intro h
          subst t
          exact C.root_not_mem ht
        change t ∈ insert x (C.T.erase t) at htSupport
        simp only [Finset.mem_insert] at htSupport
        rcases htSupport with htx' | htErase
        · exact htx htx'
        · exact (Finset.mem_erase.mp htErase).1 rfl
    }

end TypeOneCore

namespace TypeThreeCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

private theorem claim36_T_catalog_start
    (C : TypeThreeCore G x ℓ) (u : V) (hu : u ∈ C.T)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT u hu n
      hnOne hnFour hnCore).start = 1 := by
  unfold semiAdmissiblePathsToT
  interval_cases n <;> rfl

private theorem claim36_T_catalog_step
    (C : TypeThreeCore G x ℓ) (u : V) (hu : u ∈ C.T)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT u hu n
      hnOne hnFour hnCore).step = 2 := by
  unfold semiAdmissiblePathsToT
  interval_cases n <;> rfl

private theorem claim36_T_deleted_catalog_start
    (C : TypeThreeCore G x ℓ)
    (u t : V) (hu : u ∈ C.T) (ht : t ∈ C.T)
    (hut : u ≠ t) (hlarge : ℓ + 2 ≤ C.T.card)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToTAfterDeleting
      u t hu ht hut hlarge n hnOne hnFour hnCore).start = 1 := by
  unfold semiAdmissiblePathsToTAfterDeleting
  interval_cases n <;> rfl

private theorem claim36_T_deleted_catalog_step
    (C : TypeThreeCore G x ℓ)
    (u t : V) (hu : u ∈ C.T) (ht : t ∈ C.T)
    (hut : u ≠ t) (hlarge : ℓ + 2 ≤ C.T.card)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToTAfterDeleting
      u t hu ht hut hlarge n hnOne hnFour hnCore).step = 2 := by
  unfold semiAdmissiblePathsToTAfterDeleting
  interval_cases n <;> rfl

/-- The slack type-3 inner catalogue, with only the retained `T`-vertex deleted. -/
noncomputable def deletedInnerDataSlackForClaim36
    (C : TypeThreeCore G x ℓ)
    (u t : V) (hu : u ∈ C.T.erase t)
    (ht : t ∈ C.T) (hlarge : ℓ + 2 ≤ C.T.card)
    (hcountFour : ℓ + 1 ≤ 4) :
    DeletedInnerData G x u
      (insert x (C.S ∪ C.T)) t (ℓ + 1) 2 := by
  classical
  have huT : u ∈ C.T :=
    Finset.mem_of_mem_erase hu
  have hut : u ≠ t :=
    (Finset.mem_erase.mp hu).1
  have hcountOne : 1 ≤ ℓ + 1 := by omega
  let F :=
    C.semiAdmissiblePathsToTAfterDeleting
      u t huT ht hut hlarge (ℓ + 1)
      hcountOne hcountFour (by omega)
  exact {
    family := F
    length_path := by
      intro i
      rw [F.length_path i,
        C.claim36_T_deleted_catalog_start
          u t huT ht hut hlarge (ℓ + 1)
          hcountOne hcountFour (by omega),
        C.claim36_T_deleted_catalog_step
          u t huT ht hut hlarge (ℓ + 1)
          hcountOne hcountFour (by omega)]
    support_subset := by
      intro i v hv
      have hv' :=
        C.semiAdmissiblePathsToTAfterDeleting_support
          u t huT ht hut hlarge (ℓ + 1)
          hcountOne hcountFour (by omega) i v hv
      simp only [Finset.mem_insert, Finset.mem_union] at hv' ⊢
      rcases hv' with rfl | hvS | hvT
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hvS)
      · exact Or.inr (Or.inr
          (Finset.mem_of_mem_erase hvT))
    avoids_deleted := by
      intro i
      exact
        C.semiAdmissiblePathsToTAfterDeleting_avoids_deleted
          u t huT ht hut hlarge (ℓ + 1)
          hcountOne hcountFour (by omega) i
  }

/--
The tight type-3 inner catalogue.  For rank one it is the direct root
edge.  At larger rank one vertex is erased from each side and the standard
rank-`ℓ-1` catalogue supplies `ℓ` odd lengths.
-/
noncomputable def deletedInnerDataTightForClaim36
    (C : TypeThreeCore G x ℓ)
    (u t : V) (hu : u ∈ C.T.erase t)
    (ht : t ∈ C.T)
    (htight : C.T.card = ℓ + 1)
    (hℓFour : ℓ ≤ 4) :
    DeletedInnerData G x u
      (insert x (C.S ∪ C.T)) t ℓ 2 := by
  classical
  have huT : u ∈ C.T :=
    Finset.mem_of_mem_erase hu
  have hut : u ≠ t :=
    (Finset.mem_erase.mp hu).1
  have hℓOne : 1 ≤ ℓ := by
    have htwo : 2 ≤ C.T.card :=
      (Nat.le_max_right (ℓ + 1) 2).trans
        C.card_T_lower
    omega
  by_cases hℓEq : ℓ = 1
  · subst ℓ
    have hxt : x ≠ t := by
      intro h
      subst t
      exact C.root_not_mem_T ht
    let P : SimplePath G x u :=
      SimplePath.ofAdj (C.root_adj_T u huT)
    let F : SemiAdmissiblePathFamily G x u 1 := {
      start := 1
      step := 2
      admissible_step := Or.inr rfl
      start_ge_one := le_rfl
      path := fun _ => P
      length_path := by
        intro i
        fin_cases i
        simp [P]
    }
    exact {
      family := F
      length_path := by
        intro i
        fin_cases i
        simp [F, P]
      support_subset := by
        intro i v hv
        fin_cases i
        simp [F, P] at hv ⊢
        rcases hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr huT)
      avoids_deleted := by
        intro i
        fin_cases i
        simp [F, P, hut.symm, hxt.symm]
    }
  · have hℓTwo : 2 ≤ ℓ := by omega
    have hSNonempty : C.S.Nonempty := by
      rw [← Finset.card_pos, C.card_S]
      omega
    let s₀ := hSNonempty.choose
    have hs₀ : s₀ ∈ C.S :=
      hSNonempty.choose_spec
    have hbalance : C.T.card = C.S.card + 1 := by
      rw [htight, C.card_S]
    let C' :=
      C.eraseBalanced s₀ t hs₀ ht hℓTwo hbalance
    have hu' : u ∈ C'.T := by
      exact hu
    have hcore : ℓ ≤ (ℓ - 1) + 1 := by omega
    let F :=
      C'.semiAdmissiblePathsToT u hu' ℓ
        hℓOne hℓFour hcore
    exact {
      family := F
      length_path := by
        intro i
        rw [F.length_path i,
          C'.claim36_T_catalog_start
            u hu' ℓ hℓOne hℓFour hcore,
          C'.claim36_T_catalog_step
            u hu' ℓ hℓOne hℓFour hcore]
      support_subset := by
        intro i v hv
        have hv' :=
          C'.semiAdmissiblePathsToT_support
            u hu' ℓ hℓOne hℓFour hcore i v hv
        change
          v ∈ insert x
            ((C.S.erase s₀) ∪ (C.T.erase t)) at hv'
        simp only [Finset.mem_insert, Finset.mem_union] at hv' ⊢
        rcases hv' with rfl | hvS | hvT
        · exact Or.inl rfl
        · exact Or.inr
            (Or.inl (Finset.mem_of_mem_erase hvS))
        · exact Or.inr
            (Or.inr (Finset.mem_of_mem_erase hvT))
      avoids_deleted := by
        intro i hti
        have htSupport :=
          C'.semiAdmissiblePathsToT_support
            u hu' ℓ hℓOne hℓFour hcore i t hti
        change
          t ∈ insert x
            ((C.S.erase s₀) ∪ (C.T.erase t)) at htSupport
        have htx : t ≠ x := by
          intro h
          subst t
          exact C.root_not_mem_T ht
        have htNotS : t ∉ C.S.erase s₀ := by
          intro htS
          exact Finset.disjoint_left.mp C.disjoint
            (Finset.mem_of_mem_erase htS) ht
        simp [htx, htNotS] at htSupport
  }

end TypeThreeCore

namespace Core

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

/-- Every COY core carrier has at least three vertices. -/
theorem three_le_carrier_card_claim36
    (C : Core G x ℓ) :
    3 ≤ C.carrier.card := by
  cases C with
  | typeOne A =>
      have hrank := A.rank_pos
      simp only [Core.carrier, Core.S, Core.T,
        Finset.empty_union]
      rw [Finset.card_insert_of_notMem A.root_not_mem,
        A.card_T]
      omega
  | typeTwo A =>
      have hx : x ∉ A.S ∪ A.T := by
        simp [A.root_not_mem_S, A.root_not_mem_T]
      simp only [Core.carrier, Core.S, Core.T]
      rw [Finset.card_insert_of_notMem hx,
        Finset.card_union_of_disjoint A.disjoint,
        A.card_S]
      omega
  | typeThree A =>
      have hx : x ∉ A.S ∪ A.T := by
        simp [A.root_not_mem_S, A.root_not_mem_T]
      have htwo : 2 ≤ A.T.card :=
        (Nat.le_max_right (ℓ + 1) 2).trans
          A.card_T_lower
      simp only [Core.carrier, Core.S, Core.T]
      rw [Finset.card_insert_of_notMem hx,
        Finset.card_union_of_disjoint A.disjoint]
      omega

/-- Tight `T`-size forces positive rank in every source core type. -/
theorem rank_pos_of_tight_T_claim36
    (C : Core G x ℓ)
    (hT : C.T.card = ℓ + 1) :
    1 ≤ ℓ := by
  cases C with
  | typeOne A => exact A.rank_pos
  | typeTwo A => exact A.rank_ge_two.trans' (by omega)
  | typeThree A =>
      change A.T.card = ℓ + 1 at hT
      have htwo : 2 ≤ A.T.card :=
        (Nat.le_max_right (ℓ + 1) 2).trans
          A.card_T_lower
      omega

end Core

/--
Join a lifted recursive family to endpoint-wise core catalogues.  This is
the Claim 3.6 use of COY Fact 1, with the simplicity proof reduced to the
four possible support classes of a lifted outer path.
-/
theorem factOne_of_liftedOuter
    [DecidableEq V]
    {G : SimpleGraph V} {x y t : V}
    {Q T carrier : Finset V} {s n δ : ℕ}
    (hQCarrier : Disjoint Q carrier)
    (hxT : x ∉ T) (hyT : y ∉ T)
    (hyCarrier : y ∉ carrier)
    (hxy : x ≠ y)
    (hs : 1 ≤ s) (hn : 1 ≤ n)
    (outer : BoundaryCompression.LiftedOuterData
      G Q T t y s)
    (inner :
      ∀ i, DeletedInnerData G x
        (outer.family.endpoint i) carrier t n δ) :
    Nonempty (AdmissiblePathFamily G x y (s + n - 1)) := by
  let U : Set V := ↑(T.erase t)
  let certificate :
      FactOneCertificate G x y U s n := {
    hs := hs
    ht := hn
    x_ne_y := hxy
    x_not_mem := by
      intro hx
      exact hxT (Finset.mem_of_mem_erase hx)
    y_not_mem := by
      intro hy
      exact hyT (Finset.mem_of_mem_erase hy)
    outer := outer.family
    inner := fun i => (inner i).family
    equal_inner_length := by
      intro i j
      rw [(inner i).length_path j,
        (inner (firstFin hs)).length_path j]
    avoid_outer := by
      intro i j
      apply List.disjoint_left.mpr
      intro v hvInner hvOuterTail
      have hvCarrier :
          v ∈ carrier :=
        (inner i).support_subset j v hvInner
      rcases outer.support_class i v
          (List.mem_of_mem_tail hvOuterTail) with
        hvEndpoint | hvt | hvQ | hvy
      · subst v
        exact outer.family.path i |>.start_not_mem_tail
          hvOuterTail
      · subst v
        exact (inner i).avoids_deleted j hvInner
      · exact
          (Finset.disjoint_left.mp hQCarrier hvQ hvCarrier)
      · exact hyCarrier (hvy ▸ hvCarrier)
  }
  exact fact_one certificate

namespace PreferredOrientationData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
The recursive part of Claim 3.6, before the core-side catalogue is joined
back in.  Its conclusion exposes the retained old vertex `t` and keeps the
source indicator `ε = 1[|T| = rank+1]` visible in the family size.
-/
private theorem exists_recursive_family_on_otherDeletionRegion
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype :
      D.chosen.rooted.core.typeNumber = 1 ∨
        D.chosen.rooted.core.typeNumber = 3)
    (K :
      (deleteVertices G
        D.chosen.rooted.core.carrier).ConnectedComponent)
    (hK : K ≠ D.chosen.rooted.otherComponent)
    (hordinary :
      ∃ d ∈ componentVertices G
          D.chosen.rooted.core.carrier K,
        d ≠ z)
    (hnoS :
      ¬∃ d ∈ componentVertices G
          D.chosen.rooted.core.carrier K,
        ∃ s ∈ D.chosen.rooted.core.S,
          G.Adj s d) :
    ∃ t ∈ D.chosen.rooted.core.T,
      Nonempty
        (AdmissiblePathFamily
          (BoundaryCompression.graph G
            (componentVertices G
              D.chosen.rooted.core.carrier K)
            D.chosen.rooted.core.T t)
          (BoundaryCompression.collapsedRoot :
            BoundaryCompressionVertex
              (componentVertices G
                D.chosen.rooted.core.carrier K))
          BoundaryCompression.retainedRoot
          (q - D.chosen.rank +
            if D.chosen.rooted.core.T.card =
                D.chosen.rank + 1 then 1 else 0)) := by
  let C := D.chosen.rooted.core
  let Q := D.otherDeletionRegion K
  let T := C.T
  have hQ : ComponentRegion G C.carrier Q :=
    D.otherDeletionRegion_componentRegion K
  have hnoS' :
      ¬∃ d ∈ Q, ∃ s ∈ C.S, G.Adj s d := by
    simpa only [Q, C,
      PreferredOrientationData.otherDeletionRegion] using hnoS
  have hordinary' :
      ∃ d ∈ Q, d ≠ z := by
    simpa only [Q, C,
      PreferredOrientationData.otherDeletionRegion] using hordinary
  have hQC : Disjoint Q C.carrier :=
    hQ.disjoint
  have hQT : Disjoint Q T :=
    hQ.disjoint.mono_right C.T_subset_carrier
  have hxQ : x ∉ Q := by
    intro hx
    exact hQ.not_mem_separator hx C.root_mem_carrier
  have hyQ : y ∉ Q := by
    exact D.other_root_not_mem_otherDeletionRegion K hK
  have hboundary :
      ∀ {d a : V}, d ∈ Q → G.Adj d a →
        a ∈ C.carrier → a ∈ T := by
    intro d a hd hda ha
    exact D.boundary_mem_T_of_no_S_attachment
      M hnot hregion htype K
      hnoS' hd hda ha
  obtain ⟨d₀, hd₀, t₀, ht₀, ht₀d₀,
      d₁, hd₁, t₁, ht₁, ht₁t₀, ht₁d₁⟩ :=
    D.exists_two_T_attachments_of_no_S_attachment
      M hnot hregion htype K
        hnoS'
  have hd₀Q : d₀ ∈ Q := by
    exact hd₀
  have hd₁Q : d₁ ∈ Q := by
    exact hd₁
  have ht₀T : t₀ ∈ T := by
    simpa [T, C] using ht₀
  have ht₁T : t₁ ∈ T := by
    simpa [T, C] using ht₁
  have hall (d : V) (hd : d ∈ Q) :
      ∀ ⦃v : V⦄, G.Adj d v → v ∈ Q ∪ T := by
    intro v hdv
    by_cases hvC : v ∈ C.carrier
    · exact Finset.mem_union_right Q
        (hboundary hd hdv hvC)
    · exact Finset.mem_union_left T
        (hQ.closed hd hdv hvC)
  have hTbound (d : V) (hd : d ∈ Q) :
      (G.neighborSet d ∩ (↑T : Set V)).ncard ≤
        D.chosen.rank + 1 := by
    have hdy : d ≠ y := by
      intro h
      subst d
      exact hyQ hd
    have hdCarrier : d ∉ C.carrier :=
      hQ.not_mem_separator hd
    have hcarrierBound :
        (G.neighborSet d ∩
          (↑C.carrier : Set V)).ncard ≤
            D.chosen.rank + 1 := by
      simpa [SelectedWorkingCore.rooted,
        SelectedWorkingCore.rank, C] using
        (SelectedWorkingCore.natural hnot).coreNeighbor_ncard_le
          hdCarrier hdy (by simpa using hdy)
    have hTIntersection :
        G.neighborSet d ∩ (↑T : Set V) =
          G.neighborSet d ∩
            (↑C.carrier : Set V) := by
      ext a
      change
        (G.Adj d a ∧ a ∈ T) ↔
          (G.Adj d a ∧ a ∈ C.carrier)
      constructor
      · rintro ⟨hda, haT⟩
        exact ⟨hda, C.T_subset_carrier haT⟩
      · rintro ⟨hda, haC⟩
        exact ⟨hda, hboundary hd hda haC⟩
    rw [hTIntersection]
    exact hcarrierBound
  have hneighbors :=
    D.neighborSets_eq_T_of_natural_singleton
      M hnot hregion htype
  have ht₀Neighbor : t₀ ∈ G.neighborSet y := by
    rw [hneighbors.2]
    exact ht₀
  have ht₀y : G.Adj t₀ y := by
    have hyt₀ : G.Adj y t₀ := by
      simpa [SimpleGraph.mem_neighborSet] using
        ht₀Neighbor
    exact hyt₀.symm
  have hattach :
      C.HasTAttachment
        D.chosen.rooted.otherRegion :=
    ⟨y, D.chosen.rooted.other_root_mem_otherRegion,
      t₀, ht₀, ht₀y⟩
  have hrStrong :
      D.chosen.rank + 1 < q :=
    (M.rootedCore_factThree D.chosen.rooted).2
      hattach
  let ε :=
    if T.card = D.chosen.rank + 1 then 1 else 0
  have hεr : ε ≤ D.chosen.rank := by
    by_cases htight :
        T.card = D.chosen.rank + 1
    · have hrank :
          1 ≤ D.chosen.rank :=
        C.rank_pos_of_tight_T_claim36
          (by simpa [T, C] using htight)
      simp [ε, htight, hrank]
    · simp [ε, htight]
  have hledger :
      ∀ d (hd : d ∈ Q),
        finiteDegree G d + ε ≤
          finiteDegree
              (BoundaryCompression.graph G Q T t₀)
              (BoundaryCompression.inner ⟨d, hd⟩) +
            D.chosen.rank := by
    intro d hd
    by_cases htight :
        T.card = D.chosen.rank + 1
    · have hrank :
          1 ≤ D.chosen.rank :=
        C.rank_pos_of_tight_T_claim36
          (by simpa [T, C] using htight)
      have h :=
        BoundaryCompression.finiteDegree_add_one_le_compressed_add
          (G := G) (Q := Q) (T := T) (t := t₀)
          hQT ht₀T hd
          (fun {_} hv => hall d hd hv)
          D.chosen.rank
          hrank htight (hTbound d hd)
      simpa [ε, htight] using h
    · have h :=
        BoundaryCompression.finiteDegree_le_compressed_add
          (G := G) (Q := Q) (T := T) (t := t₀)
          hQT hd
          (fun {_} hv => hall d hd hv)
          D.chosen.rank
          (hTbound d hd)
      simpa [ε, htight] using h
  have hF :=
    BoundaryCompression.exists_recursive_family
      (G := G) (C := C.carrier) (Q := Q) (T := T)
      M hQ hQC C.three_le_carrier_card_claim36
      hQT hboundary t₀ ht₀T hd₀Q ht₀d₀
      hd₁Q ht₁T ht₁t₀ ht₁d₁
      hxQ hyQ
      hordinary'
      D.chosen.rank ε hrStrong hεr hledger
  exact ⟨t₀, ht₀, by
    simpa only [C, Q, T, ε,
      PreferredOrientationData.otherDeletionRegion] using hF⟩

/--
COY Claim 3.6, source-faithful form.

For a natural singleton exterior and a type-1 or type-3 working core, any
different deletion component containing an ordinary vertex has an
attachment to the core side `S`.  The component is stated directly with
`componentVertices`, so downstream claims need no private alias.
-/
theorem attachment_to_S_of_natural_singleton
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype :
      D.chosen.rooted.core.typeNumber = 1 ∨
        D.chosen.rooted.core.typeNumber = 3)
    (K :
      (deleteVertices G
        D.chosen.rooted.core.carrier).ConnectedComponent)
    (hK : K ≠ D.chosen.rooted.otherComponent)
    (hordinary :
      ∃ d ∈ componentVertices G
          D.chosen.rooted.core.carrier K,
        d ≠ z) :
    ∃ d ∈ componentVertices G
        D.chosen.rooted.core.carrier K,
      ∃ s ∈ D.chosen.rooted.core.S,
        G.Adj s d := by
  by_contra hnoS
  have hnoS' :
      ¬∃ d ∈ componentVertices G
          D.chosen.rooted.core.carrier K,
        ∃ s ∈ D.chosen.rooted.core.S,
          G.Adj s d := by
    exact hnoS
  obtain ⟨t, ht, F⟩ :=
    D.exists_recursive_family_on_otherDeletionRegion
      M hnot hregion htype K hK hordinary hnoS'
  let C := D.chosen.rooted.core
  let Q :=
    componentVertices G C.carrier K
  have hQ : ComponentRegion G C.carrier Q :=
    componentRegion_componentVertices G C.carrier K
  have hQT : Disjoint Q C.T :=
    hQ.disjoint.mono_right C.T_subset_carrier
  have hyQ : y ∉ Q := by
    exact D.other_root_not_mem_otherDeletionRegion K hK
  have hyT : y ∉ C.T := by
    intro hy
    exact D.chosen.rooted.other_root_not_mem
      (C.T_subset_carrier hy)
  have hyCarrier : y ∉ C.carrier :=
    D.chosen.rooted.other_root_not_mem
  have hneighbors :=
    D.neighborSets_eq_T_of_natural_singleton
      M hnot hregion htype
  have hty : G.Adj t y := by
    have hyt : G.Adj y t := by
      rw [← SimpleGraph.mem_neighborSet,
        hneighbors.2]
      exact ht
    exact hyt.symm
  have hrStrong :
      D.chosen.rank + 1 < q := by
    have hattach :
        C.HasTAttachment
          D.chosen.rooted.otherRegion :=
      ⟨y, D.chosen.rooted.other_root_mem_otherRegion,
        t, ht, hty⟩
    exact
      (M.rootedCore_factThree D.chosen.rooted).2
        hattach
  cases hcore : D.chosen.rooted.core with
  | typeOne A =>
      have F' :
          Nonempty
            (AdmissiblePathFamily
              (BoundaryCompression.graph G Q A.T t)
              (BoundaryCompression.collapsedRoot :
                BoundaryCompressionVertex Q)
              BoundaryCompression.retainedRoot
              (q - D.chosen.rank + 1)) := by
        simpa [Q, C, hcore, Core.T, A.card_T] using F
      obtain ⟨F'⟩ := F'
      have htA : t ∈ A.T := by
        simpa [C, hcore, Core.T] using ht
      have hQTA : Disjoint Q A.T := by
        simpa [C, hcore, Core.T] using hQT
      have hyA : y ∉ A.T := by
        simpa [C, hcore, Core.T] using hyT
      obtain ⟨outer⟩ :=
        BoundaryCompression.exists_lifted_outer_data
          hQTA htA hyQ hyA hty F'
      have hrankFour : D.chosen.rank ≤ 4 := by
        have hqFour := M.q_le_four
        omega
      let inner (i : Fin (q - D.chosen.rank + 1)) :
          DeletedInnerData G x
            (outer.family.endpoint i)
            (insert x A.T) t D.chosen.rank 1 :=
          A.deletedInnerDataForClaim36
            (outer.family.endpoint i) t
          (by exact outer.family.endpoint_mem i)
          htA hrankFour
      have hfact :=
        factOne_of_liftedOuter
          (G := G) (x := x) (y := y) (t := t)
          (Q := Q) (T := A.T)
          (carrier := insert x A.T)
          (s := q - D.chosen.rank + 1)
          (n := D.chosen.rank) (δ := 1)
          (by
            simpa [C, hcore, Core.carrier,
              Core.S, Core.T] using hQ.disjoint)
          A.root_not_mem hyA
          (by
            simpa [C, hcore, Core.carrier,
              Core.S, Core.T] using hyCarrier)
          M.roots_ne (by omega) A.rank_pos
          outer inner
      apply M.no_paths
      change Nonempty
        (AdmissiblePathFamily G x y q)
      simpa [Nat.sub_add_cancel (by omega :
        D.chosen.rank ≤ q)] using hfact
  | typeTwo A =>
      rcases htype with htype | htype <;>
        simp [hcore, Core.typeNumber] at htype
  | typeThree A =>
      have htA : t ∈ A.T := by
        simpa [C, hcore, Core.T] using ht
      have hQTA : Disjoint Q A.T := by
        simpa [C, hcore, Core.T] using hQT
      have hyA : y ∉ A.T := by
        simpa [C, hcore, Core.T] using hyT
      have hcarrierDisjoint :
          Disjoint Q (insert x (A.S ∪ A.T)) := by
        simpa [C, hcore, Core.carrier,
          Core.S, Core.T] using hQ.disjoint
      have hyACarrier :
          y ∉ insert x (A.S ∪ A.T) := by
        simpa [C, hcore, Core.carrier,
          Core.S, Core.T] using hyCarrier
      have hcountFour :
          D.chosen.rank + 1 ≤ 4 := by
        have hqFour := M.q_le_four
        omega
      by_cases htight :
          A.T.card = D.chosen.rank + 1
      · have F' :
            Nonempty
              (AdmissiblePathFamily
                (BoundaryCompression.graph G Q A.T t)
                (BoundaryCompression.collapsedRoot :
                  BoundaryCompressionVertex Q)
                BoundaryCompression.retainedRoot
                (q - D.chosen.rank + 1)) := by
          simpa [Q, C, hcore, Core.T, htight] using F
        obtain ⟨F'⟩ := F'
        obtain ⟨outer⟩ :=
          BoundaryCompression.exists_lifted_outer_data
            hQTA htA hyQ hyA hty F'
        have hrankFour : D.chosen.rank ≤ 4 := by
          omega
        let inner (i : Fin (q - D.chosen.rank + 1)) :
            DeletedInnerData G x
              (outer.family.endpoint i)
              (insert x (A.S ∪ A.T)) t
              D.chosen.rank 2 :=
          A.deletedInnerDataTightForClaim36
            (outer.family.endpoint i) t
            (by exact outer.family.endpoint_mem i)
            htA htight hrankFour
        have hrankPos : 1 ≤ D.chosen.rank := by
          have htwo : 2 ≤ A.T.card :=
            (Nat.le_max_right
              (D.chosen.rank + 1) 2).trans
              A.card_T_lower
          omega
        have hfact :=
          factOne_of_liftedOuter
            (G := G) (x := x) (y := y) (t := t)
            (Q := Q) (T := A.T)
            (carrier := insert x (A.S ∪ A.T))
            (s := q - D.chosen.rank + 1)
            (n := D.chosen.rank) (δ := 2)
            hcarrierDisjoint A.root_not_mem_T hyA
            hyACarrier M.roots_ne (by omega)
            hrankPos outer inner
        apply M.no_paths
        change Nonempty
          (AdmissiblePathFamily G x y q)
        simpa [Nat.sub_add_cancel (by omega :
          D.chosen.rank ≤ q)] using hfact
      · have hlarge :
            D.chosen.rank + 2 ≤ A.T.card := by
          have hlower :
              D.chosen.rank + 1 ≤ A.T.card :=
            (Nat.le_max_left
              (D.chosen.rank + 1) 2).trans
              A.card_T_lower
          omega
        have F' :
            Nonempty
              (AdmissiblePathFamily
                (BoundaryCompression.graph G Q A.T t)
                (BoundaryCompression.collapsedRoot :
                  BoundaryCompressionVertex Q)
                BoundaryCompression.retainedRoot
                (q - D.chosen.rank)) := by
          simpa [Q, C, hcore, Core.T, htight] using F
        obtain ⟨F'⟩ := F'
        obtain ⟨outer⟩ :=
          BoundaryCompression.exists_lifted_outer_data
            hQTA htA hyQ hyA hty F'
        let inner (i : Fin (q - D.chosen.rank)) :
            DeletedInnerData G x
              (outer.family.endpoint i)
              (insert x (A.S ∪ A.T)) t
              (D.chosen.rank + 1) 2 :=
          A.deletedInnerDataSlackForClaim36
            (outer.family.endpoint i) t
            (by exact outer.family.endpoint_mem i)
            htA hlarge hcountFour
        have hfact :=
          factOne_of_liftedOuter
            (G := G) (x := x) (y := y) (t := t)
            (Q := Q) (T := A.T)
            (carrier := insert x (A.S ∪ A.T))
            (s := q - D.chosen.rank)
            (n := D.chosen.rank + 1) (δ := 2)
            hcarrierDisjoint A.root_not_mem_T hyA
            hyACarrier M.roots_ne (by omega)
            (by omega) outer inner
        apply M.no_paths
        change Nonempty
          (AdmissiblePathFamily G x y q)
        simpa [Nat.sub_add_cancel (by omega :
          D.chosen.rank ≤ q)] using hfact

/--
In a natural type-1 singleton-exterior configuration, no different
deletion component can contain an ordinary vertex: Claim 3.6 would attach
it to the empty side `S`.
-/
theorem no_ordinary_other_component_of_natural_singleton_typeOne
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (A : TypeOneCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeOne A)
    (K :
      (deleteVertices G
        D.chosen.rooted.core.carrier).ConnectedComponent)
    (hK : K ≠ D.chosen.rooted.otherComponent) :
    ¬∃ d ∈ componentVertices G
        D.chosen.rooted.core.carrier K,
      d ≠ z := by
  intro hordinary
  obtain ⟨d, hd, s, hs, hsd⟩ :=
    D.attachment_to_S_of_natural_singleton
      M hnot hregion
      (Or.inl (by rw [hcore]; rfl))
      K hK hordinary
  rw [hcore] at hs
  simp [Core.S] at hs

end PreferredOrientationData

end COY

end DeanK5
