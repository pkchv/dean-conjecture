import DeanK5.EndLobeExistence
import DeanK5.Graph.Connectivity
import DeanK5.Graph.Separation

/-!
# End lobes of a connected component

The component form of the end-lobe input is derived from the ordinary
connected-graph form.  This file transports the resulting lobes, their
2-connected blocks, and their connector from a connected-component subtype
back to the original graph.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace ConnectedComponentEndLobe

variable [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C]

/-- The component inclusion, with adjacency reflected as well as preserved. -/
def inclusion : C.toSimpleGraph ↪g G where
  toFun z := z.1
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- The interior of a component lobe, on the original vertex carrier. -/
def ambientInner (L : EndLobe C.toSimpleGraph) : Finset V :=
  L.inner.map (inclusion C).toEmbedding

omit [Fintype V] [DecidableEq V] in
theorem mem_ambientInner_iff
    (L : EndLobe C.toSimpleGraph) (v : V) :
    v ∈ ambientInner C L ↔
      ∃ z : C, z ∈ L.inner ∧ z.1 = v := by
  simp only [ambientInner, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, hzv⟩
    exact ⟨z, hz, hzv⟩
  · rintro ⟨z, hz, hzv⟩
    exact ⟨z, hz, hzv⟩

/-- The component lobe block embedded in the ambient graph. -/
def blockEmbedding (L : EndLobe C.toSimpleGraph) :
    (C.toSimpleGraph.induce
      (↑(insert L.cut L.inner) : Set C)) ↪g G where
  toFun z := z.1.1
  inj' := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  map_rel_iff' := Iff.rfl

omit [Fintype V] in
theorem range_blockEmbedding
    (L : EndLobe C.toSimpleGraph) :
    Set.range (blockEmbedding C L) =
      (↑(insert L.cut.1 (ambientInner C L)) : Set V) := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    rcases Finset.mem_insert.mp z.2 with hzCut | hzInner
    · apply Finset.mem_insert.mpr
      exact Or.inl (congrArg Subtype.val hzCut)
    · apply Finset.mem_insert.mpr
      exact Or.inr
        ((mem_ambientInner_iff C L z.1.1).2
          ⟨z.1, hzInner, rfl⟩)
  · intro hv
    rcases Finset.mem_insert.mp hv with hvCut | hvInner
    · refine ⟨⟨L.cut, Finset.mem_insert_self _ _⟩, ?_⟩
      exact hvCut.symm
    · obtain ⟨z, hz, hzv⟩ :=
        (mem_ambientInner_iff C L v).1 hvInner
      refine ⟨⟨z, Finset.mem_insert.mpr (Or.inr hz)⟩, ?_⟩
      exact hzv

/-- The component lobe interior embedded in the ambient graph. -/
def innerEmbedding (L : EndLobe C.toSimpleGraph) :
    (C.toSimpleGraph.induce (↑L.inner : Set C)) ↪g G where
  toFun z := z.1.1
  inj' := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  map_rel_iff' := Iff.rfl

omit [Fintype V] [DecidableEq V] in
theorem range_innerEmbedding
    (L : EndLobe C.toSimpleGraph) :
    Set.range (innerEmbedding C L) =
      (↑(ambientInner C L) : Set V) := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact (mem_ambientInner_iff C L z.1.1).2
      ⟨z.1, z.2, rfl⟩
  · intro hv
    obtain ⟨z, hz, hzv⟩ :=
      (mem_ambientInner_iff C L v).1 hv
    exact ⟨⟨z, hz⟩, hzv⟩

/-- Transport one end lobe from a connected component to the ambient graph. -/
noncomputable def ambientEndLobe
    (L : EndLobe C.toSimpleGraph) :
    EndLobe G where
  inner := ambientInner C L
  cut := L.cut.1
  inner_nonempty := by
    obtain ⟨z, hz⟩ := L.inner_nonempty
    exact ⟨z.1,
      (mem_ambientInner_iff C L z.1).2
        ⟨z, hz, rfl⟩⟩
  cut_not_inner := by
    intro hcut
    obtain ⟨z, hz, hzeq⟩ :=
      (mem_ambientInner_iff C L L.cut.1).1 hcut
    apply L.cut_not_inner
    have : z = L.cut :=
      Subtype.ext hzeq
    simpa [this] using hz
  block_two_connected := by
    let f := blockEmbedding C L
    have hrange :
        Set.range f =
          (↑(insert L.cut.1
            (ambientInner C L)) : Set V) := by
      simpa [f] using range_blockEmbedding C L
    let e :
        C.toSimpleGraph.induce
            (↑(insert L.cut L.inner) : Set C) ≃g
          G.induce
            (↑(insert L.cut.1
              (ambientInner C L)) : Set V) := by
      let e' := f.isoInduceRange
      rw [hrange] at e'
      exact e'
    exact L.block_two_connected.map_iso e
  inner_connected := by
    let f := innerEmbedding C L
    have hrange :
        Set.range f =
          (↑(ambientInner C L) : Set V) := by
      simpa [f] using range_innerEmbedding C L
    let e :
        C.toSimpleGraph.induce (↑L.inner : Set C) ≃g
          G.induce (↑(ambientInner C L) : Set V) := by
      let e' := f.isoInduceRange
      rw [hrange] at e'
      exact e'
    exact (SimpleGraph.Iso.connected_iff e).mp
      L.inner_connected
  closed := by
    intro u v hu huv
    obtain ⟨uC, huC, huval⟩ :=
      (mem_ambientInner_iff C L u).1 hu
    have huv' : G.Adj uC.1 v := by
      simpa [huval] using huv
    have hvC : v ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp uC.2 huv'
    let vC : C := ⟨v, hvC⟩
    have huvC : C.toSimpleGraph.Adj uC vC := huv'
    rcases L.closed huC huvC with hvInner | hvCut
    · exact Or.inl
        ((mem_ambientInner_iff C L v).2
          ⟨vC, hvInner, rfl⟩)
    · exact Or.inr (congrArg Subtype.val hvCut)

/-- Transport an end-lobe pair from a connected component to the ambient graph. -/
noncomputable def ambientEndLobePair
    (P : EndLobePair C.toSimpleGraph) :
    EndLobePair G where
  left := ambientEndLobe C P.left
  right := ambientEndLobe C P.right
  inner_disjoint := by
    apply Finset.disjoint_left.mpr
    intro v hvLeft hvRight
    obtain ⟨a, ha, hav⟩ :=
      (mem_ambientInner_iff C P.left v).1 hvLeft
    obtain ⟨b, hb, hbv⟩ :=
      (mem_ambientInner_iff C P.right v).1 hvRight
    have hab : a = b :=
      Subtype.ext (hav.trans hbv.symm)
    subst b
    exact Finset.disjoint_left.mp
      P.inner_disjoint ha hb
  left_cut_not_right_inner := by
    intro hcut
    obtain ⟨z, hz, hzeq⟩ :=
      (mem_ambientInner_iff C P.right P.left.cut.1).1
        hcut
    apply P.left_cut_not_right_inner
    have : z = P.left.cut :=
      Subtype.ext hzeq
    simpa [this] using hz
  right_cut_not_left_inner := by
    intro hcut
    obtain ⟨z, hz, hzeq⟩ :=
      (mem_ambientInner_iff C P.left P.right.cut.1).1
        hcut
    apply P.right_cut_not_left_inner
    have : z = P.right.cut :=
      Subtype.ext hzeq
    simpa [this] using hz
  connector :=
    P.connector.mapInjectiveHom
      (inclusion C).toHom
      (inclusion C).injective
  connector_avoids_left := by
    intro v hv hinner
    change v ∈
      (P.connector.walk.map
        (inclusion C).toHom).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨z, hz, hzv⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, hav⟩ :=
      (mem_ambientInner_iff C P.left v).1 hinner
    have hza : z = a :=
      Subtype.ext (hzv.trans hav.symm)
    subst a
    exact P.connector_avoids_left z hz ha
  connector_avoids_right := by
    intro v hv hinner
    change v ∈
      (P.connector.walk.map
        (inclusion C).toHom).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨z, hz, hzv⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, hav⟩ :=
      (mem_ambientInner_iff C P.right v).1 hinner
    have hza : z = a :=
      Subtype.ext (hzv.trans hav.symm)
    subst a
    exact P.connector_avoids_right z hz ha

end ConnectedComponentEndLobe

namespace ClassicalGraphTheory

/--
The component form of the two-end-lobe theorem follows from its ordinary
connected-graph form by applying it to the component graph and transporting
the result to the original carrier.
-/
theorem two_end_lobes_of_non_two_component
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C]
    (hnotTwo : ¬ IsTwoConnected C.toSimpleGraph)
    (hdegree : MinDegreeAtLeast G 3) :
    Nonempty (EndLobePair G) := by
  have hcomponentDegree :
      MinDegreeAtLeast C.toSimpleGraph 3 := by
    intro z
    have hinside :
        ∀ y, G.Adj z.1 y → y ∈ C.supp := by
      intro y hzy
      exact C.mem_supp_of_adj_mem_supp
        z.2 hzy
    exact (hdegree z.1).trans
      (finiteDegree_le_induce
        G C.supp z hinside)
  obtain ⟨P⟩ :=
    two_end_lobes
      C.toSimpleGraph C.connected_toSimpleGraph
      hnotTwo hcomponentDegree
  exact ⟨
    ConnectedComponentEndLobe.ambientEndLobePair
      C P⟩

end ClassicalGraphTheory

end DeanK5
