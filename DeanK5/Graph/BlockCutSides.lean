import DeanK5.Graph.FeasibleBlocks

/-!
# Deletion sides attached to a graph block

For a block `B` and a vertex `c ∈ B`, the connected subgraph
`B - c` lies in one distinguished component of `G - c`.  We call this the
main deletion component.  All other deletion components are off components
attached to `B` at `c`.

When the ambient graph is connected, off components attached at distinct
cut vertices of one block are disjoint.  This separation supplies the
injection used to show that a graph with at most two marked vertices and no
feasible block has no block of order at least three.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace GraphBlock

variable [DecidableEq V]
  {G : SimpleGraph V}

/--
A deterministic carrier vertex different from `c`, used only to name the
component of `G - c` containing the rest of the block.
-/
private noncomputable def blockDeleteAnchor
    (B : GraphBlock G) (c : V) (hc : c ∈ B.carrier) :
    (↑(B.carrier.erase c) : Set V) := by
  have hnonempty :
      (B.carrier.erase c).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hc]
    have hcard := B.card_ge_two
    omega
  exact ⟨hnonempty.choose, hnonempty.choose_spec⟩

/--
The main component of `G - c` determined by a block `B`: the component
containing `B - c`.
-/
noncomputable def mainDeletionComponent
    (B : GraphBlock G) (c : V) (hc : c ∈ B.carrier) :
    (deleteVertices G {c}).ConnectedComponent :=
  (deleteVertices G {c}).connectedComponentMk
    ⟨(blockDeleteAnchor B c hc).1, by
      have hne :
          (blockDeleteAnchor B c hc).1 ≠ c :=
        (Finset.mem_erase.mp
          (blockDeleteAnchor B c hc).2).1
      simpa using hne⟩

section Finite

variable [Fintype V]

/--
Every block vertex other than `c` belongs to the main component of
`G - c`.
-/
theorem mem_mainDeletionComponent
    (B : GraphBlock G) {c v : V}
    (hc : c ∈ B.carrier)
    (hv : v ∈ B.carrier) (hvc : v ≠ c) :
    v ∈ componentVertices G {c}
      (B.mainDeletionComponent c hc) := by
  have hvErase :
      v ∈ B.carrier.erase c :=
    Finset.mem_erase.mpr ⟨hvc, hv⟩
  let aB : (↑(B.carrier.erase c) : Set V) :=
    blockDeleteAnchor B c hc
  let vB : (↑(B.carrier.erase c) : Set V) :=
    ⟨v, hvErase⟩
  have hsubset :
      (↑(B.carrier.erase c) : Set V) ⊆
        {w : V | w ∉ ({c} : Finset V)} := by
    intro w hw
    have hwc : w ≠ c :=
      (Finset.mem_erase.mp hw).1
    simpa using hwc
  have hreach :=
    (B.delete_connected hc).preconnected aB vB
  have hmapped :=
    hreach.map (G.induceHomOfLE hsubset).toHom
  have haEq :
      (G.induceHomOfLE hsubset) aB =
        ⟨(blockDeleteAnchor B c hc).1, by
          have hne :
              (blockDeleteAnchor B c hc).1 ≠ c :=
            (Finset.mem_erase.mp
              (blockDeleteAnchor B c hc).2).1
          simpa using hne⟩ := by
    apply Subtype.ext
    rfl
  have hvEq :
      (G.induceHomOfLE hsubset) vB =
        ⟨v, by simpa using hvc⟩ := by
    apply Subtype.ext
    rfl
  have hcomponent :
      (deleteVertices G {c}).connectedComponentMk
          ⟨v, by simpa using hvc⟩ =
        B.mainDeletionComponent c hc := by
    rw [mainDeletionComponent]
    exact
      (SimpleGraph.ConnectedComponent.sound
        (by simpa [haEq, hvEq] using hmapped)).symm
  apply (mem_componentVertices_iff
    G {c} (B.mainDeletionComponent c hc) v).2
  exact ⟨by simpa using hvc, by
    change
      (deleteVertices G {c}).connectedComponentMk
          ⟨v, by simpa using hvc⟩ =
        B.mainDeletionComponent c hc
    exact hcomponent⟩

end Finite

/-- An off component is any deletion component other than the main one. -/
def IsOffDeletionComponent
    (B : GraphBlock G) {c : V}
    (hc : c ∈ B.carrier)
    (Q : (deleteVertices G {c}).ConnectedComponent) : Prop :=
  Q ≠ B.mainDeletionComponent c hc

/--
A global cut vertex of a block has at least one off deletion component.
-/
theorem exists_offDeletionComponent
    (hconnected : G.Connected)
    (B : GraphBlock G) {c : V}
    (hc : c ∈ B.carrier)
    (hcut : IsCutVertex G c) :
    ∃ Q : (deleteVertices G {c}).ConnectedComponent,
      B.IsOffDeletionComponent hc Q := by
  have hvertexCut :
      IsVertexCut G {c} :=
    (isCutVertex_iff_isVertexCut
      G c hconnected.preconnected).1 hcut
  obtain ⟨Q, hQ⟩ :=
    hvertexCut.exists_other_component
      (B.mainDeletionComponent c hc)
  exact ⟨Q, hQ⟩

/--
A canonical off component at a global cut vertex of a block.
-/
noncomputable def offDeletionComponent
    (hconnected : G.Connected)
    (B : GraphBlock G) (c : V)
    (hc : c ∈ B.carrier)
    (hcut : IsCutVertex G c) :
    (deleteVertices G {c}).ConnectedComponent :=
  Classical.choose
    (B.exists_offDeletionComponent
      hconnected hc hcut)

/-- The canonical off component is not the main component. -/
theorem offDeletionComponent_isOff
    (hconnected : G.Connected)
    (B : GraphBlock G) (c : V)
    (hc : c ∈ B.carrier)
    (hcut : IsCutVertex G c) :
    B.IsOffDeletionComponent hc
      (B.offDeletionComponent
        hconnected c hc hcut) :=
  Classical.choose_spec
    (B.exists_offDeletionComponent
      hconnected hc hcut)

section Finite

variable [Fintype V]

/--
An off component at `c` contains no vertex of the block that determines its
main component.
-/
theorem componentVertices_disjoint_carrier_of_isOff
    (B : GraphBlock G) {c : V}
    (hc : c ∈ B.carrier)
    {Q : (deleteVertices G {c}).ConnectedComponent}
    (hQoff : B.IsOffDeletionComponent hc Q) :
    Disjoint (componentVertices G {c} Q)
      B.carrier := by
  apply Finset.disjoint_left.mpr
  intro v hvQ hvB
  obtain ⟨hvNotDeleted, -⟩ :=
    (mem_componentVertices_iff G {c} Q v).1 hvQ
  have hvc : v ≠ c := by
    simpa using hvNotDeleted
  have hvMain :
      v ∈ componentVertices G {c}
        (B.mainDeletionComponent c hc) :=
    B.mem_mainDeletionComponent hc hvB hvc
  exact
    Finset.disjoint_left.mp
      (componentVertices_disjoint_of_ne
        G {c} hQoff)
      hvQ hvMain

/--
Off components attached at distinct vertices of one block have disjoint
original-carrier vertex sets.
-/
theorem componentVertices_disjoint_of_isOff_of_ne
    (hconnected : G.Connected)
    (B : GraphBlock G)
    {c d : V}
    (hc : c ∈ B.carrier)
    (hd : d ∈ B.carrier)
    (hcd : c ≠ d)
    {Q : (deleteVertices G {c}).ConnectedComponent}
    (hQoff : B.IsOffDeletionComponent hc Q)
    {R : (deleteVertices G {d}).ConnectedComponent}
    (hRoff : B.IsOffDeletionComponent hd R) :
    Disjoint (componentVertices G {c} Q)
      (componentVertices G {d} R) := by
  apply Finset.disjoint_left.mpr
  intro x hxQ hxR
  have hdMain :
      d ∈ componentVertices G {c}
        (B.mainDeletionComponent c hc) :=
    B.mem_mainDeletionComponent
      hc hd hcd.symm
  have hdNotQ :
      d ∉ componentVertices G {c} Q := by
    intro hdQ
    exact
      Finset.disjoint_left.mp
        (componentVertices_disjoint_of_ne
          G {c} hQoff)
        hdQ hdMain
  have hside :=
    componentRegion_componentVertices
      G {c} Q
  have hsideConnected :
      (G.induce
        (↑(insert c (componentVertices G {c} Q)) :
          Set V)).Connected :=
    hside.connected_insert_singleton_of_connected
      hconnected
  have hsubset :
      (↑(insert c (componentVertices G {c} Q)) :
          Set V) ⊆
        {w : V | w ∉ ({d} : Finset V)} := by
    intro w hw
    have hwCases :
        w = c ∨
          w ∈ componentVertices G {c} Q := by
      simpa using hw
    rcases hwCases with rfl | hwQ
    · simpa using hcd
    · have hwd : w ≠ d := by
        intro h
        exact hdNotQ (h ▸ hwQ)
      simpa using hwd
  let xI :
      (↑(insert c (componentVertices G {c} Q)) :
        Set V) :=
    ⟨x, by simp [hxQ]⟩
  let cI :
      (↑(insert c (componentVertices G {c} Q)) :
        Set V) :=
    ⟨c, by simp⟩
  obtain ⟨hxNotD, -⟩ :=
    (mem_componentVertices_iff
      G {d} R x).1 hxR
  let xD :
      {w : V // w ∉ ({d} : Finset V)} :=
    ⟨x, hxNotD⟩
  let cD :
      {w : V // w ∉ ({d} : Finset V)} :=
    ⟨c, by simpa using hcd⟩
  have hreachMapped :=
    (hsideConnected.preconnected xI cI).map
      (G.induceHomOfLE hsubset).toHom
  have hxEq :
      (G.induceHomOfLE hsubset) xI = xD := by
    apply Subtype.ext
    rfl
  have hcEq :
      (G.induceHomOfLE hsubset) cI = cD := by
    apply Subtype.ext
    rfl
  have hreachXC :
      (deleteVertices G {d}).Reachable xD cD := by
    simpa [hxEq, hcEq] using hreachMapped
  have hcMain :
      c ∈ componentVertices G {d}
        (B.mainDeletionComponent d hd) :=
    B.mem_mainDeletionComponent
      hd hc hcd
  obtain ⟨hcNotD, hcSuppMain⟩ :=
    (mem_componentVertices_iff
      G {d} (B.mainDeletionComponent d hd) c).1
      hcMain
  have hcComponentEqRaw :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff
      (B.mainDeletionComponent d hd)
      ⟨c, hcNotD⟩).1 hcSuppMain
  have hcComponentEq :
      (deleteVertices G {d}).connectedComponentMk cD =
        B.mainDeletionComponent d hd := by
    simpa [cD] using hcComponentEqRaw
  have hxMain :
      x ∈ componentVertices G {d}
        (B.mainDeletionComponent d hd) := by
    apply (mem_componentVertices_iff
      G {d} (B.mainDeletionComponent d hd) x).2
    refine ⟨hxNotD, ?_⟩
    change
      (deleteVertices G {d}).connectedComponentMk xD =
        B.mainDeletionComponent d hd
    exact
      (SimpleGraph.ConnectedComponent.sound
        hreachXC).trans hcComponentEq
  exact
    Finset.disjoint_left.mp
      (componentVertices_disjoint_of_ne
        G {d} hRoff)
      hxR hxMain

end Finite

section MarkedSelection

variable [Fintype V]

/--
A marked vertex selected from the canonical off component at a block cut
vertex, under the hypothesis that no feasible block exists.
-/
noncomputable def offMarkedVertex
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ C : GraphBlock G,
        ¬IsFeasibleBlock G marked C)
    (B : GraphBlock G) (c : V)
    (hc : c ∈ B.carrier)
    (hcut : IsCutVertex G c) : V :=
  Classical.choose
    (deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible c
      (B.offDeletionComponent
        hconnected c hc hcut))

/-- The selected off-side vertex is marked. -/
theorem offMarkedVertex_mem_marked
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ C : GraphBlock G,
        ¬IsFeasibleBlock G marked C)
    (B : GraphBlock G) (c : V)
    (hc : c ∈ B.carrier)
    (hcut : IsCutVertex G c) :
    B.offMarkedVertex
      hconnected marked hnoFeasible c hc hcut ∈ marked :=
  (Classical.choose_spec
    (deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible c
      (B.offDeletionComponent
        hconnected c hc hcut))).1

/-- The selected vertex lies in the canonical off component. -/
theorem offMarkedVertex_mem_component
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ C : GraphBlock G,
        ¬IsFeasibleBlock G marked C)
    (B : GraphBlock G) (c : V)
    (hc : c ∈ B.carrier)
    (hcut : IsCutVertex G c) :
    B.offMarkedVertex
        hconnected marked hnoFeasible c hc hcut ∈
      componentVertices G {c}
        (B.offDeletionComponent
          hconnected c hc hcut) :=
  (Classical.choose_spec
    (deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible c
      (B.offDeletionComponent
        hconnected c hc hcut))).2

/-- The selected off-side marked vertex does not belong to the block. -/
theorem offMarkedVertex_not_mem_carrier
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ C : GraphBlock G,
        ¬IsFeasibleBlock G marked C)
    (B : GraphBlock G) (c : V)
    (hc : c ∈ B.carrier)
    (hcut : IsCutVertex G c) :
    B.offMarkedVertex
      hconnected marked hnoFeasible c hc hcut ∉
        B.carrier := by
  intro hcarrier
  exact
    Finset.disjoint_left.mp
      (B.componentVertices_disjoint_carrier_of_isOff hc
        (B.offDeletionComponent_isOff
          hconnected c hc hcut))
      (B.offMarkedVertex_mem_component
        hconnected marked hnoFeasible c hc hcut)
      hcarrier

/--
Distinct global cut vertices in one block select distinct marked vertices
outside the block.
-/
theorem offMarkedVertex_injective
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ C : GraphBlock G,
        ¬IsFeasibleBlock G marked C)
    (B : GraphBlock G) :
    Function.Injective
      (fun c : ↑(B.carrier ∩ cutVertices G) =>
        B.offMarkedVertex hconnected marked hnoFeasible
          c.1
          (Finset.mem_inter.mp c.2).1
          (by simpa using
            (Finset.mem_inter.mp c.2).2)) := by
  intro c d hselected
  apply Subtype.ext
  by_contra hcd
  have hcCarrier :
      c.1 ∈ B.carrier :=
    (Finset.mem_inter.mp c.2).1
  have hdCarrier :
      d.1 ∈ B.carrier :=
    (Finset.mem_inter.mp d.2).1
  have hcCut :
      IsCutVertex G c.1 := by
    simpa using (Finset.mem_inter.mp c.2).2
  have hdCut :
      IsCutVertex G d.1 := by
    simpa using (Finset.mem_inter.mp d.2).2
  have hdisjoint :=
    B.componentVertices_disjoint_of_isOff_of_ne
      hconnected hcCarrier hdCarrier hcd
      (B.offDeletionComponent_isOff
        hconnected c.1 hcCarrier hcCut)
      (B.offDeletionComponent_isOff
        hconnected d.1 hdCarrier hdCut)
  have hcSide :=
    B.offMarkedVertex_mem_component
      hconnected marked hnoFeasible
      c.1 hcCarrier hcCut
  have hdSide :=
    B.offMarkedVertex_mem_component
      hconnected marked hnoFeasible
      d.1 hdCarrier hdCut
  have hselected' :
      B.offMarkedVertex hconnected marked hnoFeasible
          c.1 hcCarrier hcCut =
        B.offMarkedVertex hconnected marked hnoFeasible
          d.1 hdCarrier hdCut := by
    simpa using hselected
  apply Finset.disjoint_left.mp hdisjoint hcSide
  rw [hselected']
  exact hdSide

/--
Under the no-feasible-block hypothesis, the global cut vertices in a block
inject into the marked vertices outside that block.
-/
theorem cutVertices_card_le_marked_sdiff
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ C : GraphBlock G,
        ¬IsFeasibleBlock G marked C)
    (B : GraphBlock G) :
    (B.carrier ∩ cutVertices G).card ≤
      (marked \ B.carrier).card := by
  let f :
      ↑(B.carrier ∩ cutVertices G) →
        ↑(marked \ B.carrier) :=
    fun c =>
      ⟨B.offMarkedVertex hconnected marked hnoFeasible
          c.1
          (Finset.mem_inter.mp c.2).1
          (by simpa using
            (Finset.mem_inter.mp c.2).2),
        Finset.mem_sdiff.mpr ⟨
          B.offMarkedVertex_mem_marked
            hconnected marked hnoFeasible
            c.1
            (Finset.mem_inter.mp c.2).1
            (by simpa using
              (Finset.mem_inter.mp c.2).2),
          B.offMarkedVertex_not_mem_carrier
            hconnected marked hnoFeasible
            c.1
            (Finset.mem_inter.mp c.2).1
            (by simpa using
              (Finset.mem_inter.mp c.2).2)⟩⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply B.offMarkedVertex_injective
      hconnected marked hnoFeasible
    exact congrArg Subtype.val hcd
  exact Finset.card_le_card_of_injective hf

end MarkedSelection

end GraphBlock

/--
If at most two vertices are marked and no feasible block exists, every
graph block has at most two vertices.

The proof counts cut vertices of the block by distinct marked witnesses in
off components.  Marked vertices lying in the block are counted separately,
so the argument does not assume that marked vertices and cut vertices are
disjoint.
-/
theorem graphBlock_card_le_two_of_no_feasibleBlock
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (B : GraphBlock G) :
    B.carrier.card ≤ 2 := by
  by_contra hnot
  have hthree :
      3 ≤ B.carrier.card := by
    omega
  have hcutBound :
      (B.carrier ∩ cutVertices G).card ≤
        (marked \ B.carrier).card :=
    B.cutVertices_card_le_marked_sdiff
      hconnected marked hnoFeasible
  have hspecialEq :
      B.carrier ∩ (cutVertices G ∪ marked) =
        (B.carrier ∩ cutVertices G) ∪
          (B.carrier ∩ marked) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hspecialCard :
      (B.carrier ∩
        (cutVertices G ∪ marked)).card ≤ 2 := by
    calc
      (B.carrier ∩
          (cutVertices G ∪ marked)).card =
          ((B.carrier ∩ cutVertices G) ∪
            (B.carrier ∩ marked)).card :=
        congrArg Finset.card hspecialEq
      _ ≤
          (B.carrier ∩ cutVertices G).card +
            (B.carrier ∩ marked).card :=
        Finset.card_union_le _ _
      _ ≤
          (marked \ B.carrier).card +
            (B.carrier ∩ marked).card :=
        Nat.add_le_add_right hcutBound _
      _ = marked.card := by
        rw [Finset.inter_comm B.carrier marked]
        exact
          Finset.card_sdiff_add_card_inter
            marked B.carrier
      _ ≤ 2 := hmarked
  have hordinary :
      (B.carrier \
        (cutVertices G ∪ marked)).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro hsubset
    have hinterEq :
        B.carrier ∩
          (cutVertices G ∪ marked) =
            B.carrier :=
      Finset.inter_eq_left.mpr hsubset
    rw [hinterEq] at hspecialCard
    omega
  exact
    hnoFeasible B
      ⟨hspecialCard, hordinary⟩

end DeanK5
