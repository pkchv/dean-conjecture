import DeanK5.Graph.BlockBoundary

/-!
# Intersections of distinct graph blocks

Distinct blocks share at most one vertex.  In a connected graph, any vertex
they do share is a cut vertex: a neighbor of that vertex inside either block
but outside the other witnesses an edge leaving the other block.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace GraphBlock

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
A common vertex of two distinct blocks in a connected graph is a cut
vertex.
-/
theorem isCutVertex_of_mem_inter
    (hconnected : G.Connected)
    (B C : GraphBlock G)
    (hne : B ≠ C)
    {c : V}
    (hcB : c ∈ B.carrier)
    (hcC : c ∈ C.carrier) :
    IsCutVertex G c := by
  have hcard : 1 < C.carrier.card := by
    have := C.card_ge_two
    omega
  obtain ⟨d, hdC, hdc⟩ :=
    Finset.exists_mem_ne hcard c
  letI : Nontrivial (↑C.carrier : Set V) :=
    ⟨⟨⟨c, hcC⟩, ⟨d, hdC⟩, by
      intro h
      exact hdc (congrArg Subtype.val h).symm⟩⟩
  letI :
      Fintype
        ((G.induce (↑C.carrier : Set V)).neighborSet
          ⟨c, hcC⟩) :=
    Fintype.ofFinite _
  have hcDegree :
      0 <
        (G.induce (↑C.carrier : Set V)).degree
          ⟨c, hcC⟩ :=
    C.connected.preconnected.degree_pos_of_nontrivial
      ⟨c, hcC⟩
  obtain ⟨a, hcaInduced⟩ :=
    ((G.induce (↑C.carrier : Set V)).degree_pos_iff_exists_adj
      ⟨c, hcC⟩).1 hcDegree
  have hca : G.Adj c a.1 :=
    hcaInduced
  have haNotB : a.1 ∉ B.carrier := by
    intro haB
    have hpair :
        ({c, a.1} : Finset V) ⊆
          B.carrier ∩ C.carrier := by
      intro v hv
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hcB, hcC⟩
      · exact Finset.mem_inter.mpr ⟨haB, a.2⟩
    have hpairCard :
        ({c, a.1} : Finset V).card = 2 := by
      simp [hca.ne]
    have hinterTwo :
        2 ≤ (B.carrier ∩ C.carrier).card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpair
    exact
      (not_le_of_gt hinterTwo)
        (B.inter_card_le_one C hne)
  exact
    B.isCutVertex_of_adj_outside
      hconnected hcB hca haNotB

omit [Fintype V] in
/--
If two distinct blocks share a specified vertex, their carrier
intersection is exactly that singleton.
-/
theorem inter_eq_singleton_of_mem_of_ne
    (B C : GraphBlock G)
    (hne : B ≠ C)
    {c : V}
    (hcB : c ∈ B.carrier)
    (hcC : c ∈ C.carrier) :
    B.carrier ∩ C.carrier = {c} := by
  apply Finset.Subset.antisymm
  · intro v hv
    have hinterCard :
        (B.carrier ∩ C.carrier).card ≤ 1 :=
      B.inter_card_le_one C hne
    have hcInter :
        c ∈ B.carrier ∩ C.carrier :=
      Finset.mem_inter.mpr ⟨hcB, hcC⟩
    have hvc : v = c :=
      Finset.card_le_one.mp hinterCard
        v hv c hcInter
    simp [hvc]
  · intro v hv
    have hvc : v = c := by
      simpa using hv
    subst v
    exact Finset.mem_inter.mpr ⟨hcB, hcC⟩

/--
Every cut vertex of a finite connected graph belongs to at least two
distinct blocks.
-/
theorem exists_two_distinct_of_isCutVertex
    (hconnected : G.Connected)
    {c : V}
    (hcut : IsCutVertex G c) :
    ∃ B C : GraphBlock G,
      B ≠ C ∧
        c ∈ B.carrier ∧
        c ∈ C.carrier := by
  classical
  have hvertexCut :
      IsVertexCut G {c} :=
    (isCutVertex_iff_isVertexCut
      G c hconnected.preconnected).1 hcut
  obtain ⟨Q, R, hQR⟩ := hvertexCut
  let regionQ :
      ComponentRegion G {c}
        (componentVertices G {c} Q) :=
    componentRegion_componentVertices G {c} Q
  let regionR :
      ComponentRegion G {c}
        (componentVertices G {c} R) :=
    componentRegion_componentVertices G {c} R
  obtain ⟨q, hqQ⟩ := regionQ.nonempty
  obtain ⟨r, hrR⟩ := regionR.nonempty
  obtain ⟨pathQ⟩ :=
    hconnected.preconnected q c
  obtain ⟨a, haQ, -, s, hs, -, has⟩ :=
    regionQ.exists_boundary_edge_of_walk
      hqQ (by simp) pathQ
  have hsc : s = c := by
    simpa using hs
  subst s
  obtain ⟨pathR⟩ :=
    hconnected.preconnected r c
  obtain ⟨d, hdR, -, t, ht, -, hdt⟩ :=
    regionR.exists_boundary_edge_of_walk
      hrR (by simp) pathR
  have htc : t = c := by
    simpa using ht
  subst t
  obtain ⟨B, haB, hcB⟩ :=
    GraphBlock.exists_of_adj has
  obtain ⟨C, hdC, hcC⟩ :=
    GraphBlock.exists_of_adj hdt
  have hBC : B ≠ C := by
    intro h
    subst C
    have haNeC : a ≠ c := by
      intro hac
      exact regionQ.not_mem_separator haQ
        (by simp [hac])
    have hdNeC : d ≠ c := by
      intro hdc
      exact regionR.not_mem_separator hdR
        (by simp [hdc])
    let aB : (↑(B.carrier.erase c) : Set V) :=
      ⟨a, Finset.mem_erase.mpr ⟨haNeC, haB⟩⟩
    let dB : (↑(B.carrier.erase c) : Set V) :=
      ⟨d, Finset.mem_erase.mpr ⟨hdNeC, hdC⟩⟩
    have hreachB :=
      (B.delete_connected hcB).preconnected aB dB
    have hsubset :
        (↑(B.carrier.erase c) : Set V) ⊆
          {v : V | v ∉ ({c} : Finset V)} := by
      intro v hv
      have hvc :
          v ≠ c :=
        (Finset.mem_erase.mp hv).1
      simpa using hvc
    have hreachDeleted :=
      hreachB.map (G.induceHomOfLE hsubset).toHom
    have haComponent :=
      (mem_componentVertices_iff
        G {c} Q a).1 haQ
    have hdComponent :=
      (mem_componentVertices_iff
        G {c} R d).1 hdR
    have hcomponents :
        Q = R := by
      calc
        Q =
            (deleteVertices G {c}).connectedComponentMk
              ⟨a, haComponent.1⟩ :=
          haComponent.2.symm
        _ =
            (deleteVertices G {c}).connectedComponentMk
              ⟨d, hdComponent.1⟩ := by
          apply SimpleGraph.ConnectedComponent.sound
          convert hreachDeleted using 1 <;>
            apply Subtype.ext <;> rfl
        _ = R :=
          hdComponent.2
    exact hQR hcomponents
  exact ⟨B, C, hBC, hcB, hcC⟩

/--
Every vertex of a finite connected graph of order at least two belongs to
some block.
-/
theorem exists_of_vertex
    (hconnected : G.Connected)
    (horder : 2 ≤ Fintype.card V)
    (v : V) :
    ∃ B : GraphBlock G, v ∈ B.carrier := by
  letI : Nontrivial V := by
    exact Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Fintype (G.neighborSet v) :=
    Fintype.ofFinite _
  have hdegree :
      0 < G.degree v :=
    hconnected.preconnected.degree_pos_of_nontrivial v
  obtain ⟨w, hvw⟩ :=
    (G.degree_pos_iff_exists_adj v).1 hdegree
  obtain ⟨B, hvB, -⟩ :=
    GraphBlock.exists_of_adj hvw
  exact ⟨B, hvB⟩

end GraphBlock

end DeanK5
