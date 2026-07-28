import DeanK5.Graph.CycleBlocks

/-!
# Boundary vertices of graph blocks

An edge leaving a block through one of its vertices certifies that the
attachment vertex is a cut vertex of the ambient connected graph.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace GraphBlock

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/--
If an edge of a connected graph leaves a block at `c`, then `c` is a cut
vertex of the ambient graph.
-/
theorem isCutVertex_of_adj_outside
    (hconnected : G.Connected)
    (B : GraphBlock G)
    {c a : V}
    (hc : c ∈ B.carrier)
    (hca : G.Adj c a)
    (ha : a ∉ B.carrier) :
    IsCutVertex G c := by
  by_contra hnotCut
  have hcard : 1 < B.carrier.card := by
    have := B.card_ge_two
    omega
  obtain ⟨d, hd, hdc⟩ :=
    Finset.exists_mem_ne hcard c
  letI : Nontrivial (↑B.carrier : Set V) :=
    ⟨⟨⟨c, hc⟩, ⟨d, hd⟩, by
      intro h
      exact hdc (congrArg Subtype.val h).symm⟩⟩
  letI :
      Fintype
        ((G.induce (↑B.carrier : Set V)).neighborSet
          ⟨c, hc⟩) :=
    Fintype.ofFinite _
  have hcDegree :
      0 <
        (G.induce (↑B.carrier : Set V)).degree
          ⟨c, hc⟩ :=
    B.connected.preconnected.degree_pos_of_nontrivial ⟨c, hc⟩
  obtain ⟨v, hcvInduced⟩ :=
    ((G.induce (↑B.carrier : Set V)).degree_pos_iff_exists_adj
      ⟨c, hc⟩).1 hcDegree
  have hcv : G.Adj c v.1 :=
    hcvInduced
  have hav : a ≠ v.1 := by
    intro hav
    apply ha
    rw [hav]
    exact v.2
  have hsurvives : Nonempty {w : V // w ≠ c} :=
    ⟨⟨a, hca.ne.symm⟩⟩
  have hdelete :
      (deleteVertices G {c}).Connected :=
    (not_isCutVertex_iff_delete_connected
      G c hconnected hsurvives).1 hnotCut
  let a' : {w : V // w ∉ ({c} : Finset V)} :=
    ⟨a, by simpa using hca.ne.symm⟩
  let v' : {w : V // w ∉ ({c} : Finset V)} :=
    ⟨v.1, by simpa using hcv.ne.symm⟩
  obtain ⟨p, hp⟩ :=
    hdelete.preconnected.exists_isPath a' v'
  let inclusion :
      deleteVertices G {c} →g G :=
    (Embedding.induce
      {w : V | w ∉ ({c} : Finset V)}).toHom
  let P : SimplePath G a v.1 := {
    walk := p.map inclusion
    isPath := hp.map (by
      intro x y hxy
      exact Subtype.ext hxy)
  }
  have hcAvoid : c ∉ P.walk.support := by
    intro hmem
    change c ∈ (p.map inclusion).support at hmem
    rw [SimpleGraph.Walk.support_map] at hmem
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hmem
    change w.1 = c at hw
    have hwc : w.1 ≠ c := by
      simpa using w.2
    exact hwc hw
  obtain ⟨C, hcC, haC, hvC, -⟩ :=
    GraphBlock.exists_containing_center_and_path_ends
      hav hca hcv P hcAvoid
  have hBC : B = C := by
    by_contra hne
    have hinterCard :
        2 ≤ (B.carrier ∩ C.carrier).card := by
      have hpair :
          ({c, v.1} : Finset V) ⊆
            B.carrier ∩ C.carrier := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hc, hcC⟩
        · exact Finset.mem_inter.mpr ⟨v.2, hvC⟩
      have hpairCard :
          ({c, v.1} : Finset V).card = 2 := by
        simp [hcv.ne]
      rw [← hpairCard]
      exact Finset.card_le_card hpair
    exact
      (not_le_of_gt hinterCard)
        (GraphBlock.inter_card_le_one B C hne)
  apply ha
  rw [hBC]
  exact haC

end GraphBlock

end DeanK5
