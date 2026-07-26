import DeanK5.Published
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The one-subdivision of `K₄`

This module proves the paper's subdivision-attachment lemma internally.  It
constructs the relevant path in the canonical one-subdivision, maps it
through the supplied copy, closes it through the outside vertex, and applies
the girth hypothesis.  The same canonical configuration appears in GHLM
Lemma 5.9.
-/

open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace SubdivisionK4

private def edgeOfNe (x y : Fin 4) (hxy : x ≠ y) : K4Edge :=
  ⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet]⟩

@[simp] private theorem edgeOfNe_val
    (x y : Fin 4) (hxy : x ≠ y) :
    (edgeOfNe x y hxy : Sym2 (Fin 4)) = s(x, y) :=
  rfl

private theorem branch_edge_adj_of_mem
    (x : Fin 4) (e : K4Edge) (hx : x ∈ (e : Sym2 (Fin 4))) :
    oneSubdivisionK4.Adj (Sum.inl x) (Sum.inr e) := by
  exact hx

private theorem edge_branch_adj_of_mem
    (x : Fin 4) (e : K4Edge) (hx : x ∈ (e : Sym2 (Fin 4))) :
    oneSubdivisionK4.Adj (Sum.inr e) (Sum.inl x) := by
  exact hx

/-- The two-edge route between distinct branch vertices. -/
private def branchBranchPath
    (x y : Fin 4) (hxy : x ≠ y) :
    SimplePath oneSubdivisionK4 (Sum.inl x) (Sum.inl y) := {
  walk :=
    .cons
      (branch_edge_adj_of_mem x (edgeOfNe x y hxy)
        (by simp))
      (.cons
        (edge_branch_adj_of_mem y (edgeOfNe x y hxy)
          (by simp))
        .nil)
  isPath := by
    simp [hxy]
}

@[simp] private theorem branchBranchPath_length
    (x y : Fin 4) (hxy : x ≠ y) :
    (branchBranchPath x y hxy).length = 2 := by
  simp [branchBranchPath, SimplePath.length]

/-- A branch vertex is adjacent to each incident subdivision vertex. -/
private def branchEdgePath
    (x : Fin 4) (e : K4Edge)
    (hx : x ∈ (e : Sym2 (Fin 4))) :
    SimplePath oneSubdivisionK4 (Sum.inl x) (Sum.inr e) :=
  SimplePath.ofAdj (branch_edge_adj_of_mem x e hx)

/--
If a branch vertex is not incident with an edge, route through the first
endpoint of that edge.  The route has three edges.
-/
private noncomputable def branchEdgePathThree
    (x : Fin 4) (e : K4Edge)
    (hx : x ∉ (e : Sym2 (Fin 4))) :
    SimplePath oneSubdivisionK4 (Sum.inl x) (Sum.inr e) := by
  let y : Fin 4 := (e : Sym2 (Fin 4)).out.1
  have hy : y ∈ (e : Sym2 (Fin 4)) :=
    Sym2.out_fst_mem _
  have hxy : x ≠ y := fun h => hx (h ▸ hy)
  let xy := edgeOfNe x y hxy
  have hxyEdge : xy ≠ e := by
    intro h
    apply hx
    rw [← h]
    simp [xy]
  exact {
    walk :=
      .cons
        (branch_edge_adj_of_mem x xy (by simp [xy]))
        (.cons
          (edge_branch_adj_of_mem y xy (by simp [xy]))
          (.cons (branch_edge_adj_of_mem y e hy) .nil))
    isPath := by
      simp [xy, hxy, hxyEdge, y]
  }

@[simp] private theorem branchEdgePathThree_length
    (x : Fin 4) (e : K4Edge)
    (hx : x ∉ (e : Sym2 (Fin 4))) :
    (branchEdgePathThree x e hx).length = 3 := by
  simp [branchEdgePathThree, SimplePath.length]

/-- The two-edge route between subdivision vertices sharing an endpoint. -/
private def edgeEdgePath
    (e f : K4Edge) (hef : e ≠ f)
    (x : Fin 4)
    (hxe : x ∈ (e : Sym2 (Fin 4)))
    (hxf : x ∈ (f : Sym2 (Fin 4))) :
    SimplePath oneSubdivisionK4 (Sum.inr e) (Sum.inr f) := {
  walk :=
    .cons (edge_branch_adj_of_mem x e hxe)
      (.cons (branch_edge_adj_of_mem x f hxf) .nil)
  isPath := by
    simp [hef]
}

@[simp] private theorem edgeEdgePath_length
    (e f : K4Edge) (hef : e ≠ f)
    (x : Fin 4)
    (hxe : x ∈ (e : Sym2 (Fin 4)))
    (hxf : x ∈ (f : Sym2 (Fin 4))) :
    (edgeEdgePath e f hef x hxe hxf).length = 2 := by
  simp [edgeEdgePath, SimplePath.length]

private theorem k4Edge_ne_of_mem_not_mem
    {e f : K4Edge} {x : Fin 4}
    (hxe : x ∈ (e : Sym2 (Fin 4)))
    (hxf : x ∉ (f : Sym2 (Fin 4))) :
    e ≠ f := by
  intro h
  exact hxf (h ▸ hxe)

/--
Opposite subdivision vertices are joined by an eight-edge simple path.
Together with an outside common neighbor, this is the required 10-cycle.
-/
private noncomputable def edgeEdgePathEight
    (e f : K4Edge)
    (hdisj :
      Disjoint
        ((e : Sym2 (Fin 4)) : Set (Fin 4))
        ((f : Sym2 (Fin 4)) : Set (Fin 4))) :
    SimplePath oneSubdivisionK4 (Sum.inr e) (Sum.inr f) := by
  let x : Fin 4 := (e : Sym2 (Fin 4)).out.1
  let y : Fin 4 := (e : Sym2 (Fin 4)).out.2
  let z : Fin 4 := (f : Sym2 (Fin 4)).out.1
  let w : Fin 4 := (f : Sym2 (Fin 4)).out.2
  have hxE : x ∈ (e : Sym2 (Fin 4)) :=
    Sym2.out_fst_mem _
  have hyE : y ∈ (e : Sym2 (Fin 4)) :=
    Sym2.out_snd_mem _
  have hzF : z ∈ (f : Sym2 (Fin 4)) :=
    Sym2.out_fst_mem _
  have hwF : w ∈ (f : Sym2 (Fin 4)) :=
    Sym2.out_snd_mem _
  have hxF : x ∉ (f : Sym2 (Fin 4)) :=
    Set.disjoint_left.mp hdisj hxE
  have hyF : y ∉ (f : Sym2 (Fin 4)) :=
    Set.disjoint_left.mp hdisj hyE
  have hzE : z ∉ (e : Sym2 (Fin 4)) := by
    intro hz
    exact Set.disjoint_left.mp hdisj hz hzF
  have hwE : w ∉ (e : Sym2 (Fin 4)) := by
    intro hw
    exact Set.disjoint_left.mp hdisj hw hwF
  have hxy : x ≠ y := by
    intro h
    apply (completeGraph (Fin 4)).not_isDiag_of_mem_edgeSet e.property
    rw [show (e : Sym2 (Fin 4)) =
      s((e : Sym2 (Fin 4)).out.1,
        (e : Sym2 (Fin 4)).out.2) from
      (e : Sym2 (Fin 4)).out_eq.symm]
    exact h
  have hzw : z ≠ w := by
    intro h
    apply (completeGraph (Fin 4)).not_isDiag_of_mem_edgeSet f.property
    rw [show (f : Sym2 (Fin 4)) =
      s((f : Sym2 (Fin 4)).out.1,
        (f : Sym2 (Fin 4)).out.2) from
      (f : Sym2 (Fin 4)).out_eq.symm]
    exact h
  have hxz : x ≠ z := fun h => hxF (h ▸ hzF)
  have hxw : x ≠ w := fun h => hxF (h ▸ hwF)
  have hyz : y ≠ z := fun h => hyF (h ▸ hzF)
  have hyw : y ≠ w := fun h => hyF (h ▸ hwF)
  have hzy : z ≠ y := hyz.symm
  let xz := edgeOfNe x z hxz
  let yz := edgeOfNe y z hyz
  let yw := edgeOfNe y w hyw
  have hx_xz : x ∈ (xz : Sym2 (Fin 4)) := by simp [xz]
  have hz_xz : z ∈ (xz : Sym2 (Fin 4)) := by simp [xz]
  have hy_yz : y ∈ (yz : Sym2 (Fin 4)) := by simp [yz]
  have hz_yz : z ∈ (yz : Sym2 (Fin 4)) := by simp [yz]
  have hy_yw : y ∈ (yw : Sym2 (Fin 4)) := by simp [yw]
  have hw_yw : w ∈ (yw : Sym2 (Fin 4)) := by simp [yw]
  have hx_not_yz : x ∉ (yz : Sym2 (Fin 4)) := by
    simp [yz, hxy, hxz]
  have hx_not_yw : x ∉ (yw : Sym2 (Fin 4)) := by
    simp [yw, hxy, hxw]
  have hz_not_yw : z ∉ (yw : Sym2 (Fin 4)) := by
    simp [yw, hzy, hzw]
  have he_xz : e ≠ xz :=
    (k4Edge_ne_of_mem_not_mem hz_xz hzE).symm
  have he_yz : e ≠ yz :=
    (k4Edge_ne_of_mem_not_mem hz_yz hzE).symm
  have he_yw : e ≠ yw :=
    (k4Edge_ne_of_mem_not_mem hw_yw hwE).symm
  have he_f : e ≠ f :=
    k4Edge_ne_of_mem_not_mem hxE hxF
  have hxz_yz : xz ≠ yz :=
    k4Edge_ne_of_mem_not_mem hx_xz hx_not_yz
  have hxz_yw : xz ≠ yw :=
    k4Edge_ne_of_mem_not_mem hx_xz hx_not_yw
  have hxz_f : xz ≠ f :=
    k4Edge_ne_of_mem_not_mem hx_xz hxF
  have hyz_yw : yz ≠ yw :=
    k4Edge_ne_of_mem_not_mem hz_yz hz_not_yw
  have hyz_f : yz ≠ f :=
    k4Edge_ne_of_mem_not_mem hy_yz hyF
  have hyw_f : yw ≠ f :=
    k4Edge_ne_of_mem_not_mem hy_yw hyF
  exact {
    walk :=
      .cons (edge_branch_adj_of_mem x e hxE)
        (.cons (branch_edge_adj_of_mem x xz (by simp [xz]))
          (.cons (edge_branch_adj_of_mem z xz (by simp [xz]))
            (.cons (branch_edge_adj_of_mem z yz (by simp [yz]))
              (.cons (edge_branch_adj_of_mem y yz (by simp [yz]))
                (.cons (branch_edge_adj_of_mem y yw (by simp [yw]))
                  (.cons (edge_branch_adj_of_mem w yw (by simp [yw]))
                    (.cons (branch_edge_adj_of_mem w f hwF) .nil)))))))
    isPath := by
      simp [hxy, hzw, hxz, hxw, hzy, hyw,
        he_xz, he_yz, he_yw, he_f,
        hxz_yz, hxz_yw, hxz_f, hyz_yw, hyz_f, hyw_f]
  }

@[simp] private theorem edgeEdgePathEight_length
    (e f : K4Edge)
    (hdisj :
      Disjoint
        ((e : Sym2 (Fin 4)) : Set (Fin 4))
        ((f : Sym2 (Fin 4)) : Set (Fin 4))) :
    (edgeEdgePathEight e f hdisj).length = 8 := by
  simp [edgeEdgePathEight, SimplePath.length]

/--
Map a canonical subdivision path into the ambient graph and close it through
an outside common neighbor.
-/
private theorem closeOutsidePath
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (K : SimpleGraph.Copy oneSubdivisionK4 G)
    (v : V) (hv : v ∉ Set.range K)
    (a b : Fin 4 ⊕ K4Edge) (hab : a ≠ b)
    (P : SimplePath oneSubdivisionK4 a b)
    (hva : G.Adj v (K a)) (hvb : G.Adj v (K b)) :
    ∃ C : SimpleCycle G, C.length = P.length + 2 := by
  let Q : SimplePath G (K a) (K b) :=
    P.mapInjectiveHom K.toHom K.injective
  have hvQ : v ∉ Q.walk.support := by
    intro hvSupport
    change v ∈ (P.walk.map K.toHom).support at hvSupport
    rw [SimpleGraph.Walk.support_map] at hvSupport
    obtain ⟨x, -, hx⟩ := List.mem_map.mp hvSupport
    exact hv ⟨x, hx⟩
  let R : SimplePath G (K a) v := {
    walk := Q.walk.concat hvb.symm
    isPath := Q.isPath.concat hvQ hvb.symm
  }
  have hedge :
      s(v, K a) ∉ R.walk.edges := by
    intro hedge
    simp only [R, SimpleGraph.Walk.edges_concat,
      List.concat_eq_append, List.mem_append,
      List.mem_singleton] at hedge
    rcases hedge with hedge | hedge
    · apply hvQ
      exact Q.walk.mem_support_of_mem_edges hedge
        (Sym2.mem_mk_left _ _)
    · have hedgeCases :
          (v = K b ∧ K a = v) ∨
          (v = v ∧ K a = K b) := by
        exact Sym2.eq_iff.mp hedge
      rcases hedgeCases with hedgeCases | hedgeCases
      · exact hv ⟨b, hedgeCases.1.symm⟩
      · exact hab (K.injective hedgeCases.2)
  let C : SimpleCycle G := {
    base := v
    walk := R.walk.cons hva
    isCycle :=
      (SimpleGraph.Walk.cons_isCycle_iff R.walk hva).2
        ⟨R.isPath, hedge⟩
  }
  refine ⟨C, ?_⟩
  have hQlength : Q.length = P.length :=
    SimplePath.mapInjectiveHom_length P K.toHom K.injective
  simp only [C, SimpleCycle.length,
    SimpleGraph.Walk.length_cons, R,
    SimpleGraph.Walk.length_concat]
  change Q.walk.length + 1 + 1 = P.walk.length + 2
  change Q.walk.length = P.walk.length at hQlength
  omega

theorem outside_vertex_cycle
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hgirth : GirthAtLeast G 5)
    (K : SimpleGraph.Copy oneSubdivisionK4 G)
    (v : V) (hv : v ∉ Set.range K)
    (a b : Fin 4 ⊕ K4Edge) (hab : a ≠ b)
    (hva : G.Adj v (K a)) (hvb : G.Adj v (K b)) :
    HasCycleLength G 5 ∨ HasCycleLength G 10 := by
  rcases a with x | e <;> rcases b with y | f
  · have hxy : x ≠ y := by
      intro h
      exact hab (by simp [h])
    obtain ⟨C, hC⟩ :=
      closeOutsidePath G K v hv _ _ hab
        (branchBranchPath x y hxy) hva hvb
    exfalso
    have hge := hgirth C
    rw [branchBranchPath_length] at hC
    omega
  · by_cases hxe : x ∈ (f : Sym2 (Fin 4))
    · obtain ⟨C, hC⟩ :=
        closeOutsidePath G K v hv _ _ hab
          (branchEdgePath x f hxe) hva hvb
      exfalso
      have hge := hgirth C
      simp [branchEdgePath] at hC
      omega
    · obtain ⟨C, hC⟩ :=
        closeOutsidePath G K v hv _ _ hab
          (branchEdgePathThree x f hxe) hva hvb
      exact Or.inl ⟨C, by
        rw [branchEdgePathThree_length] at hC
        omega⟩
  · by_cases hxy : y ∈ (e : Sym2 (Fin 4))
    · obtain ⟨C, hC⟩ :=
        closeOutsidePath G K v hv _ _ hab
          (branchEdgePath y e hxy).reverse hva hvb
      exfalso
      have hge := hgirth C
      simp [branchEdgePath] at hC
      omega
    · obtain ⟨C, hC⟩ :=
        closeOutsidePath G K v hv _ _ hab
          (branchEdgePathThree y e hxy).reverse hva hvb
      exact Or.inl ⟨C, by
        simp only [SimplePath.reverse_length,
          branchEdgePathThree_length] at hC
        omega⟩
  · have hef : e ≠ f := by
      intro h
      exact hab (by simp [h])
    by_cases hshare :
        ∃ x : Fin 4,
          x ∈ (e : Sym2 (Fin 4)) ∧
          x ∈ (f : Sym2 (Fin 4))
    · obtain ⟨x, hxe, hxf⟩ := hshare
      obtain ⟨C, hC⟩ :=
        closeOutsidePath G K v hv _ _ hab
          (edgeEdgePath e f hef x hxe hxf) hva hvb
      exfalso
      have hge := hgirth C
      rw [edgeEdgePath_length] at hC
      omega
    · have hdisj :
          Disjoint
            (((e : Sym2 (Fin 4)) : Set (Fin 4)))
            (((f : Sym2 (Fin 4)) : Set (Fin 4))) := by
        apply Set.disjoint_left.2
        intro x hxe hxf
        exact hshare ⟨x, hxe, hxf⟩
      obtain ⟨C, hC⟩ :=
        closeOutsidePath G K v hv _ _ hab
          (edgeEdgePathEight e f hdisj) hva hvb
      exact Or.inr ⟨C, by
        rw [edgeEdgePathEight_length] at hC
        omega⟩

end SubdivisionK4

namespace GHLM

/--
The paper's subdivision-attachment lemma, proved directly for the canonical
one-subdivision of `K₄`; this is the configuration appearing in GHLM
Lemma 5.9.
-/
theorem outside_vertex_on_subdivided_K4
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hgirth : GirthAtLeast G 5)
    (K : SimpleGraph.Copy oneSubdivisionK4 G)
    (v : V) (hv : v ∉ Set.range K)
    (a b : Fin 4 ⊕ K4Edge) (hab : a ≠ b)
    (hva : G.Adj v (K a)) (hvb : G.Adj v (K b)) :
    HasCycleLength G 5 ∨ HasCycleLength G 10 :=
  SubdivisionK4.outside_vertex_cycle
    G hgirth K v hv a b hab hva hvb

end GHLM

end DeanK5
