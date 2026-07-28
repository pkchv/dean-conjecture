import DeanK5.ThetaMinimumInduced
import DeanK5.ThetaOutsideChord
import DeanK5.SubdivisionK4

/-!
# The local attachment conclusion for a minimum theta

This module internalizes the third conclusion of GHLM Lemma 5.10.  The
eventual public theorem shows that adjoining an outside vertex with two
neighbors to a minimum-order theta in a graph of girth at least six induces
the canonical one-subdivision of `K₄`.
-/

open SimpleGraph
open scoped Sym2

namespace DeanK5

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace ThetaMinimumAttachment

private def k4edge (i j : Fin 4) (hij : i ≠ j) : K4Edge :=
  ⟨s(i, j), by simpa [SimpleGraph.mem_edgeSet]⟩

private def e01 : K4Edge := k4edge 0 1 (by decide)
private def e02 : K4Edge := k4edge 0 2 (by decide)
private def e03 : K4Edge := k4edge 0 3 (by decide)
private def e12 : K4Edge := k4edge 1 2 (by decide)
private def e13 : K4Edge := k4edge 1 3 (by decide)
private def e23 : K4Edge := k4edge 2 3 (by decide)

private theorem all_k4edge_cases :
    ∀ e : K4Edge,
      e = e01 ∨ e = e02 ∨ e = e03 ∨
        e = e12 ∨ e = e13 ∨ e = e23 := by
  decide

private theorem k4edge_cases (e : K4Edge) :
    e = e01 ∨ e = e02 ∨ e = e03 ∨
      e = e12 ∨ e = e13 ∨ e = e23 :=
  all_k4edge_cases e

private theorem branch_edge_adj
    (x : Fin 4) (e : K4Edge)
    (hx : x ∈ (e : Sym2 (Fin 4))) :
    oneSubdivisionK4.Adj (Sum.inl x) (Sum.inr e) :=
  hx

private theorem edge_branch_adj
    (x : Fin 4) (e : K4Edge)
    (hx : x ∈ (e : Sym2 (Fin 4))) :
    oneSubdivisionK4.Adj (Sum.inr e) (Sum.inl x) :=
  hx

private def branchBranchPath
    (x y : Fin 4) (hxy : x ≠ y) :
    SimplePath oneSubdivisionK4 (Sum.inl x) (Sum.inl y) := {
  walk :=
    .cons (branch_edge_adj x (k4edge x y hxy) (by simp [k4edge]))
      (.cons (edge_branch_adj y (k4edge x y hxy)
        (by simp [k4edge])) .nil)
  isPath := by
    simp [k4edge, hxy]
}

private noncomputable def branchSubdivisionPath
    (x : Fin 4) (e : K4Edge)
    (hx : x ∉ (e : Sym2 (Fin 4))) :
    SimplePath oneSubdivisionK4 (Sum.inl x) (Sum.inr e) := by
  let y : Fin 4 := (e : Sym2 (Fin 4)).out.1
  have hy : y ∈ (e : Sym2 (Fin 4)) :=
    Sym2.out_fst_mem _
  have hxy : x ≠ y := fun h => hx (h ▸ hy)
  let xy := k4edge x y hxy
  have hxyE : xy ≠ e := by
    intro h
    exact hx (h ▸ (by simp [xy, k4edge]))
  exact {
    walk :=
      .cons (branch_edge_adj x xy (by simp [xy, k4edge]))
        (.cons (edge_branch_adj y xy (by simp [xy, k4edge]))
          (.cons (branch_edge_adj y e hy) .nil))
    isPath := by
      simp [xy, k4edge, hxy]
      change xy ≠ e
      exact hxyE
  }

private def subdivisionSubdivisionPathShared
    (e f : K4Edge) (hef : e ≠ f)
    (x : Fin 4)
    (hxe : x ∈ (e : Sym2 (Fin 4)))
    (hxf : x ∈ (f : Sym2 (Fin 4))) :
    SimplePath oneSubdivisionK4 (Sum.inr e) (Sum.inr f) := {
  walk :=
    .cons (edge_branch_adj x e hxe)
      (.cons (branch_edge_adj x f hxf) .nil)
  isPath := by simp [hef]
}

private noncomputable def subdivisionSubdivisionPathDisjoint
    (e f : K4Edge) (hef : e ≠ f)
    (hshare : ¬∃ x : Fin 4,
      x ∈ (e : Sym2 (Fin 4)) ∧
      x ∈ (f : Sym2 (Fin 4))) :
    SimplePath oneSubdivisionK4 (Sum.inr e) (Sum.inr f) := by
  let x : Fin 4 := (e : Sym2 (Fin 4)).out.1
  let y : Fin 4 := (f : Sym2 (Fin 4)).out.1
  have hxE : x ∈ (e : Sym2 (Fin 4)) :=
    Sym2.out_fst_mem _
  have hyF : y ∈ (f : Sym2 (Fin 4)) :=
    Sym2.out_fst_mem _
  have hxF : x ∉ (f : Sym2 (Fin 4)) :=
    fun hx => hshare ⟨x, hxE, hx⟩
  have hyE : y ∉ (e : Sym2 (Fin 4)) :=
    fun hy => hshare ⟨y, hy, hyF⟩
  have hxy : x ≠ y := fun h => hxF (h ▸ hyF)
  let xy := k4edge x y hxy
  have hexy : e ≠ xy := by
    intro h
    apply hyE
    rw [h]
    simp [xy, k4edge]
  have hxyf : xy ≠ f := by
    intro h
    apply hxF
    rw [← h]
    simp [xy, k4edge]
  exact {
    walk :=
      .cons (edge_branch_adj x e hxE)
        (.cons (branch_edge_adj x xy (by simp [xy, k4edge]))
          (.cons (edge_branch_adj y xy (by simp [xy, k4edge]))
            (.cons (branch_edge_adj y f hyF) .nil)))
    isPath := by
      simp [xy, k4edge, hef, hxy]
      constructor
      · change xy ≠ f
        exact hxyf
      · change e ≠ xy
        exact hexy
  }

@[simp] private theorem branchBranchPath_length
    (x y : Fin 4) (hxy : x ≠ y) :
    (branchBranchPath x y hxy).length = 2 := by
  simp [branchBranchPath, SimplePath.length]

@[simp] private theorem branchSubdivisionPath_length
    (x : Fin 4) (e : K4Edge)
    (hx : x ∉ (e : Sym2 (Fin 4))) :
    (branchSubdivisionPath x e hx).length = 3 := by
  simp [branchSubdivisionPath, SimplePath.length]

@[simp] private theorem subdivisionSubdivisionPathShared_length
    (e f : K4Edge) (hef : e ≠ f)
    (x : Fin 4)
    (hxe : x ∈ (e : Sym2 (Fin 4)))
    (hxf : x ∈ (f : Sym2 (Fin 4))) :
    (subdivisionSubdivisionPathShared e f hef x hxe hxf).length =
      2 := by
  simp [subdivisionSubdivisionPathShared, SimplePath.length]

@[simp] private theorem subdivisionSubdivisionPathDisjoint_length
    (e f : K4Edge) (hef : e ≠ f)
    (hshare : ¬∃ x : Fin 4,
      x ∈ (e : Sym2 (Fin 4)) ∧
      x ∈ (f : Sym2 (Fin 4))) :
    (subdivisionSubdivisionPathDisjoint e f hef hshare).length =
      4 := by
  simp [subdivisionSubdivisionPathDisjoint, SimplePath.length]

/--
Every nonedge between two distinct canonical subdivision vertices has a
simple route of length between two and four.  This is the small-diameter
fact used to rule out additional induced edges by girth six.
-/
private noncomputable def shortCanonicalPath
    (z w : Fin 4 ⊕ K4Edge) (hzw : z ≠ w)
    (hnadj : ¬oneSubdivisionK4.Adj z w) :
    SimplePath oneSubdivisionK4 z w := by
  rcases z with x | e <;> rcases w with y | f
  · exact branchBranchPath x y (by
      intro h
      exact hzw (by simp [h]))
  · exact branchSubdivisionPath x f (by
      simpa [oneSubdivisionK4] using hnadj)
  · exact (branchSubdivisionPath y e (by
      simpa [oneSubdivisionK4] using hnadj)).reverse
  · have hef : e ≠ f := by
      intro h
      exact hzw (by simp [h])
    by_cases hshare :
        ∃ x : Fin 4,
          x ∈ (e : Sym2 (Fin 4)) ∧
          x ∈ (f : Sym2 (Fin 4))
    · let x := Classical.choose hshare
      have hxe : x ∈ (e : Sym2 (Fin 4)) :=
        (Classical.choose_spec hshare).1
      have hxf : x ∈ (f : Sym2 (Fin 4)) :=
        (Classical.choose_spec hshare).2
      exact subdivisionSubdivisionPathShared
        e f hef x hxe hxf
    · exact subdivisionSubdivisionPathDisjoint
        e f hef hshare

private theorem shortCanonicalPath_length_bounds
    (z w : Fin 4 ⊕ K4Edge) (hzw : z ≠ w)
    (hnadj : ¬oneSubdivisionK4.Adj z w) :
    2 ≤ (shortCanonicalPath z w hzw hnadj).length ∧
      (shortCanonicalPath z w hzw hnadj).length ≤ 4 := by
  rcases z with x | e <;> rcases w with y | f
  · simp [shortCanonicalPath]
  · simp [shortCanonicalPath]
  · simp [shortCanonicalPath]
  · simp only [shortCanonicalPath]
    split_ifs with hshare
    · simp
    · simp

/--
Data for a labeled induced copy of the canonical one-subdivision of `K₄`.
Keeping the range and reflection obligations explicit makes the final
conversion to `InducesOneSubdivisionK4` independent of the construction
used to locate the ten vertices.
-/
private structure Model
    (G : SimpleGraph V) (S : Finset V) where
  map : Fin 4 ⊕ K4Edge → V
  map_mem : ∀ z, map z ∈ S
  injective : Function.Injective map
  surjective_on : ∀ v, v ∈ S → ∃ z, map z = v
  adj_iff : ∀ z w,
    G.Adj (map z) (map w) ↔ oneSubdivisionK4.Adj z w

private theorem induces_of_model
    [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V}
    (M : Model G S) :
    InducesOneSubdivisionK4 G S := by
  let f : Fin 4 ⊕ K4Edge → (↑S : Set V) :=
    fun z => ⟨M.map z, M.map_mem z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w hzw
      exact M.injective (congrArg Subtype.val hzw)
    · rintro ⟨v, hv⟩
      obtain ⟨z, hz⟩ := M.surjective_on v hv
      exact ⟨z, Subtype.ext hz⟩
  let e : (Fin 4 ⊕ K4Edge) ≃ (↑S : Set V) :=
    Equiv.ofBijective f hf
  let iso :
      oneSubdivisionK4 ≃g G.induce (↑S : Set V) := {
    toEquiv := e
    map_rel_iff' := by
      intro z w
      change G.Adj (M.map z) (M.map w) ↔
        oneSubdivisionK4.Adj z w
      exact M.adj_iff z w
  }
  exact ⟨iso.symm⟩

private theorem canonical_vertex_count :
    Fintype.card (Fin 4 ⊕ K4Edge) = 10 := by
  decide

/--
A cardinality-based constructor for the model.  In the attachment proof the
natural labeling is visibly onto the ten vertices; equal finite cardinalities
then provide injectivity without a separate pairwise-distinctness ledger.
-/
private theorem induces_of_spanning_labeled_map
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V}
    (f : Fin 4 ⊕ K4Edge → V)
    (himage : Finset.univ.image f = S)
    (hcard : S.card = 10)
    (hadj : ∀ z w,
      G.Adj (f z) (f w) ↔ oneSubdivisionK4.Adj z w) :
    InducesOneSubdivisionK4 G S := by
  have hmem : ∀ z, f z ∈ S := by
    intro z
    rw [← himage]
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
  let fS : Fin 4 ⊕ K4Edge → (↑S : Set V) :=
    fun z => ⟨f z, hmem z⟩
  have hsurj : Function.Surjective fS := by
    rintro ⟨v, hv⟩
    rw [← himage] at hv
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hv
    exact ⟨z, Subtype.ext hz⟩
  have hcardTypes :
      Fintype.card (Fin 4 ⊕ K4Edge) =
        Fintype.card (↑S : Set V) := by
    rw [canonical_vertex_count]
    simpa using hcard.symm
  have hbij :
      Function.Bijective fS :=
    (Fintype.bijective_iff_surjective_and_card fS).2
      ⟨hsurj, hcardTypes⟩
  apply induces_of_model
  exact {
    map := f
    map_mem := hmem
    injective := fun z w h =>
      hbij.1 (Subtype.ext h)
    surjective_on := by
      intro v hv
      obtain ⟨z, hz⟩ := hsurj ⟨v, hv⟩
      exact ⟨z, congrArg Subtype.val hz⟩
    adj_iff := hadj
  }

/--
An additional edge on a spanning labeled one-subdivision closes a canonical
path of length at most four and therefore violates girth six.
-/
private theorem no_extra_edge_of_girth_six
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hgirth : GirthAtLeast G 6)
    (f : Fin 4 ⊕ K4Edge → V)
    (hinj : Function.Injective f)
    (hhom : ∀ {z w},
      oneSubdivisionK4.Adj z w → G.Adj (f z) (f w))
    {z w : Fin 4 ⊕ K4Edge}
    (hzw : G.Adj (f z) (f w)) :
    oneSubdivisionK4.Adj z w := by
  by_contra hcanonical
  have hne : z ≠ w := by
    intro h
    subst w
    exact G.loopless.irrefl (f z) hzw
  let P := shortCanonicalPath z w hne hcanonical
  let hom : oneSubdivisionK4 →g G := {
    toFun := f
    map_rel' := hhom
  }
  let Q : SimplePath G (f z) (f w) :=
    P.mapInjectiveHom hom hinj
  let E : SimplePath G (f z) (f w) :=
    SimplePath.ofAdj hzw
  have hPlength :
      2 ≤ P.length ∧ P.length ≤ 4 := by
    simpa [P] using
      shortCanonicalPath_length_bounds z w hne hcanonical
  have hQlength : Q.length = P.length :=
    SimplePath.mapInjectiveHom_length P hom hinj
  have hElength : E.length = 1 := by
    simp [E]
  have hwalks : Q.walk ≠ E.walk := by
    intro h
    have hlen := congrArg SimpleGraph.Walk.length h
    change Q.length = E.length at hlen
    omega
  obtain ⟨a, -, -, Cwalk, hcycle, hlength⟩ :=
    Q.isPath.exists_isCycle_length_le_add_of_ne
      E.isPath hwalks
  let C : SimpleCycle G := {
    base := a
    walk := Cwalk
    isCycle := hcycle
  }
  have hge : 6 ≤ C.length :=
    hgirth C
  have hClength : C.length = Cwalk.length :=
    rfl
  rw [hClength] at hge
  have hCle : C.length ≤ 5 := by
    rw [hClength]
    change Cwalk.length ≤ Q.length + E.length at hlength
    omega
  omega

/--
It is enough to build a spanning homomorphic copy. Girth six upgrades it to
an induced copy automatically.
-/
private theorem induces_of_spanning_labeled_hom
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V}
    (hgirth : GirthAtLeast G 6)
    (f : Fin 4 ⊕ K4Edge → V)
    (himage : Finset.univ.image f = S)
    (hcard : S.card = 10)
    (hhom : ∀ {z w},
      oneSubdivisionK4.Adj z w → G.Adj (f z) (f w)) :
    InducesOneSubdivisionK4 G S := by
  have hmem : ∀ z, f z ∈ S := by
    intro z
    rw [← himage]
    exact Finset.mem_image.mpr
      ⟨z, Finset.mem_univ _, rfl⟩
  let fS : Fin 4 ⊕ K4Edge → (↑S : Set V) :=
    fun z => ⟨f z, hmem z⟩
  have hsurj : Function.Surjective fS := by
    rintro ⟨v, hv⟩
    rw [← himage] at hv
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hv
    exact ⟨z, Subtype.ext hz⟩
  have hcardTypes :
      Fintype.card (Fin 4 ⊕ K4Edge) =
        Fintype.card (↑S : Set V) := by
    rw [canonical_vertex_count]
    simpa using hcard.symm
  have hbij :
      Function.Bijective fS :=
    (Fintype.bijective_iff_surjective_and_card fS).2
      ⟨hsurj, hcardTypes⟩
  have hinj : Function.Injective f := by
    intro z w h
    exact hbij.1 (Subtype.ext h)
  apply induces_of_spanning_labeled_map f himage hcard
  intro z w
  constructor
  · exact no_extra_edge_of_girth_six
      hgirth f hinj hhom
  · exact hhom

/-- The canonical labeling used after all five theta segments are known. -/
private def labeledMap
    (x y a b pxy pxa pay pxb pby pab : V) :
    Fin 4 ⊕ K4Edge → V
  | Sum.inl i => ![x, y, a, b] i
  | Sum.inr e =>
      if e = e01 then pxy
      else if e = e02 then pxa
      else if e = e03 then pxb
      else if e = e12 then pay
      else if e = e13 then pby
      else pab

set_option maxHeartbeats 1000000

/--
The six displayed subdivided edges make `labeledMap` a homomorphism from
the canonical one-subdivision.
-/
private theorem labeledMap_map_adj
    (x y a b pxy pxa pay pxb pby pab : V)
    (hxxy : G.Adj x pxy) (hyxy : G.Adj y pxy)
    (hxxa : G.Adj x pxa) (haxa : G.Adj a pxa)
    (hxay : G.Adj a pay) (hyay : G.Adj y pay)
    (hxxb : G.Adj x pxb) (hbxb : G.Adj b pxb)
    (hxby : G.Adj b pby) (hyby : G.Adj y pby)
    (hab : G.Adj a pab) (hba : G.Adj b pab) :
    ∀ {z w},
      oneSubdivisionK4.Adj z w →
        G.Adj
          (labeledMap x y a b pxy pxa pay pxb pby pab z)
          (labeledMap x y a b pxy pxa pay pxb pby pab w) := by
  set_option maxHeartbeats 1000000 in
    intro z w hzw
    rcases z with i | e <;> rcases w with j | f
    · exact False.elim hzw
    · rcases k4edge_cases f with rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        fin_cases i <;>
        simp_all [oneSubdivisionK4, labeledMap,
          e01, e02, e03, e12, e13, e23,
          k4edge]
    · rcases k4edge_cases e with rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        fin_cases j <;>
        simp_all [oneSubdivisionK4, labeledMap,
          e01, e02, e03, e12, e13, e23,
          k4edge, SimpleGraph.adj_comm]
    · exact False.elim hzw

set_option maxHeartbeats 200000

end ThetaMinimumAttachment

namespace Theta

/--
Normalized data for the two attachments: they lie at interior positions on
two distinct theta legs, with the remaining leg recorded explicitly.
-/
private structure AttachmentData
    (T : Theta G) (v : V) where
  i : Fin 3
  j : Fin 3
  k : Fin 3
  i_ne_j : i ≠ j
  i_ne_k : i ≠ k
  j_ne_k : j ≠ k
  r : ℕ
  s : ℕ
  r_pos : 0 < r
  r_lt : r < (T.path i).length
  s_pos : 0 < s
  s_lt : s < (T.path j).length
  adj_r : G.Adj v ((T.path i).walk.getVert r)
  adj_s : G.Adj v ((T.path j).walk.getVert s)

/--
The two-neighbor hypothesis can be normalized to two distinct legs and
strictly internal attachment positions.  The same-leg exclusion proved in
`ThetaMinimumInduced` also rules out attachments at either branch vertex,
because each branch vertex lies on all three legs.
-/
private theorem exists_attachmentData
    [Fintype V] [DecidableEq V]
    (T : Theta G)
    (hminimum : T.IsMinimumOrder)
    (hgirth : GirthAtLeast G 6)
    (v : V) (hv : v ∉ T.verts)
    (hdegree :
      2 ≤ (G.neighborSet v ∩
        (↑T.verts : Set V)).ncard) :
    Nonempty (AttachmentData T v) := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard
      (s := G.neighborSet v ∩
        (↑T.verts : Set V))).1 hdegree
  have hva : G.Adj v a := by
    simpa [SimpleGraph.mem_neighborSet] using ha.1
  have hvb : G.Adj v b := by
    simpa [SimpleGraph.mem_neighborSet] using hb.1
  have haT : a ∈ T.verts := ha.2
  have hbT : b ∈ T.verts := hb.2
  simp only [Theta.verts, Finset.mem_biUnion] at haT hbT
  obtain ⟨i, -, hai⟩ := haT
  obtain ⟨j, -, hbj⟩ := hbT
  have hai' : a ∈ (T.path i).walk.support := by
    simpa using hai
  have hbj' : b ∈ (T.path j).walk.support := by
    simpa using hbj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact T.minimumOrder_outside_atMostOneNeighbor_on_path
      hminimum hgirth v hv i hab hai' hbj' hva hvb
  have hax : a ≠ T.x := by
    intro hax
    have haj :
        a ∈ (T.path j).walk.support := by
      rw [hax]
      exact (T.path j).walk.start_mem_support
    exact T.minimumOrder_outside_atMostOneNeighbor_on_path
      hminimum hgirth v hv j hab haj hbj' hva hvb
  have hay : a ≠ T.y := by
    intro hay
    have haj :
        a ∈ (T.path j).walk.support := by
      rw [hay]
      exact (T.path j).walk.end_mem_support
    exact T.minimumOrder_outside_atMostOneNeighbor_on_path
      hminimum hgirth v hv j hab haj hbj' hva hvb
  have hbx : b ≠ T.x := by
    intro hbx
    have hbi :
        b ∈ (T.path i).walk.support := by
      rw [hbx]
      exact (T.path i).walk.start_mem_support
    exact T.minimumOrder_outside_atMostOneNeighbor_on_path
      hminimum hgirth v hv i hab.symm hbi hai' hvb hva
  have hby : b ≠ T.y := by
    intro hby
    have hbi :
        b ∈ (T.path i).walk.support := by
      rw [hby]
      exact (T.path i).walk.end_mem_support
    exact T.minimumOrder_outside_atMostOneNeighbor_on_path
      hminimum hgirth v hv i hab.symm hbi hai' hvb hva
  obtain ⟨r, hra, hrleWalk⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hai'
  obtain ⟨s, hsb, hsleWalk⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hbj'
  have hrle : r ≤ (T.path i).length := by
    simpa [SimplePath.length] using hrleWalk
  have hsle : s ≤ (T.path j).length := by
    simpa [SimplePath.length] using hsleWalk
  have hrpos : 0 < r := by
    by_contra hr
    have hrzero : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    apply hax
    simpa using hra.symm
  have hspos : 0 < s := by
    by_contra hs
    have hszero : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    apply hbx
    simpa using hsb.symm
  have hrlt : r < (T.path i).length := by
    by_contra hr
    have hre : r = (T.path i).length := by omega
    apply hay
    rw [← hra]
    simp [SimplePath.length, hre]
  have hslt : s < (T.path j).length := by
    by_contra hs
    have hse : s = (T.path j).length := by omega
    apply hby
    rw [← hsb]
    simp [SimplePath.length, hse]
  obtain ⟨k, hik, hjk⟩ :
      ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    have hfinite :
        ∀ p q : Fin 3, p ≠ q →
          ∃ k : Fin 3, p ≠ k ∧ q ≠ k := by
      decide
    exact hfinite i j hij
  exact ⟨{
    i := i
    j := j
    k := k
    i_ne_j := hij
    i_ne_k := hik
    j_ne_k := hjk
    r := r
    s := s
    r_pos := hrpos
    r_lt := hrlt
    s_pos := hspos
    s_lt := hslt
    adj_r := by simpa [hra] using hva
    adj_s := by simpa [hsb] using hvb
  }⟩

private theorem attachment_r_ne_s_vertex
    (T : Theta G) (v : V)
    (D : AttachmentData T v) :
    (T.path D.i).walk.getVert D.r ≠
      (T.path D.j).walk.getVert D.s := by
  intro h
  have hri :
      (T.path D.i).walk.getVert D.r ∈
        (T.path D.i).internalSupport := by
    apply (T.path D.i).mem_internalSupport_of_mem_support
      ((T.path D.i).walk.getVert_mem_support D.r)
    · intro hx
      have hrzero :=
        ((T.path D.i).isPath.getVert_eq_start_iff
          (by simpa [SimplePath.length] using D.r_lt.le)).1 hx
      exact (Nat.ne_of_gt D.r_pos) hrzero
    · intro hy
      have hrend :=
        ((T.path D.i).isPath.getVert_eq_end_iff
          (by simpa [SimplePath.length] using D.r_lt.le)).1 hy
      simpa [SimplePath.length] using
        (Nat.ne_of_lt D.r_lt hrend)
  have hsj :
      (T.path D.j).walk.getVert D.s ∈
        (T.path D.j).internalSupport := by
    apply (T.path D.j).mem_internalSupport_of_mem_support
      ((T.path D.j).walk.getVert_mem_support D.s)
    · intro hx
      have hszero :=
        ((T.path D.j).isPath.getVert_eq_start_iff
          (by simpa [SimplePath.length] using D.s_lt.le)).1 hx
      exact (Nat.ne_of_gt D.s_pos) hszero
    · intro hy
      have hsend :=
        ((T.path D.j).isPath.getVert_eq_end_iff
          (by simpa [SimplePath.length] using D.s_lt.le)).1 hy
      simpa [SimplePath.length] using
        (Nat.ne_of_lt D.s_lt hsend)
  exact (List.disjoint_left.mp
    (T.internal_disjoint D.i D.j D.i_ne_j) hri)
    (h ▸ hsj)

private def attachmentPath
    [DecidableEq V]
    (T : Theta G) (v : V) (hv : v ∉ T.verts)
    (D : AttachmentData T v) :
    SimplePath G
      ((T.path D.i).walk.getVert D.r)
      ((T.path D.j).walk.getVert D.s) := {
  walk := .cons D.adj_r.symm (.cons D.adj_s .nil)
  isPath := by
    have hrv :
        (T.path D.i).walk.getVert D.r ≠ v := by
      intro h
      apply hv
      simp only [Theta.verts, Finset.mem_biUnion]
      exact ⟨D.i, Finset.mem_univ _, by
        simpa [h] using
          (T.path D.i).walk.getVert_mem_support D.r⟩
    have hsv :
        (T.path D.j).walk.getVert D.s ≠ v := by
      intro h
      apply hv
      simp only [Theta.verts, Finset.mem_biUnion]
      exact ⟨D.j, Finset.mem_univ _, by
        simpa [h] using
          (T.path D.j).walk.getVert_mem_support D.s⟩
    have hrs := attachment_r_ne_s_vertex T v D
    simp [hrv, hsv.symm, hrs]
}

@[simp] private theorem attachmentPath_length
    [DecidableEq V]
    (T : Theta G) (v : V) (hv : v ∉ T.verts)
    (D : AttachmentData T v) :
    (attachmentPath T v hv D).length = 2 := by
  simp [attachmentPath, SimplePath.length]

private theorem viaFirstRoot_support_in_verts
    [DecidableEq V]
    (T : Theta G) (v : V)
    (D : AttachmentData T v) :
    ∀ z ∈
        (T.viaFirstRoot D.i_ne_j D.r D.s D.r_lt).walk.support,
      z ∈ T.verts := by
  intro z hz
  change z ∈
    (((T.path D.i).take D.r).reverse.walk.append
      ((T.path D.j).take D.s).walk).support at hz
  rw [SimpleGraph.Walk.support_append] at hz
  rcases List.mem_append.mp hz with hzI | hzJ
  · have hzTake :
        z ∈ ((T.path D.i).take D.r).walk.support := by
      simpa [SimplePath.reverse] using hzI
    simp only [Theta.verts, Finset.mem_biUnion]
    exact ⟨D.i, Finset.mem_univ _,
      by simpa using
        (T.path D.i).mem_support_of_mem_take D.r hzTake⟩
  · simp only [Theta.verts, Finset.mem_biUnion]
    exact ⟨D.j, Finset.mem_univ _,
      by simpa using
        (T.path D.j).mem_support_of_mem_take D.s
          (List.mem_of_mem_tail hzJ)⟩

private theorem viaEnd_support_in_verts
    [DecidableEq V]
    (T : Theta G) (v : V)
    (D : AttachmentData T v) :
    ∀ z ∈
        (T.viaEnd D.i_ne_j D.r D.s
          D.r_pos D.r_lt.le).walk.support,
      z ∈ T.verts := by
  intro z hz
  change z ∈
    (((T.path D.i).drop D.r).walk.append
      ((T.path D.j).drop D.s).reverse.walk).support at hz
  rw [SimpleGraph.Walk.support_append] at hz
  rcases List.mem_append.mp hz with hzI | hzJ
  · simp only [Theta.verts, Finset.mem_biUnion]
    exact ⟨D.i, Finset.mem_univ _,
      by simpa using
        (T.path D.i).mem_support_of_mem_drop D.r hzI⟩
  · have hzDrop :
        z ∈ ((T.path D.j).drop D.s).walk.support := by
      simpa [SimplePath.reverse] using
        (List.mem_of_mem_tail hzJ)
    simp only [Theta.verts, Finset.mem_biUnion]
    exact ⟨D.j, Finset.mem_univ _,
      by simpa using
        (T.path D.j).mem_support_of_mem_drop D.s hzDrop⟩

/-- Girth six forces both cycles closed through the outside vertex to have
at least four theta edges. -/
private theorem attachment_girth_bounds
    [DecidableEq V]
    (T : Theta G)
    (hgirth : GirthAtLeast G 6)
    (v : V) (hv : v ∉ T.verts)
    (D : AttachmentData T v) :
    4 ≤ D.r + D.s ∧
      4 ≤ ((T.path D.i).length - D.r) +
        ((T.path D.j).length - D.s) := by
  let R := (attachmentPath T v hv D).reverse
  let A :=
    T.viaFirstRoot D.i_ne_j D.r D.s D.r_lt
  have hdisjA :
      A.walk.support.tail.Disjoint R.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzA hzR
    have hzR' :
        z = v ∨
          z = (T.path D.i).walk.getVert D.r := by
      simpa [R, attachmentPath,
        SimplePath.reverse] using hzR
    rcases hzR' with hzv | hzr
    · apply hv
      rw [← hzv]
      exact viaFirstRoot_support_in_verts T v D z
        (List.mem_of_mem_tail hzA)
    · apply A.start_not_mem_tail
      simpa [A, hzr] using hzA
  have hlongA : 1 < A.length ∨ 1 < R.length := by
    right
    simp [R]
  let CA := cycleOfDisjointPaths A R hdisjA hlongA
  have hfirst : 4 ≤ D.r + D.s := by
    have hC := hgirth CA
    rw [cycleOfDisjointPaths_length] at hC
    have hA :
        A.length = D.r + D.s := by
      simpa [A] using
        T.viaFirstRoot_length D.i_ne_j
          D.r D.s D.r_lt D.s_lt.le
    have hR : R.length = 2 := by simp [R]
    omega
  let B :=
    T.viaEnd D.i_ne_j D.r D.s
      D.r_pos D.r_lt.le
  have hdisjB :
      B.walk.support.tail.Disjoint R.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzB hzR
    have hzR' :
        z = v ∨
          z = (T.path D.i).walk.getVert D.r := by
      simpa [R, attachmentPath,
        SimplePath.reverse] using hzR
    rcases hzR' with hzv | hzr
    · apply hv
      rw [← hzv]
      exact viaEnd_support_in_verts T v D z
        (List.mem_of_mem_tail hzB)
    · apply B.start_not_mem_tail
      simpa [B, hzr] using hzB
  have hlongB : 1 < B.length ∨ 1 < R.length := by
    right
    simp [R]
  let CB := cycleOfDisjointPaths B R hdisjB hlongB
  have hsecond :
      4 ≤ ((T.path D.i).length - D.r) +
        ((T.path D.j).length - D.s) := by
    have hC := hgirth CB
    rw [cycleOfDisjointPaths_length] at hC
    have hB :
        B.length =
            ((T.path D.i).length - D.r) +
            ((T.path D.j).length - D.s) := by
      simp [B, T.viaEnd_length D.i_ne_j D.r D.s
        D.r_pos D.r_lt.le]
    have hR : R.length = 2 := by simp [R]
    omega
  exact ⟨hfirst, hsecond⟩

private structure ExactAttachmentLengths
    (T : Theta G) (v : V)
    (D : AttachmentData T v) : Prop where
  r_eq_two : D.r = 2
  s_eq_two : D.s = 2
  i_length_eq_four : (T.path D.i).length = 4
  j_length_eq_four : (T.path D.j).length = 4
  k_length_eq_two : (T.path D.k).length = 2

private theorem exactAttachmentLengths
    [DecidableEq V]
    (T : Theta G)
    (_hminimum : T.IsMinimumOrder)
    (hgirth : GirthAtLeast G 6)
    (v : V) (hv : v ∉ T.verts)
    (D : AttachmentData T v)
    (hsegments :
      D.r ≤ 2 ∧ D.s ≤ 2 ∧
        (T.path D.i).length - D.r ≤ 2 ∧
        (T.path D.j).length - D.s ≤ 2)
    (hthird : (T.path D.k).length ≤ 2) :
    ExactAttachmentLengths T v D := by
  have hgaps :=
    attachment_girth_bounds T hgirth v hv D
  have hr : D.r = 2 := by omega
  have hs : D.s = 2 := by omega
  have hitail :
      (T.path D.i).length - D.r = 2 := by
    have hpos :
        1 ≤ (T.path D.i).length - D.r := by omega
    have hjpos :
        1 ≤ (T.path D.j).length - D.s := by omega
    omega
  have hjtail :
      (T.path D.j).length - D.s = 2 := by
    have hpos :
        1 ≤ (T.path D.i).length - D.r := by omega
    have hjpos :
        1 ≤ (T.path D.j).length - D.s := by omega
    omega
  have hi : (T.path D.i).length = 4 := by omega
  have hj : (T.path D.j).length = 4 := by omega
  have hkLower :
      2 ≤ (T.path D.k).length := by
    have hsix :=
      T.six_le_add_lengths hgirth D.i_ne_k
    omega
  exact {
    r_eq_two := hr
    s_eq_two := hs
    i_length_eq_four := hi
    j_length_eq_four := hj
    k_length_eq_two := by omega
  }

/--
Canonical vertices other than the exceptional subdivision vertex are
located by a theta leg and a position on that leg.
-/
private def canonicalLocation
    (T : Theta G) (v : V) (D : AttachmentData T v) :
    Fin 4 ⊕ K4Edge → Option (Fin 3 × ℕ)
  | Sum.inl i =>
      ![some (D.i, 0), some (D.i, 4),
        some (D.i, 2), some (D.j, 2)] i
  | Sum.inr e =>
      if e = ThetaMinimumAttachment.e01 then some (D.k, 1)
      else if e = ThetaMinimumAttachment.e02 then some (D.i, 1)
      else if e = ThetaMinimumAttachment.e03 then some (D.j, 1)
      else if e = ThetaMinimumAttachment.e12 then some (D.i, 3)
      else if e = ThetaMinimumAttachment.e13 then some (D.j, 3)
      else none

set_option maxHeartbeats 1000000

private theorem canonicalLocation_injective
    (T : Theta G) (v : V) (D : AttachmentData T v) :
    Function.Injective (canonicalLocation T v D) := by
  intro z w h
  rcases z with i | e <;> rcases w with j | f
  · fin_cases i <;> fin_cases j <;>
      simp_all [canonicalLocation,
        D.i_ne_j, D.i_ne_j.symm]
  · rcases ThetaMinimumAttachment.k4edge_cases f with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      fin_cases i <;>
      simp_all [canonicalLocation,
        ThetaMinimumAttachment.e01,
        ThetaMinimumAttachment.e02,
        ThetaMinimumAttachment.e03,
        ThetaMinimumAttachment.e12,
        ThetaMinimumAttachment.e13,
        ThetaMinimumAttachment.e23,
        ThetaMinimumAttachment.k4edge,
        D.i_ne_j, D.i_ne_j.symm,
        D.i_ne_k, D.j_ne_k]
  · rcases ThetaMinimumAttachment.k4edge_cases e with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      fin_cases j <;>
      simp_all [canonicalLocation,
        ThetaMinimumAttachment.e01,
        ThetaMinimumAttachment.e02,
        ThetaMinimumAttachment.e03,
        ThetaMinimumAttachment.e12,
        ThetaMinimumAttachment.e13,
        ThetaMinimumAttachment.e23,
        ThetaMinimumAttachment.k4edge,
        D.i_ne_j, D.i_ne_j.symm,
        D.i_ne_k.symm, D.j_ne_k.symm]
  · rcases ThetaMinimumAttachment.k4edge_cases e with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases ThetaMinimumAttachment.k4edge_cases f with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [canonicalLocation,
        ThetaMinimumAttachment.e01,
        ThetaMinimumAttachment.e02,
        ThetaMinimumAttachment.e03,
        ThetaMinimumAttachment.e12,
        ThetaMinimumAttachment.e13,
        ThetaMinimumAttachment.e23,
        ThetaMinimumAttachment.k4edge,
        D.i_ne_j, D.i_ne_j.symm,
        D.i_ne_k, D.i_ne_k.symm,
        D.j_ne_k, D.j_ne_k.symm]

set_option maxHeartbeats 200000

private def IsCanonicalLocation
    (T : Theta G) (v : V) (D : AttachmentData T v)
    (p : Fin 3 × ℕ) : Prop :=
  (p.1 = D.i ∧ p.2 ≤ 4) ∨
    (p.1 = D.j ∧ 1 ≤ p.2 ∧ p.2 ≤ 3) ∨
    (p.1 = D.k ∧ p.2 = 1)

private theorem canonicalLocation_isCanonical
    (T : Theta G) (v : V) (D : AttachmentData T v)
    {z : Fin 4 ⊕ K4Edge} {p : Fin 3 × ℕ}
    (hz : canonicalLocation T v D z = some p) :
    IsCanonicalLocation T v D p := by
  rcases z with i | e
  · fin_cases i <;>
      simp_all [canonicalLocation] <;>
      subst p <;>
      simp [IsCanonicalLocation]
  · rcases ThetaMinimumAttachment.k4edge_cases e with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [canonicalLocation,
        ThetaMinimumAttachment.e01,
        ThetaMinimumAttachment.e02,
        ThetaMinimumAttachment.e03,
        ThetaMinimumAttachment.e12,
        ThetaMinimumAttachment.e13,
        ThetaMinimumAttachment.e23,
        ThetaMinimumAttachment.k4edge] <;>
      subst p <;>
      simp [IsCanonicalLocation]

private def locationValue
    (T : Theta G) (v : V) (D : AttachmentData T v) :
    Fin 4 ⊕ K4Edge → V :=
  fun z =>
    match canonicalLocation T v D z with
    | none => v
    | some p => (T.path p.1).walk.getVert p.2

private theorem getVert_eq_location_cases
    (T : Theta G)
    {i j : Fin 3} {r s : ℕ}
    (hr : r ≤ (T.path i).length)
    (hs : s ≤ (T.path j).length)
    (h :
      (T.path i).walk.getVert r =
        (T.path j).walk.getVert s) :
    (i = j ∧ r = s) ∨
      (r = 0 ∧ s = 0) ∨
      (r = (T.path i).length ∧
        s = (T.path j).length) := by
  by_cases hij : i = j
  · subst j
    exact Or.inl ⟨rfl,
      (T.path i).isPath.getVert_injOn
        (by simpa [SimplePath.length] using hr)
        (by simpa [SimplePath.length] using hs) h⟩
  · have hri :
        (T.path i).walk.getVert r ∈
          (T.path i).walk.support :=
      (T.path i).walk.getVert_mem_support r
    have hsj :
        (T.path j).walk.getVert s ∈
          (T.path j).walk.support :=
      (T.path j).walk.getVert_mem_support s
    rcases T.eq_root_of_mem_two_paths hij
        hri (h ▸ hsj) with hx | hy
    · right
      left
      constructor
      · exact ((T.path i).isPath.getVert_eq_start_iff
          (by simpa [SimplePath.length] using hr)).1 hx
      · exact ((T.path j).isPath.getVert_eq_start_iff
          (by simpa [SimplePath.length] using hs)).1
            (h.symm.trans hx)
    · right
      right
      constructor
      · simpa [SimplePath.length] using
          ((T.path i).isPath.getVert_eq_end_iff
            (by simpa [SimplePath.length] using hr)).1 hy
      · simpa [SimplePath.length] using
          ((T.path j).isPath.getVert_eq_end_iff
            (by simpa [SimplePath.length] using hs)).1
              (h.symm.trans hy)

private theorem canonicalLocation_le_length
    (T : Theta G) (v : V) (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D)
    {p : Fin 3 × ℕ}
    (hp : IsCanonicalLocation T v D p) :
    p.2 ≤ (T.path p.1).length := by
  rcases hp with hp | hp | hp
  · rcases hp with ⟨hleg, hp⟩
    rw [hleg, E.i_length_eq_four]
    omega
  · rcases hp with ⟨hleg, -, hp⟩
    rw [hleg, E.j_length_eq_four]
    omega
  · rcases hp with ⟨hleg, hpos⟩
    rw [hleg, E.k_length_eq_two]
    omega

private theorem canonicalLocation_eq_of_start
    (T : Theta G) (v : V) (D : AttachmentData T v)
    {p : Fin 3 × ℕ}
    (hp : IsCanonicalLocation T v D p)
    (hzero : p.2 = 0) :
    p = (D.i, 0) := by
  rcases hp with hp | hp | hp
  · rcases hp with ⟨hleg, -⟩
    exact Prod.ext hleg hzero
  · omega
  · omega

private theorem canonicalLocation_eq_of_end
    (T : Theta G) (v : V) (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D)
    {p : Fin 3 × ℕ}
    (hp : IsCanonicalLocation T v D p)
    (hend : p.2 = (T.path p.1).length) :
    p = (D.i, 4) := by
  rcases hp with hp | hp | hp
  · rcases hp with ⟨hleg, -⟩
    have hpos : p.2 = 4 := by
      rw [hleg, E.i_length_eq_four] at hend
      exact hend
    exact Prod.ext hleg hpos
  · rcases hp with ⟨hleg, -, hn⟩
    rw [hleg, E.j_length_eq_four] at hend
    omega
  · rcases hp with ⟨hleg, hpos⟩
    rw [hleg, E.k_length_eq_two] at hend
    omega

private theorem locationValue_injective
    [DecidableEq V]
    (T : Theta G) (v : V) (hv : v ∉ T.verts)
    (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D) :
    Function.Injective (locationValue T v D) := by
  intro z w hzw
  generalize hz : canonicalLocation T v D z = oz
  generalize hw : canonicalLocation T v D w = ow
  unfold locationValue at hzw
  rw [hz, hw] at hzw
  rcases oz with _ | p <;> rcases ow with _ | q <;>
    simp only at hzw
  · exact canonicalLocation_injective T v D (hz.trans hw.symm)
  · exfalso
    apply hv
    rw [hzw]
    exact T.path_support_subset_verts_basic q.1 _
      ((T.path q.1).walk.getVert_mem_support q.2)
  · exfalso
    apply hv
    rw [← hzw]
    exact T.path_support_subset_verts_basic p.1 _
      ((T.path p.1).walk.getVert_mem_support p.2)
  · have hp := canonicalLocation_isCanonical T v D hz
    have hq := canonicalLocation_isCanonical T v D hw
    have hpq : p = q := by
      rcases getVert_eq_location_cases T
          (canonicalLocation_le_length T v D E hp)
          (canonicalLocation_le_length T v D E hq)
          hzw with hs | hs | he
      · exact Prod.ext hs.1 hs.2
      · exact (canonicalLocation_eq_of_start T v D hp hs.1).trans
          (canonicalLocation_eq_of_start T v D hq hs.2).symm
      · exact (canonicalLocation_eq_of_end T v D E hp he.1).trans
          (canonicalLocation_eq_of_end T v D E hq he.2).symm
    apply canonicalLocation_injective T v D
    rw [hz, hw, hpq]

private theorem fin3_eq_one_of_three
    {i j k q : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    q = i ∨ q = j ∨ q = k := by
  fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases q <;> simp_all

private theorem path_getVert_mem_locationValue_image
    [DecidableEq V]
    (T : Theta G) (v : V)
    (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D)
    (q : Fin 3) (n : ℕ)
    (hn : n ≤ (T.path q).length) :
    (T.path q).walk.getVert n ∈
      Finset.univ.image (locationValue T v D) := by
  rcases fin3_eq_one_of_three
      D.i_ne_j D.i_ne_k D.j_ne_k (q := q) with
      rfl | rfl | rfl
  · rw [E.i_length_eq_four] at hn
    interval_cases n
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 0, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inr ThetaMinimumAttachment.e02,
          Finset.mem_univ _, by
          simp [locationValue, canonicalLocation,
            ThetaMinimumAttachment.e01,
            ThetaMinimumAttachment.e02,
            ThetaMinimumAttachment.k4edge]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 2, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inr ThetaMinimumAttachment.e12,
          Finset.mem_univ _, by
          simp [locationValue, canonicalLocation,
            ThetaMinimumAttachment.e01,
            ThetaMinimumAttachment.e02,
            ThetaMinimumAttachment.e03,
            ThetaMinimumAttachment.e12,
            ThetaMinimumAttachment.k4edge]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 1, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]⟩
  · rw [E.j_length_eq_four] at hn
    interval_cases n
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 0, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inr ThetaMinimumAttachment.e03,
          Finset.mem_univ _, by
          simp [locationValue, canonicalLocation,
            ThetaMinimumAttachment.e01,
            ThetaMinimumAttachment.e02,
            ThetaMinimumAttachment.e03,
            ThetaMinimumAttachment.k4edge]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 3, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inr ThetaMinimumAttachment.e13,
          Finset.mem_univ _, by
          simp [locationValue, canonicalLocation,
            ThetaMinimumAttachment.e01,
            ThetaMinimumAttachment.e02,
            ThetaMinimumAttachment.e03,
            ThetaMinimumAttachment.e12,
            ThetaMinimumAttachment.e13,
            ThetaMinimumAttachment.k4edge]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 1, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]
          have hiend :
              (T.path D.i).walk.getVert
                  (T.path D.i).length = T.y := by
            simp [SimplePath.length]
          have hjend :
              (T.path D.j).walk.getVert
                  (T.path D.j).length = T.y := by
            simp [SimplePath.length]
          rw [E.i_length_eq_four] at hiend
          rw [E.j_length_eq_four] at hjend
          exact hiend.trans hjend.symm⟩
  · rw [E.k_length_eq_two] at hn
    interval_cases n
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 0, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inr ThetaMinimumAttachment.e01,
          Finset.mem_univ _, by
          simp [locationValue, canonicalLocation,
            ThetaMinimumAttachment.e01,
            ThetaMinimumAttachment.k4edge]⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inl 1, Finset.mem_univ _, by
          simp [locationValue, canonicalLocation]
          have hiend :
              (T.path D.i).walk.getVert
                  (T.path D.i).length = T.y := by
            simp [SimplePath.length]
          have hkend :
              (T.path D.k).walk.getVert
                  (T.path D.k).length = T.y := by
            simp [SimplePath.length]
          rw [E.i_length_eq_four] at hiend
          rw [E.k_length_eq_two] at hkend
          exact hiend.trans hkend.symm⟩

private theorem locationValue_image
    [DecidableEq V]
    (T : Theta G) (v : V)
    (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D) :
    Finset.univ.image (locationValue T v D) =
      insert v T.verts := by
  apply Finset.ext
  intro z
  constructor
  · intro hz
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hz
    generalize hloc : canonicalLocation T v D q = loc
    rcases loc with _ | p
    · apply Finset.mem_insert.mpr
      left
      simp [locationValue, hloc]
    · apply Finset.mem_insert.mpr
      right
      simp only [locationValue, hloc]
      exact T.path_support_subset_verts_basic p.1 _
        ((T.path p.1).walk.getVert_mem_support p.2)
  · intro hz
    rcases Finset.mem_insert.mp hz with rfl | hzT
    · exact Finset.mem_image.mpr
        ⟨Sum.inr ThetaMinimumAttachment.e23,
          Finset.mem_univ _, by
          simp [locationValue, canonicalLocation,
            ThetaMinimumAttachment.e01,
            ThetaMinimumAttachment.e02,
            ThetaMinimumAttachment.e03,
            ThetaMinimumAttachment.e12,
            ThetaMinimumAttachment.e13,
            ThetaMinimumAttachment.e23,
            ThetaMinimumAttachment.k4edge]⟩
    · simp only [Theta.verts, Finset.mem_biUnion] at hzT
      obtain ⟨q, -, hzq⟩ := hzT
      have hzq' :
          z ∈ (T.path q).walk.support := by
        simpa using hzq
      obtain ⟨n, hnz, hn⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzq'
      rw [← hnz]
      exact path_getVert_mem_locationValue_image
        T v D E q n (by
          simpa [SimplePath.length] using hn)

private def attachmentModelMap
    (T : Theta G) (v : V) (D : AttachmentData T v) :
    Fin 4 ⊕ K4Edge → V :=
  ThetaMinimumAttachment.labeledMap
    T.x T.y
    ((T.path D.i).walk.getVert 2)
    ((T.path D.j).walk.getVert 2)
    ((T.path D.k).walk.getVert 1)
    ((T.path D.i).walk.getVert 1)
    ((T.path D.i).walk.getVert 3)
    ((T.path D.j).walk.getVert 1)
    ((T.path D.j).walk.getVert 3)
    v

private theorem locationValue_eq_attachmentModelMap
    (T : Theta G) (v : V)
    (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D) :
    locationValue T v D = attachmentModelMap T v D := by
  have hiend :
      (T.path D.i).walk.getVert 4 = T.y := by
    have hiLength :
        (T.path D.i).walk.length = 4 := by
      simpa [SimplePath.length] using
        E.i_length_eq_four
    have h :=
      (T.path D.i).walk.getVert_length
    rw [hiLength] at h
    exact h
  funext z
  rcases z with q | e
  · fin_cases q <;>
      simp [locationValue, canonicalLocation,
        attachmentModelMap,
        ThetaMinimumAttachment.labeledMap,
        hiend]
  · rcases ThetaMinimumAttachment.k4edge_cases e with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [locationValue, canonicalLocation,
        attachmentModelMap,
        ThetaMinimumAttachment.labeledMap,
        ThetaMinimumAttachment.e01,
        ThetaMinimumAttachment.e02,
        ThetaMinimumAttachment.e03,
        ThetaMinimumAttachment.e12,
        ThetaMinimumAttachment.e13,
        ThetaMinimumAttachment.e23,
        ThetaMinimumAttachment.k4edge]

private theorem attachmentModelMap_map_adj
    (T : Theta G) (v : V)
    (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D) :
    ∀ {z w},
      oneSubdivisionK4.Adj z w →
        G.Adj (attachmentModelMap T v D z)
          (attachmentModelMap T v D w) := by
  have hiLength :
      (T.path D.i).walk.length = 4 := by
    simpa [SimplePath.length] using
      E.i_length_eq_four
  have hjLength :
      (T.path D.j).walk.length = 4 := by
    simpa [SimplePath.length] using
      E.j_length_eq_four
  have hkLength :
      (T.path D.k).walk.length = 2 := by
    simpa [SimplePath.length] using
      E.k_length_eq_two
  have hi01 :
      G.Adj ((T.path D.i).walk.getVert 0)
        ((T.path D.i).walk.getVert 1) :=
    (T.path D.i).walk.adj_getVert_succ (by omega)
  have hi12 :
      G.Adj ((T.path D.i).walk.getVert 1)
        ((T.path D.i).walk.getVert 2) :=
    (T.path D.i).walk.adj_getVert_succ (by omega)
  have hi23 :
      G.Adj ((T.path D.i).walk.getVert 2)
        ((T.path D.i).walk.getVert 3) :=
    (T.path D.i).walk.adj_getVert_succ (by omega)
  have hi34 :
      G.Adj ((T.path D.i).walk.getVert 3)
        ((T.path D.i).walk.getVert 4) :=
    (T.path D.i).walk.adj_getVert_succ (by omega)
  have hj01 :
      G.Adj ((T.path D.j).walk.getVert 0)
        ((T.path D.j).walk.getVert 1) :=
    (T.path D.j).walk.adj_getVert_succ (by omega)
  have hj12 :
      G.Adj ((T.path D.j).walk.getVert 1)
        ((T.path D.j).walk.getVert 2) :=
    (T.path D.j).walk.adj_getVert_succ (by omega)
  have hj23 :
      G.Adj ((T.path D.j).walk.getVert 2)
        ((T.path D.j).walk.getVert 3) :=
    (T.path D.j).walk.adj_getVert_succ (by omega)
  have hj34 :
      G.Adj ((T.path D.j).walk.getVert 3)
        ((T.path D.j).walk.getVert 4) :=
    (T.path D.j).walk.adj_getVert_succ (by omega)
  have hk01 :
      G.Adj ((T.path D.k).walk.getVert 0)
        ((T.path D.k).walk.getVert 1) :=
    (T.path D.k).walk.adj_getVert_succ (by omega)
  have hk12 :
      G.Adj ((T.path D.k).walk.getVert 1)
        ((T.path D.k).walk.getVert 2) :=
    (T.path D.k).walk.adj_getVert_succ (by omega)
  apply ThetaMinimumAttachment.labeledMap_map_adj
  · simpa using hk01
  · have hkend :
        (T.path D.k).walk.getVert 2 = T.y := by
      have h := (T.path D.k).walk.getVert_length
      rw [hkLength] at h
      exact h
    simpa [hkend] using hk12.symm
  · simpa using hi01
  · simpa using hi12.symm
  · exact hi23
  · have hiend :
        (T.path D.i).walk.getVert 4 = T.y := by
      have h := (T.path D.i).walk.getVert_length
      rw [hiLength] at h
      exact h
    simpa [hiend] using hi34.symm
  · simpa using hj01
  · simpa using hj12.symm
  · exact hj23
  · have hjend :
        (T.path D.j).walk.getVert 4 = T.y := by
      have h := (T.path D.j).walk.getVert_length
      rw [hjLength] at h
      exact h
    simpa [hjend] using hj34.symm
  · simpa [E.r_eq_two] using D.adj_r.symm
  · simpa [E.s_eq_two] using D.adj_s.symm

private theorem exactAttachment_induces_oneSubdivisionK4
    [Fintype V] [DecidableEq V]
    (T : Theta G)
    (hgirth : GirthAtLeast G 6)
    (v : V) (hv : v ∉ T.verts)
    (D : AttachmentData T v)
    (E : ExactAttachmentLengths T v D) :
    InducesOneSubdivisionK4 G (insert v T.verts) := by
  let f := locationValue T v D
  have hinj : Function.Injective f := by
    simpa [f] using locationValue_injective T v hv D E
  have himage :
      Finset.univ.image f = insert v T.verts := by
    simpa [f] using locationValue_image T v D E
  have hcardImage :=
    Finset.card_image_of_injective Finset.univ hinj
  have hcard : (insert v T.verts).card = 10 := by
    rw [himage, Finset.card_univ,
      ThetaMinimumAttachment.canonical_vertex_count] at hcardImage
    exact hcardImage
  apply ThetaMinimumAttachment.induces_of_spanning_labeled_hom
    hgirth f himage hcard
  intro z w hzw
  change G.Adj
    (locationValue T v D z)
    (locationValue T v D w)
  rw [locationValue_eq_attachmentModelMap T v D E]
  exact attachmentModelMap_map_adj T v D E hzw

/--
Let `T` be a minimum-order theta in a finite simple graph of girth at least
six.  If a vertex outside `T` has two neighbors on `T`, then that vertex
together with the theta vertices induces the one-subdivision of `K₄`.

This is the attachment conclusion of GHLM Lemma 5.10, derived here from
the minimum-theta comparison arguments rather than assumed as an external
input.
-/
theorem minimumOrder_attachment_induces_oneSubdivisionK4
    [Fintype V] [DecidableEq V]
    (T : Theta G)
    (hgirth : GirthAtLeast G 6)
    (hminimum : T.IsMinimumOrder)
    (v : V) (hv : v ∉ T.verts)
    (hdegree :
      2 ≤ (G.neighborSet v ∩
        (↑T.verts : Set V)).ncard) :
    InducesOneSubdivisionK4 G (insert v T.verts) := by
  obtain ⟨D⟩ :=
    exists_attachmentData T hminimum hgirth v hv hdegree
  have hsegments :
      D.r ≤ 2 ∧ D.s ≤ 2 ∧
        (T.path D.i).length - D.r ≤ 2 ∧
        (T.path D.j).length - D.s ≤ 2 :=
    T.minimumOrder_outside_chord_segment_bounds
      hminimum v hv
      D.i_ne_j D.i_ne_k D.j_ne_k
      D.r D.s D.r_pos D.r_lt D.s_pos D.s_lt
      D.adj_r D.adj_s
  have hthird : (T.path D.k).length ≤ 2 :=
    T.minimumOrder_thirdLeg_length_le_two_of_outside_chord
      hminimum v hv
      D.i_ne_j D.i_ne_k D.j_ne_k
      D.r D.s D.r_pos D.r_lt D.s_pos D.s_lt
      D.adj_r D.adj_s
  let E :=
    exactAttachmentLengths
      T hminimum hgirth v hv D hsegments hthird
  exact exactAttachment_induces_oneSubdivisionK4
    T hgirth v hv D E

end Theta

end DeanK5
