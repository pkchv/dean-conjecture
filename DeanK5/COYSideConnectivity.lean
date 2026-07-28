import DeanK5.COYCutDecomposition
import DeanK5.COYSideInstance
import DeanK5.ThreeSeparator

/-!
# Rooted connectivity of one side of a cut vertex

This file supplies the connectivity step in COY Claim 3.2(1).  Suppose
`G ⊔ edge x y` is 2-connected, while a component `Q` of `G - c`
contains `x` but not `y`.  Putting `c` back on the `Q` side and adjoining
the edge `xc` gives a 2-connected rooted auxiliary graph, provided that
the side contains one vertex besides `x`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

private theorem isTwoConnected_of_iso
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {H : SimpleGraph A} {K : SimpleGraph B}
    (e : H ≃g K)
    (hH : IsTwoConnected H) :
    IsTwoConnected K := by
  constructor
  · rw [← e.card_eq]
    exact hH.1
  · intro S hS
    let R : Finset A := S.image e.symm
    have hRcard : R.card < 2 :=
      Finset.card_image_le.trans_lt hS
    have hconnected := hH.2 R hRcard
    let eDeleted :
        H.induce {a | a ∉ R} ≃g
          K.induce {b | b ∉ S} := {
      toFun a := ⟨e a.1, by
        intro heaS
        apply a.2
        exact Finset.mem_image.mpr
          ⟨e a.1, heaS, by simp⟩⟩
      invFun b := ⟨e.symm b.1, by
        intro hebR
        obtain ⟨w, hwS, hw⟩ :=
          Finset.mem_image.mp hebR
        apply b.2
        have : w = b.1 := by
          apply e.symm.injective
          exact hw
        simpa [this] using hwS⟩
      left_inv a := by
        apply Subtype.ext
        simp
      right_inv b := by
        apply Subtype.ext
        simp
      map_rel_iff' := by
        intro a b
        exact e.map_rel_iff
    }
    exact (SimpleGraph.Iso.connected_iff eDeleted).mp
      hconnected

/--
The side of a cut vertex containing `x`, rooted at `x` and the cut
vertex, is 2-connected after the root edge is adjoined.

The final hypothesis is necessary for the project's order-at-least-three
convention for 2-connectivity.  In the COY induction it is supplied by
the choice of a side containing an ordinary vertex.
-/
theorem one_cut_root_side_two_connected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y c : V)
    (hQ : ComponentRegion G {c} Q)
    (hxQ : x ∈ Q) (hyQ : y ∉ Q)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hside : ∃ v ∈ Q, v ≠ x) :
    IsTwoConnected (twoRootComponentGraph G Q x c) := by
  have hxc : x ≠ c := by
    intro h
    exact hQ.not_mem_separator hxQ (by simp [h])
  constructor
  · obtain ⟨v, hvQ, hvx⟩ := hside
    have hvc : v ≠ c := by
      intro h
      exact hQ.not_mem_separator hvQ (by simp [h])
    have hthree : ({v, x, c} : Finset V).card = 3 := by
      simp [hvx, hvc, hxc]
    have hsub :
        ({v, x, c} : Finset V) ⊆ twoRootVertices Q x c := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;>
        simp [twoRootVertices, hvQ, hxQ]
    have hcard : 3 ≤ (twoRootVertices Q x c).card := by
      rw [← hthree]
      exact Finset.card_le_card hsub
    simpa using hcard
  · intro T hT
    have hTle : T.card ≤ 1 := by omega
    by_cases hcT : twoRootY Q x c ∈ T
    · have hTsub :
          ∀ t ∈ T, t = twoRootY Q x c :=
        fun t ht => Finset.card_le_one.mp hTle
          t ht _ hcT
      obtain ⟨q, hqQ⟩ := hQ.nonempty
      have hqc : q ≠ c := by
        intro h
        exact hQ.not_mem_separator hqQ (by simp [h])
      let qU : (↑(twoRootVertices Q x c) : Set V) :=
        ⟨q, by simp [twoRootVertices, hqQ]⟩
      have hqT : qU ∉ T := by
        intro hmem
        have heq := hTsub qU hmem
        exact hqc (by
          simpa [qU, twoRootY] using
            congrArg Subtype.val heq)
      let f :
          G.induce (↑Q : Set V) →g
            (twoRootComponentGraph G Q x c).induce
              {w | w ∉ T} := {
        toFun w := by
          let wU : (↑(twoRootVertices Q x c) : Set V) :=
            ⟨w.1, by simp [twoRootVertices, w.2]⟩
          have hwc : w.1 ≠ c := by
            intro hw
            exact hQ.not_mem_separator w.2 (by simp [hw])
          have hwT : wU ∉ T := by
            intro hmem
            have heq := hTsub wU hmem
            exact hwc (by
              simpa [wU, twoRootY] using
                congrArg Subtype.val heq)
          exact ⟨wU, hwT⟩
        map_rel' := by
          intro a b hab
          exact Or.inl hab
      }
      rw [connected_iff_exists_forall_reachable]
      refine ⟨⟨qU, hqT⟩, ?_⟩
      rintro ⟨⟨w, hwU⟩, hwT⟩
      have hwClass : w ∈ Q ∨ w = x ∨ w = c := by
        have h : w = x ∨ w = c ∨ w ∈ Q := by
          simpa [twoRootVertices] using hwU
        tauto
      have hwQ : w ∈ Q := by
        rcases hwClass with hwQ | rfl | rfl
        · exact hwQ
        · exact hxQ
        · exact False.elim (hwT hcT)
      have hreach :=
        (hQ.connected.preconnected
          (⟨q, hqQ⟩ : (↑Q : Set V))
          (⟨w, hwQ⟩ : (↑Q : Set V))).map f
      simpa [f, qU] using hreach
    · let R : Finset V := T.image Subtype.val
      have hRcard : R.card < 2 :=
        Finset.card_image_le.trans_lt hT
      have hcR : c ∉ R := by
        intro h
        obtain ⟨t, htT, ht⟩ := Finset.mem_image.mp h
        have htc : t = twoRootY Q x c := by
          apply Subtype.ext
          simpa [twoRootY] using ht
        exact hcT (htc ▸ htT)
      have hdeleted := hconn.2 R hRcard
      let cD :
          {w : (↑(twoRootVertices Q x c) : Set V) // w ∉ T} :=
        ⟨twoRootY Q x c, hcT⟩
      let rec go {a : V}
          (haQ : a ∈ Q) (haR : a ∉ R)
          (p : (G ⊔ edge x y).Walk a c)
          (havoid : ∀ w ∈ p.support, w ∉ R) :
          ((twoRootComponentGraph G Q x c).induce
            {w | w ∉ T}).Reachable
            ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
              intro haT
              exact haR (Finset.mem_image.mpr
                ⟨⟨a, by simp [twoRootVertices, haQ]⟩,
                  haT, rfl⟩)⟩
            cD := by
        cases p with
        | nil =>
            exact False.elim
              (hQ.not_mem_separator haQ (by simp))
        | cons hab p =>
            rename_i b
            have hbR : b ∉ R :=
              havoid b (by simp)
            by_cases hbQ : b ∈ Q
            · have htail :
                  ∀ w ∈ p.support, w ∉ R := by
                intro w hw
                exact havoid w (by simp [hw])
              rcases hab with habG | habEdge
              · have ih := go hbQ hbR p htail
                have hadj :
                    ((twoRootComponentGraph G Q x c).induce
                      {w | w ∉ T}).Adj
                      ⟨⟨a, by
                        simp [twoRootVertices, haQ]⟩, by
                        intro haT
                        exact haR (Finset.mem_image.mpr
                          ⟨⟨a, by
                            simp [twoRootVertices, haQ]⟩,
                            haT, rfl⟩)⟩
                      ⟨⟨b, by
                        simp [twoRootVertices, hbQ]⟩, by
                        intro hbT
                        exact hbR (Finset.mem_image.mpr
                          ⟨⟨b, by
                            simp [twoRootVertices, hbQ]⟩,
                            hbT, rfl⟩)⟩ :=
                  Or.inl habG
                exact hadj.reachable.trans ih
              · simp only [SimpleGraph.edge_adj] at habEdge
                rcases habEdge with
                  ⟨hax, hby⟩ | ⟨hay, hbx⟩
                · exact False.elim (hyQ (hby ▸ hbQ))
                · exact False.elim (hyQ (hay ▸ haQ))
            · rcases hab with habG | habEdge
              · have hbc : b = c := by
                  by_contra hbc
                  apply hbQ
                  exact hQ.closed haQ habG (by simpa using hbc)
                subst b
                have hadj :
                    ((twoRootComponentGraph G Q x c).induce
                      {w | w ∉ T}).Adj
                      ⟨⟨a, by
                        simp [twoRootVertices, haQ]⟩, by
                        intro haT
                        exact haR (Finset.mem_image.mpr
                          ⟨⟨a, by
                            simp [twoRootVertices, haQ]⟩,
                            haT, rfl⟩)⟩
                      cD :=
                  Or.inl habG
                exact hadj.reachable
              · simp only [SimpleGraph.edge_adj] at habEdge
                rcases habEdge with
                  ⟨hax, hby⟩ | ⟨hay, hbx⟩
                · subst a
                  subst b
                  have hroot :=
                    twoRootComponentGraph_roots_adj
                      G Q hxc
                  have hrootDeleted :
                      ((twoRootComponentGraph G Q x c).induce
                        {w | w ∉ T}).Adj
                        ⟨twoRootX Q x c, by
                          intro hxT
                          exact haR (Finset.mem_image.mpr
                            ⟨twoRootX Q x c, hxT, rfl⟩)⟩
                        cD :=
                    hroot
                  simpa [cD, twoRootX] using
                    hrootDeleted.reachable
                · exact False.elim (hyQ (hay ▸ haQ))
      rw [connected_iff_exists_forall_reachable]
      refine ⟨cD, ?_⟩
      rintro ⟨⟨v, hvU⟩, hvT⟩
      have hvClass : v ∈ Q ∨ v = x ∨ v = c := by
        have h : v = x ∨ v = c ∨ v ∈ Q := by
          simpa [twoRootVertices] using hvU
        tauto
      rcases hvClass with hvQ | hvx | hvc
      · have hvR : v ∉ R := by
          intro h
          obtain ⟨t, htT, ht⟩ :=
            Finset.mem_image.mp h
          have htv :
              t =
                (⟨v, by
                  simp [twoRootVertices, hvQ]⟩ :
                  (↑(twoRootVertices Q x c) : Set V)) := by
            apply Subtype.ext
            exact ht
          exact hvT (htv ▸ htT)
        obtain ⟨p⟩ :=
          hdeleted.preconnected
            ⟨v, hvR⟩ ⟨c, hcR⟩
        let pH : (G ⊔ edge x y).Walk v c :=
          p.map (Embedding.induce _).toHom
        have havoid :
            ∀ w ∈ pH.support, w ∉ R := by
          intro w hw
          change w ∈
            (p.map (Embedding.induce _).toHom).support at hw
          rw [SimpleGraph.Walk.support_map] at hw
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
          exact a.property
        simpa [cD] using
          (go hvQ hvR pH havoid).symm
      · subst v
        have hxR : x ∉ R := by
          intro h
          obtain ⟨t, htT, ht⟩ :=
            Finset.mem_image.mp h
          have htx :
              t =
                (⟨x, hvU⟩ :
                  (↑(twoRootVertices Q x c) : Set V)) := by
            apply Subtype.ext
            exact ht
          exact hvT (htx ▸ htT)
        obtain ⟨p⟩ :=
          hdeleted.preconnected
            ⟨x, hxR⟩ ⟨c, hcR⟩
        let pH : (G ⊔ edge x y).Walk x c :=
          p.map (Embedding.induce _).toHom
        have havoid :
            ∀ w ∈ pH.support, w ∉ R := by
          intro w hw
          change w ∈
            (p.map (Embedding.induce _).toHom).support at hw
          rw [SimpleGraph.Walk.support_map] at hw
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
          exact a.property
        simpa [cD, twoRootX] using
          (go hxQ hxR pH havoid).symm
      · subst v
        exact .rfl

namespace COY

namespace CutSide

/--
The cut-side graph in the exact carrier used by the COY recursive
instance is rooted 2-connected after adjoining its root edge.
-/
theorem graph_sup_root_cut_two_connected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y c : V)
    (hQ : ComponentRegion G {c} Q)
    (hxQ : x ∈ Q) (hyQ : y ∉ Q)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hside : ∃ v ∈ Q, v ≠ x) :
    IsTwoConnected
      (COY.CutSide.graph G Q c ⊔
        edge (COY.CutSide.root Q c x hxQ)
          (COY.CutSide.cut Q c)) := by
  let carrierEquiv :
      (↑(twoRootVertices Q x c) : Set V) ≃
        COY.CutSide.Vertex Q c := {
    toFun a := ⟨a.1, by
      change a.1 ∈ insert c Q
      have ha := a.2
      change a.1 ∈ Q ∪ {x, c} at ha
      rcases Finset.mem_union.mp ha with haQ | haRoots
      · exact Finset.mem_insert_of_mem haQ
      · simp only [Finset.mem_insert,
          Finset.mem_singleton] at haRoots
        rcases haRoots with hax | hac
        · exact Finset.mem_insert_of_mem (hax.symm ▸ hxQ)
        · exact Finset.mem_insert.mpr (Or.inl hac)⟩
    invFun a := ⟨a.1, by
      change a.1 ∈ Q ∪ {x, c}
      have ha := a.2
      change a.1 ∈ insert c Q at ha
      rcases Finset.mem_insert.mp ha with hac | haQ
      · exact Finset.mem_union.mpr
          (Or.inr (by simp [hac]))
      · exact Finset.mem_union.mpr (Or.inl haQ)⟩
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv a := by
      apply Subtype.ext
      rfl
  }
  let sideIso :
      twoRootComponentGraph G Q x c ≃g
        (COY.CutSide.graph G Q c ⊔
          edge (COY.CutSide.root Q c x hxQ)
            (COY.CutSide.cut Q c)) := {
    __ := carrierEquiv
    map_rel_iff' := by
      intro a b
      simp only [twoRootComponentGraph,
        COY.CutSide.graph, SimpleGraph.sup_adj]
      simp only [SimpleGraph.edge_adj, Subtype.ext_iff]
      simp [carrierEquiv,
        COY.CutSide.root, COY.CutSide.innerVertex,
        COY.CutSide.cut]
  }
  exact isTwoConnected_of_iso sideIso
    (one_cut_root_side_two_connected
      G Q x y c hQ hxQ hyQ hconn hside)

end CutSide

end COY

end DeanK5
