import DeanK5.Graph.Separation
import DeanK5.RootLifting

/-!
# From 3-connectivity to 4-connectivity (paper Section 4)

This file formalizes paper Lemma 4.1.  A component `Q` of
`J - {x,y,z}` is put back together with roots `x,y`, and the edge `xy` is
added.  The proof checks connectivity after every deletion of fewer than two
vertices.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/-- Vertices of one component together with two chosen separator roots. -/
def twoRootVertices [DecidableEq V]
    (Q : Finset V) (x y : V) : Finset V :=
  Q ∪ {x, y}

/-- The graph `J[Q ∪ {x,y}] + xy` appearing in Lemma 4.1. -/
def twoRootComponentGraph [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y : V) :
    SimpleGraph (↑(twoRootVertices Q x y) : Set V) :=
  let rx : (↑(twoRootVertices Q x y) : Set V) := ⟨x, by
    simp [twoRootVertices]⟩
  let ry : (↑(twoRootVertices Q x y) : Set V) := ⟨y, by
    simp [twoRootVertices]⟩
  G.induce (↑(twoRootVertices Q x y) : Set V) ⊔ edge rx ry

/-- The copy of `x` in the two-root component carrier. -/
def twoRootX [DecidableEq V]
    (Q : Finset V) (x y : V) :
    (↑(twoRootVertices Q x y) : Set V) :=
  ⟨x, by simp [twoRootVertices]⟩

/-- The copy of `y` in the two-root component carrier. -/
def twoRootY [DecidableEq V]
    (Q : Finset V) (x y : V) :
    (↑(twoRootVertices Q x y) : Set V) :=
  ⟨y, by simp [twoRootVertices]⟩

/-- The rooted component graph with the possible root edge removed. -/
def twoRootComponentBase [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y : V) :
    SimpleGraph (↑(twoRootVertices Q x y) : Set V) :=
  G.induce (↑(twoRootVertices Q x y) : Set V) \
    edge (twoRootX Q x y) (twoRootY Q x y)

/-- The rooted component base embeds in its ambient graph by forgetting
the induced-subgraph subtype. -/
def twoRootComponentBaseHom [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y : V) :
    twoRootComponentBase G Q x y →g G where
  toFun z := z.1
  map_rel' := by
    intro a b hab
    exact hab.1

theorem twoRootComponentBaseHom_injective [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y : V) :
    Function.Injective (twoRootComponentBaseHom G Q x y) := by
  intro a b hab
  exact Subtype.ext hab

@[simp] theorem twoRootComponentBase_sup_edge [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y : V) :
    twoRootComponentBase G Q x y ⊔
        edge (twoRootX Q x y) (twoRootY Q x y) =
      twoRootComponentGraph G Q x y := by
  ext a b
  simp only [twoRootComponentBase, twoRootComponentGraph,
    SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  tauto

@[nolint unusedArguments]
theorem finiteDegree_twoRootComponentBase_inner
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y v : V)
    (hvQ : v ∈ Q) (hvx : v ≠ x) (hvy : v ≠ y) :
    finiteDegree (twoRootComponentBase G Q x y)
        (⟨v, by simp [twoRootVertices, hvQ]⟩ :
          (↑(twoRootVertices Q x y) : Set V)) =
      finiteDegree (G.induce (↑(twoRootVertices Q x y) : Set V))
        (⟨v, by simp [twoRootVertices, hvQ]⟩ :
          (↑(twoRootVertices Q x y) : Set V)) := by
  unfold finiteDegree
  congr 1
  ext w
  simp [twoRootComponentBase, SimpleGraph.sdiff_adj,
    SimpleGraph.edge_adj, twoRootX, twoRootY, hvx, hvy]

/--
An inner vertex of a component behind the two-vertex separator `{x,y}`
keeps all of its ambient neighbors in the rooted component base.
-/
theorem finiteDegree_le_twoRootComponentBase_of_two_separator
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y v : V)
    (hQ : ComponentRegion G {x, y} Q)
    (hvQ : v ∈ Q) :
    finiteDegree G v ≤
      finiteDegree (twoRootComponentBase G Q x y)
        (⟨v, by simp [twoRootVertices, hvQ]⟩ :
          (↑(twoRootVertices Q x y) : Set V)) := by
  let U : Set V := ↑(twoRootVertices Q x y)
  let vU : U :=
    ⟨v, by simp [U, twoRootVertices, hvQ]⟩
  have hvS : v ∉ ({x, y} : Finset V) :=
    hQ.not_mem_separator hvQ
  have hvx : v ≠ x := by
    intro h
    exact hvS (by simp [h])
  have hvy : v ≠ y := by
    intro h
    exact hvS (by simp [h])
  have hinside :
      ∀ w, G.Adj v w → w ∈ U := by
    intro w hvw
    by_cases hwS : w ∈ ({x, y} : Finset V)
    · simp only [Finset.mem_insert,
        Finset.mem_singleton] at hwS
      rcases hwS with rfl | rfl <;>
        simp [U, twoRootVertices]
    · have hwQ := hQ.closed hvQ hvw hwS
      simp [U, twoRootVertices, hwQ]
  have hdegree :=
    finiteDegree_le_induce G U vU hinside
  rw [← finiteDegree_twoRootComponentBase_inner
    G Q x y v hvQ hvx hvy] at hdegree
  exact hdegree

/-- An inner component vertex loses at most its possible edge to `z`. -/
theorem finiteDegree_le_twoRootComponentBase_add_one
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y z v : V)
    (hQ : ComponentRegion G {x, y, z} Q)
    (hvQ : v ∈ Q) :
    finiteDegree G v ≤
      finiteDegree (twoRootComponentBase G Q x y)
        (⟨v, by simp [twoRootVertices, hvQ]⟩ :
          (↑(twoRootVertices Q x y) : Set V)) + 1 := by
  let U : Set V := ↑(twoRootVertices Q x y)
  let vU : U := ⟨v, by simp [U, twoRootVertices, hvQ]⟩
  have hvS : v ∉ ({x, y, z} : Finset V) :=
    hQ.not_mem_separator hvQ
  have hvx : v ≠ x := by
    intro h
    exact hvS (by simp [h])
  have hvy : v ≠ y := by
    intro h
    exact hvS (by simp [h])
  have houtside :
      ∀ w, G.Adj v w → w ∉ U → w = z := by
    intro w hvw hwU
    have hwS : w ∈ ({x, y, z} : Finset V) := by
      by_contra hwNotS
      have hwQ := hQ.closed hvQ hvw hwNotS
      exact hwU (by simp [U, twoRootVertices, hwQ])
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwS
    rcases hwS with hwx | hwy | hwz
    · exact False.elim (hwU (by simp [U, twoRootVertices, hwx]))
    · exact False.elim (hwU (by simp [U, twoRootVertices, hwy]))
    · exact hwz
  have hdegree :=
    finiteDegree_le_induce_add_one G U vU z houtside
  rw [← finiteDegree_twoRootComponentBase_inner
    G Q x y v hvQ hvx hvy] at hdegree
  exact hdegree

@[simp] theorem twoRootComponentGraph_roots_adj [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) {x y : V} (hxy : x ≠ y) :
    (twoRootComponentGraph G Q x y).Adj
      (twoRootX Q x y) (twoRootY Q x y) := by
  exact Or.inr (by simpa [edge, twoRootX, twoRootY] using hxy)

private theorem connected_after_deleted_root
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S Q : Finset V)
    (hQ : ComponentRegion G S Q)
    (x y : V) (hxS : x ∈ S) (hyS : y ∈ S)
    (hxy : x ≠ y)
    (q : V) (hqQ : q ∈ Q) (hqy : G.Adj q y)
    (T : Finset (↑(twoRootVertices Q x y) : Set V))
    (hT : T.card < 2) (hxT : twoRootX Q x y ∈ T) :
    ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Connected := by
  have hTle : T.card ≤ 1 := by omega
  have hTsub : ∀ t ∈ T, t = twoRootX Q x y :=
    fun t ht => Finset.card_le_one.mp hTle t ht _ hxT
  have hyT : twoRootY Q x y ∉ T := by
    intro hy
    have heq := hTsub _ hy
    exact hxy (by simpa [twoRootX, twoRootY] using heq.symm)
  have hqS : q ∉ S := hQ.not_mem_separator hqQ
  have hq_ne_x : q ≠ x := fun h => hqS (h ▸ hxS)
  have hq_ne_y : q ≠ y := fun h => hqS (h ▸ hyS)
  let qU : (↑(twoRootVertices Q x y) : Set V) :=
    ⟨q, by simp [twoRootVertices, hqQ]⟩
  have hqT : qU ∉ T := by
    intro hmem
    have heq := hTsub qU hmem
    exact hq_ne_x (by simpa [qU, twoRootX] using congrArg Subtype.val heq)
  let f :
      G.induce (↑Q : Set V) →g
        (twoRootComponentGraph G Q x y).induce {v | v ∉ T} := {
    toFun v := by
      let vU : (↑(twoRootVertices Q x y) : Set V) :=
        ⟨v.1, by simp [twoRootVertices, v.2]⟩
      have hvS : v.1 ∉ S := hQ.not_mem_separator v.2
      have hvx : v.1 ≠ x := fun h => hvS (h ▸ hxS)
      have hvT : vU ∉ T := by
        intro hmem
        have heq := hTsub vU hmem
        exact hvx (by
          simpa [vU, twoRootX] using congrArg Subtype.val heq)
      exact ⟨vU, hvT⟩
    map_rel' := by
      intro a b hab
      exact Or.inl hab
  }
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨twoRootY Q x y, hyT⟩, ?_⟩
  rintro ⟨⟨v, hvU⟩, hvT⟩
  have hvClass : v ∈ Q ∨ v = x ∨ v = y := by
    have h : v = x ∨ v = y ∨ v ∈ Q := by
      simpa [twoRootVertices] using hvU
    tauto
  rcases hvClass with hvQ | rfl | rfl
  · have hreachQ :=
      (hQ.connected.preconnected ⟨q, hqQ⟩ ⟨v, hvQ⟩).map f
    have hqy' :
        ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
          ⟨qU, hqT⟩ ⟨twoRootY Q x y, hyT⟩ :=
      Or.inl hqy
    simpa [f, qU] using hqy'.reachable.symm.trans hreachQ
  · exact False.elim (hvT hxT)
  · exact .rfl

private theorem connected_after_deleted_second_root
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S Q : Finset V)
    (hQ : ComponentRegion G S Q)
    (x y : V) (_hxS : x ∈ S) (hyS : y ∈ S)
    (hxy : x ≠ y)
    (q : V) (hqQ : q ∈ Q) (hqx : G.Adj q x)
    (T : Finset (↑(twoRootVertices Q x y) : Set V))
    (hT : T.card < 2) (hyT : twoRootY Q x y ∈ T) :
    ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Connected := by
  have hTle : T.card ≤ 1 := by omega
  have hTsub : ∀ t ∈ T, t = twoRootY Q x y :=
    fun t ht => Finset.card_le_one.mp hTle t ht _ hyT
  have hxT : twoRootX Q x y ∉ T := by
    intro hx
    have heq := hTsub _ hx
    exact hxy (by simpa [twoRootX, twoRootY] using heq)
  have hqS : q ∉ S := hQ.not_mem_separator hqQ
  have hq_ne_y : q ≠ y := fun h => hqS (h ▸ hyS)
  let qU : (↑(twoRootVertices Q x y) : Set V) :=
    ⟨q, by simp [twoRootVertices, hqQ]⟩
  have hqT : qU ∉ T := by
    intro hmem
    have heq := hTsub qU hmem
    exact hq_ne_y (by simpa [qU, twoRootY] using congrArg Subtype.val heq)
  let f :
      G.induce (↑Q : Set V) →g
        (twoRootComponentGraph G Q x y).induce {v | v ∉ T} := {
    toFun v := by
      let vU : (↑(twoRootVertices Q x y) : Set V) :=
        ⟨v.1, by simp [twoRootVertices, v.2]⟩
      have hvS : v.1 ∉ S := hQ.not_mem_separator v.2
      have hvy : v.1 ≠ y := fun h => hvS (h ▸ hyS)
      have hvT : vU ∉ T := by
        intro hmem
        have heq := hTsub vU hmem
        exact hvy (by
          simpa [vU, twoRootY] using congrArg Subtype.val heq)
      exact ⟨vU, hvT⟩
    map_rel' := by
      intro a b hab
      exact Or.inl hab
  }
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨twoRootX Q x y, hxT⟩, ?_⟩
  rintro ⟨⟨v, hvU⟩, hvT⟩
  have hvClass : v ∈ Q ∨ v = x ∨ v = y := by
    have h : v = x ∨ v = y ∨ v ∈ Q := by
      simpa [twoRootVertices] using hvU
    tauto
  rcases hvClass with hvQ | hvx | hvy
  · have hreachQ :=
      (hQ.connected.preconnected ⟨q, hqQ⟩ ⟨v, hvQ⟩).map f
    have hqx' :
        ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
          ⟨qU, hqT⟩ ⟨twoRootX Q x y, hxT⟩ :=
      Or.inl hqx
    simpa [f, qU] using hqx'.reachable.symm.trans hreachQ
  · subst v
    exact .rfl
  · subst v
    exact False.elim (hvT hyT)

private theorem connected_when_roots_survive_two_separator
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y : V) (hxy : x ≠ y)
    (hQ : ComponentRegion G {x, y} Q)
    (hconn : IsKConnected G 2)
    (T : Finset (↑(twoRootVertices Q x y) : Set V))
    (hT : T.card < 2)
    (hxT : twoRootX Q x y ∉ T)
    (hyT : twoRootY Q x y ∉ T) :
    ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Connected := by
  let R : Finset V := T.image Subtype.val
  have hRcard : R.card < 2 := by
    exact (Finset.card_image_le.trans_lt hT)
  have hxImage : x ∉ R := by
    intro h
    obtain ⟨t, htT, ht⟩ := Finset.mem_image.mp h
    have htx : t = twoRootX Q x y := by
      apply Subtype.ext
      simpa [twoRootX] using ht
    exact hxT (htx ▸ htT)
  have hyImage : y ∉ R := by
    intro h
    obtain ⟨t, htT, ht⟩ := Finset.mem_image.mp h
    have hty : t = twoRootY Q x y := by
      apply Subtype.ext
      simpa [twoRootY] using ht
    exact hyT (hty ▸ htT)
  have hdeletedG := hconn.2 R hRcard
  let rxD :
      {v : (↑(twoRootVertices Q x y) : Set V) // v ∉ T} :=
    ⟨twoRootX Q x y, hxT⟩
  let ryD :
      {v : (↑(twoRootVertices Q x y) : Set V) // v ∉ T} :=
    ⟨twoRootY Q x y, hyT⟩
  have hrootEdge :
      ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
        ryD rxD := by
    exact (twoRootComponentGraph_roots_adj G Q hxy).symm
  let rec go {a : V} (haQ : a ∈ Q) (haR : a ∉ R)
      (p : G.Walk a x)
      (havoid : ∀ v ∈ p.support, v ∉ R) :
      ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Reachable
        ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
          intro haT
          have haImage : a ∈ R :=
            Finset.mem_image.mpr
              ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
          exact haR haImage⟩
        rxD := by
    cases p with
    | nil =>
        exact False.elim
          (hQ.not_mem_separator haQ (by simp))
    | cons hab p =>
        rename_i b
        have hbR : b ∉ R := havoid b (by simp)
        by_cases hbQ : b ∈ Q
        · have htail :
              ∀ v ∈ p.support, v ∉ R := by
            intro v hv
            exact havoid v (by simp [hv])
          have ih := go hbQ hbR p htail
          have hadj :
              ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
                ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
                  intro haT
                  have haImage : a ∈ R :=
                    Finset.mem_image.mpr
                      ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
                  exact haR haImage⟩
                ⟨⟨b, by simp [twoRootVertices, hbQ]⟩, by
                  intro hbT
                  have hbImage : b ∈ R :=
                    Finset.mem_image.mpr
                      ⟨⟨b, by simp [twoRootVertices, hbQ]⟩, hbT, rfl⟩
                  exact hbR hbImage⟩ :=
            Or.inl hab
          exact hadj.reachable.trans ih
        · have hbS : b ∈ ({x, y} : Finset V) := by
            by_contra hbnotS
            exact hbQ (hQ.closed haQ hab hbnotS)
          have hbxy : b = x ∨ b = y := by
            simpa only [Finset.mem_insert,
              Finset.mem_singleton] using hbS
          rcases hbxy with hbx | hby
          · subst b
            have hadj :
                ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
                  ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
                    intro haT
                    have haImage : a ∈ R :=
                      Finset.mem_image.mpr
                        ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
                    exact haR haImage⟩
                  rxD :=
              Or.inl hab
            exact hadj.reachable
          · subst b
            have hadj :
                ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
                  ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
                    intro haT
                    have haImage : a ∈ R :=
                      Finset.mem_image.mpr
                        ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
                    exact haR haImage⟩
                  ryD :=
              Or.inl hab
            exact hadj.reachable.trans hrootEdge.reachable
  rw [connected_iff_exists_forall_reachable]
  refine ⟨rxD, ?_⟩
  rintro ⟨⟨v, hvU⟩, hvT⟩
  have hvClass : v ∈ Q ∨ v = x ∨ v = y := by
    have h : v = x ∨ v = y ∨ v ∈ Q := by
      simpa [twoRootVertices] using hvU
    tauto
  rcases hvClass with hvQ | hvx | hvy
  · have hvImage : v ∉ R := by
      intro h
      obtain ⟨t, htT, ht⟩ := Finset.mem_image.mp h
      have htv :
          t = (⟨v, by simp [twoRootVertices, hvQ]⟩ :
            (↑(twoRootVertices Q x y) : Set V)) := by
        apply Subtype.ext
        exact ht
      exact hvT (htv ▸ htT)
    obtain ⟨p⟩ :=
      hdeletedG.preconnected ⟨v, hvImage⟩ ⟨x, hxImage⟩
    let pG : G.Walk v x := p.map (Embedding.induce _).toHom
    have havoid : ∀ w ∈ pG.support, w ∉ R := by
      intro w hw
      change w ∈ (p.map (Embedding.induce _).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
      exact a.property
    simpa [rxD] using (go hvQ hvImage pG havoid).symm
  · subst v
    exact .rfl
  · subst v
    exact hrootEdge.reachable.symm

private theorem connected_when_roots_survive
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ : ComponentRegion G {x, y, z} Q)
    (hconn : IsKConnected G 3)
    (T : Finset (↑(twoRootVertices Q x y) : Set V))
    (hT : T.card < 2)
    (hxT : twoRootX Q x y ∉ T)
    (hyT : twoRootY Q x y ∉ T) :
    ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Connected := by
  let R : Finset V := insert z (T.image Subtype.val)
  have hRcard : R.card < 3 := by
    calc
      R.card ≤ 1 + (T.image Subtype.val).card := by
        simpa [R, Nat.add_comm] using
          Finset.card_insert_le z (T.image Subtype.val)
      _ ≤ 1 + T.card := Nat.add_le_add_left Finset.card_image_le 1
      _ < 3 := by omega
  have hxImage : x ∉ T.image Subtype.val := by
    intro h
    obtain ⟨t, htT, ht⟩ := Finset.mem_image.mp h
    have htx : t = twoRootX Q x y := by
      apply Subtype.ext
      simpa [twoRootX] using ht
    exact hxT (htx ▸ htT)
  have hyImage : y ∉ T.image Subtype.val := by
    intro h
    obtain ⟨t, htT, ht⟩ := Finset.mem_image.mp h
    have hty : t = twoRootY Q x y := by
      apply Subtype.ext
      simpa [twoRootY] using ht
    exact hyT (hty ▸ htT)
  have hxR : x ∉ R := by
    simp [R, hxz, hxImage]
  have hyR : y ∉ R := by
    simp [R, hyz, hyImage]
  have hdeletedG := hconn.2 R hRcard
  let rxD :
      {v : (↑(twoRootVertices Q x y) : Set V) // v ∉ T} :=
    ⟨twoRootX Q x y, hxT⟩
  let ryD :
      {v : (↑(twoRootVertices Q x y) : Set V) // v ∉ T} :=
    ⟨twoRootY Q x y, hyT⟩
  have hrootEdge :
      ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
        ryD rxD := by
    exact (twoRootComponentGraph_roots_adj G Q hxy).symm
  let rec go {a : V} (haQ : a ∈ Q) (haR : a ∉ R)
      (p : G.Walk a x)
      (havoid : ∀ v ∈ p.support, v ∉ R) :
      ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Reachable
        ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
          intro haT
          have haImage : a ∈ T.image Subtype.val :=
            Finset.mem_image.mpr
              ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
          exact haR (by simp [R, haImage])⟩
        rxD := by
    cases p with
    | nil =>
        exact False.elim
          (hQ.not_mem_separator haQ (by simp))
    | cons hab p =>
        rename_i b
        have hbR : b ∉ R := havoid b (by simp)
        by_cases hbQ : b ∈ Q
        · have htail :
              ∀ v ∈ p.support, v ∉ R := by
            intro v hv
            exact havoid v (by simp [hv])
          have ih := go hbQ hbR p htail
          have hadj :
              ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
                ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
                  intro haT
                  have haImage : a ∈ T.image Subtype.val :=
                    Finset.mem_image.mpr
                      ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
                  exact haR (by simp [R, haImage])⟩
                ⟨⟨b, by simp [twoRootVertices, hbQ]⟩, by
                  intro hbT
                  have hbImage : b ∈ T.image Subtype.val :=
                    Finset.mem_image.mpr
                      ⟨⟨b, by simp [twoRootVertices, hbQ]⟩, hbT, rfl⟩
                  exact hbR (by simp [R, hbImage])⟩ :=
            Or.inl hab
          exact hadj.reachable.trans ih
        · have hbS : b ∈ ({x, y, z} : Finset V) := by
            by_contra hbnotS
            exact hbQ (hQ.closed haQ hab hbnotS)
          have hbz : b ≠ z := by
            intro h
            exact hbR (by simp [R, h])
          have hbxy : b = x ∨ b = y := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hbS
            rcases hbS with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact False.elim (hbz rfl)
          rcases hbxy with hbx | hby
          · subst b
            have hadj :
                ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
                  ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
                    intro haT
                    have haImage : a ∈ T.image Subtype.val :=
                      Finset.mem_image.mpr
                        ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
                    exact haR (by simp [R, haImage])⟩
                  rxD :=
              Or.inl hab
            exact hadj.reachable
          · subst b
            have hadj :
                ((twoRootComponentGraph G Q x y).induce {v | v ∉ T}).Adj
                  ⟨⟨a, by simp [twoRootVertices, haQ]⟩, by
                    intro haT
                    have haImage : a ∈ T.image Subtype.val :=
                      Finset.mem_image.mpr
                        ⟨⟨a, by simp [twoRootVertices, haQ]⟩, haT, rfl⟩
                    exact haR (by simp [R, haImage])⟩
                  ryD :=
              Or.inl hab
            exact hadj.reachable.trans hrootEdge.reachable
  rw [connected_iff_exists_forall_reachable]
  refine ⟨rxD, ?_⟩
  rintro ⟨⟨v, hvU⟩, hvT⟩
  have hvClass : v ∈ Q ∨ v = x ∨ v = y := by
    have h : v = x ∨ v = y ∨ v ∈ Q := by
      simpa [twoRootVertices] using hvU
    tauto
  rcases hvClass with hvQ | hvx | hvy
  · have hvS : v ∉ ({x, y, z} : Finset V) :=
      hQ.not_mem_separator hvQ
    have hvz : v ≠ z := by
      intro h
      exact hvS (by simp [h])
    have hvImage : v ∉ T.image Subtype.val := by
      intro h
      obtain ⟨t, htT, ht⟩ := Finset.mem_image.mp h
      have htv :
          t = (⟨v, by simp [twoRootVertices, hvQ]⟩ :
            (↑(twoRootVertices Q x y) : Set V)) := by
        apply Subtype.ext
        exact ht
      exact hvT (htv ▸ htT)
    have hvR : v ∉ R := by
      simp [R, hvz, hvImage]
    obtain ⟨p⟩ :=
      hdeletedG.preconnected ⟨v, hvR⟩ ⟨x, hxR⟩
    let pG : G.Walk v x := p.map (Embedding.induce _).toHom
    have havoid : ∀ w ∈ pG.support, w ∉ R := by
      intro w hw
      change w ∈ (p.map (Embedding.induce _).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
      exact a.property
    simpa [rxD] using (go hvQ hvR pG havoid).symm
  · subst v
    exact .rfl
  · subst v
    exact hrootEdge.reachable.symm

/--
For a component of a two-vertex deletion in a 2-connected graph, putting
the two boundary vertices back and adjoining their edge yields a
2-connected rooted auxiliary graph.

This is the minimum-cut claim used in the `k = 5`, `r = 1`
specialization of BGLP Lemma 2.3.
-/
theorem one_component_two_cut_roots
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y : V) (hxy : x ≠ y)
    (hQ : ComponentRegion G {x, y} Q)
    (hconn : IsTwoConnected G) :
    IsTwoConnected (twoRootComponentGraph G Q x y) := by
  have hScard : ({x, y} : Finset V).card = 2 := by
    simp [hxy]
  obtain ⟨qx, hqxQ, hqxx⟩ :=
    hQ.has_neighbor_at_each_vertex_of_two_separator
      hconn hScard (s := x) (by simp)
  obtain ⟨qy, hqyQ, hqyy⟩ :=
    hQ.has_neighbor_at_each_vertex_of_two_separator
      hconn hScard (s := y) (by simp)
  constructor
  · obtain ⟨q, hqQ⟩ := hQ.nonempty
    have hqS : q ∉ ({x, y} : Finset V) :=
      hQ.not_mem_separator hqQ
    have hqx : q ≠ x := by
      intro h
      exact hqS (by simp [h])
    have hqy : q ≠ y := by
      intro h
      exact hqS (by simp [h])
    have hsmall : ({q, x, y} : Finset V).card = 3 := by
      simp [hqx, hqy, hxy]
    have hsub :
        ({q, x, y} : Finset V) ⊆ twoRootVertices Q x y := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;>
        simp [twoRootVertices, hqQ]
    have hcard :
        3 ≤ (twoRootVertices Q x y).card := by
      rw [← hsmall]
      exact Finset.card_le_card hsub
    simpa using hcard
  · intro T hT
    by_cases hxT : twoRootX Q x y ∈ T
    · exact connected_after_deleted_root G {x, y} Q hQ
        x y (by simp) (by simp) hxy qy hqyQ hqyy T hT hxT
    by_cases hyT : twoRootY Q x y ∈ T
    · exact connected_after_deleted_second_root G {x, y} Q hQ
        x y (by simp) (by simp) hxy qx hqxQ hqxx T hT hyT
    · exact connected_when_roots_survive_two_separator
        G Q x y hxy hQ hconn T hT hxT hyT

/--
Paper Lemma 4.1 (one component and two separator roots).

The graph represented here is
`G[Q ∪ {x,y}] + xy`, which is definitionally the paper's
`A(Q;x,y) + xy`.
-/
theorem one_component_two_separator_roots
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ : ComponentRegion G {x, y, z} Q)
    (hconn : IsKConnected G 3) :
    IsTwoConnected (twoRootComponentGraph G Q x y) := by
  have hScard : ({x, y, z} : Finset V).card = 3 := by
    simp [hxy, hxz, hyz]
  obtain ⟨qx, hqxQ, hqxx⟩ :=
    hQ.has_neighbor_at_each_vertex_of_three_separator
      hconn hScard (s := x) (by simp)
  obtain ⟨qy, hqyQ, hqyy⟩ :=
    hQ.has_neighbor_at_each_vertex_of_three_separator
      hconn hScard (s := y) (by simp)
  constructor
  · obtain ⟨q, hqQ⟩ := hQ.nonempty
    have hqS : q ∉ ({x, y, z} : Finset V) :=
      hQ.not_mem_separator hqQ
    have hqx : q ≠ x := by
      intro h
      exact hqS (by simp [h])
    have hqy : q ≠ y := by
      intro h
      exact hqS (by simp [h])
    have hsmall : ({q, x, y} : Finset V).card = 3 := by
      simp [hqx, hqy, hxy]
    have hsub :
        ({q, x, y} : Finset V) ⊆ twoRootVertices Q x y := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;>
        simp [twoRootVertices, hqQ]
    have hcard :
        3 ≤ (twoRootVertices Q x y).card := by
      rw [← hsmall]
      exact Finset.card_le_card hsub
    simpa using hcard
  · intro T hT
    by_cases hxT : twoRootX Q x y ∈ T
    · exact connected_after_deleted_root G {x, y, z} Q hQ
        x y (by simp) (by simp) hxy qy hqyQ hqyy T hT hxT
    by_cases hyT : twoRootY Q x y ∈ T
    · exact connected_after_deleted_second_root G {x, y, z} Q hQ
        x y (by simp) (by simp) hxy qx hqxQ hqxx T hT hyT
    · exact connected_when_roots_survive G Q x y z
        hxy hxz hyz hQ hconn T hT hxT hyT

/-!
## Keeping the third separator vertex

Lemma 4.3 uses the graph on `Q ∪ {x,y,z}` with the possible edge `xy`
removed, treating `z` as the exceptional vertex.  It is represented as an
explicit root adjunction to the two-root component graph.  This makes the
two-connectivity and degree restoration arguments reusable and checkable.
-/

/-- Vertices on the two-root side adjacent to the retained third root. -/
noncomputable def thirdRootNeighbors
    [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y z : V) :
    Finset (↑(twoRootVertices Q x y) : Set V) := by
  classical
  exact Finset.univ.filter fun w => G.Adj z w.1

@[simp] theorem mem_thirdRootNeighbors
    [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y z : V)
    (w : (↑(twoRootVertices Q x y) : Set V)) :
    w ∈ thirdRootNeighbors G Q x y z ↔ G.Adj z w.1 := by
  classical
  simp [thirdRootNeighbors]

/--
The graph `G[Q ∪ {x,y,z}] - xy`, represented with `z` as the fresh root.
Only actual `z`-edges are adjoined.
-/
noncomputable def threeRootComponentBase
    [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y z : V) :
    SimpleGraph (Option (↑(twoRootVertices Q x y) : Set V)) :=
  adjoinRoot (twoRootComponentBase G Q x y)
    (thirdRootNeighbors G Q x y z)

/-- The lifted copy of `x` in the root-adjoined three-separator carrier. -/
def threeRootX
    [DecidableEq V]
    (Q : Finset V) (x y : V) :
    Option (↑(twoRootVertices Q x y) : Set V) :=
  some (twoRootX Q x y)

/-- The lifted copy of `y` in the root-adjoined three-separator carrier. -/
def threeRootY
    [DecidableEq V]
    (Q : Finset V) (x y : V) :
    Option (↑(twoRootVertices Q x y) : Set V) :=
  some (twoRootY Q x y)

@[simp] theorem threeRootComponentBase_sup_edge
    [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V) (x y z : V) :
    threeRootComponentBase G Q x y z ⊔
        edge (threeRootX Q x y) (threeRootY Q x y) =
      adjoinRoot (twoRootComponentGraph G Q x y)
        (thirdRootNeighbors G Q x y z) := by
  unfold threeRootComponentBase threeRootX threeRootY
  rw [← adjoinRoot_sup_edge, twoRootComponentBase_sup_edge]

/--
The retained-third-root graph is 2-connected as soon as `z` has two
neighbours on the component side.  This is the connectivity claim inside
Lemma 4.3.
-/
theorem one_component_three_separator_roots
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ : ComponentRegion G {x, y, z} Q)
    (hconn : IsKConnected G 3)
    (hzneighbors : 2 ≤ (thirdRootNeighbors G Q x y z).card) :
    IsTwoConnected
      (threeRootComponentBase G Q x y z ⊔
        edge (threeRootX Q x y) (threeRootY Q x y)) := by
  rw [threeRootComponentBase_sup_edge]
  exact isTwoConnected_adjoinRoot
    (twoRootComponentGraph G Q x y)
    (thirdRootNeighbors G Q x y z)
    (one_component_two_separator_roots
      G Q x y z hxy hxz hyz hQ hconn)
    hzneighbors

/--
An inner component vertex keeps its full ambient degree when the third
separator root is retained.
-/
theorem finiteDegree_le_threeRootComponentBase_inner
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset V)
    (x y z v : V)
    (hQ : ComponentRegion G {x, y, z} Q)
    (hvQ : v ∈ Q) :
    finiteDegree G v ≤
      finiteDegree (threeRootComponentBase G Q x y z)
        (some
          (⟨v, by simp [twoRootVertices, hvQ]⟩ :
            (↑(twoRootVertices Q x y) : Set V))) := by
  classical
  let vR : (↑(twoRootVertices Q x y) : Set V) :=
    ⟨v, by simp [twoRootVertices, hvQ]⟩
  have hvS : v ∉ ({x, y, z} : Finset V) :=
    hQ.not_mem_separator hvQ
  have hvx : v ≠ x := by
    intro h
    exact hvS (by simp [h])
  have hvy : v ≠ y := by
    intro h
    exact hvS (by simp [h])
  have houtside :
      ∀ w, G.Adj v w →
        w ∉ (↑(twoRootVertices Q x y) : Set V) → w = z := by
    intro w hvw hwRoots
    have hwS : w ∈ ({x, y, z} : Finset V) := by
      by_contra hwNotS
      have hwQ := hQ.closed hvQ hvw hwNotS
      exact hwRoots (by simp [twoRootVertices, hwQ])
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwS
    rcases hwS with hwx' | hwy' | hwz
    · exact False.elim (hwRoots (by simp [twoRootVertices, hwx']))
    · exact False.elim (hwRoots (by simp [twoRootVertices, hwy']))
    · exact hwz
  by_cases hvz : G.Adj z v
  · have hdegree :=
      finiteDegree_le_induce_add_one G
        (↑(twoRootVertices Q x y) : Set V) vR z houtside
    rw [← finiteDegree_twoRootComponentBase_inner
      G Q x y v hvQ hvx hvy] at hdegree
    change finiteDegree G v ≤
      finiteDegree
        (adjoinRoot (twoRootComponentBase G Q x y)
          (thirdRootNeighbors G Q x y z)) (some vR)
    rw [finiteDegree_adjoinRoot_some]
    have hvRmem :
        vR ∈ thirdRootNeighbors G Q x y z :=
      (mem_thirdRootNeighbors G Q x y z vR).2 (by
        simpa [vR] using hvz)
    rw [if_pos hvRmem]
    simpa [vR] using hdegree
  · have hinside :
        ∀ w, G.Adj v w →
          w ∈ (↑(twoRootVertices Q x y) : Set V) := by
      intro w hvw
      by_contra hwU
      have hwz := houtside w hvw hwU
      subst w
      exact hvz hvw.symm
    have hdegree := finiteDegree_le_induce G
      (↑(twoRootVertices Q x y) : Set V) vR hinside
    rw [← finiteDegree_twoRootComponentBase_inner
      G Q x y v hvQ hvx hvy] at hdegree
    change finiteDegree G v ≤
      finiteDegree
        (adjoinRoot (twoRootComponentBase G Q x y)
          (thirdRootNeighbors G Q x y z)) (some vR)
    rw [finiteDegree_adjoinRoot_some]
    have hvRnotmem :
        vR ∉ thirdRootNeighbors G Q x y z := by
      intro hvRmem
      exact hvz (by
        simpa [vR] using
          (mem_thirdRootNeighbors G Q x y z vR).1 hvRmem)
    rw [if_neg hvRnotmem, add_zero]
    simpa [vR] using hdegree

end DeanK5
