import DeanK5.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Vertex deletions and component regions

The paper repeatedly chooses a connected component after deleting a
small separator.  `ComponentRegion G S Q` packages the exact properties of
such a component while keeping its vertices in the original carrier.  This
avoids silently moving between a graph, an induced subtype, and the ambient
graph.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/-- The graph obtained by deleting a finite set of vertices. -/
abbrev deleteVertices (G : SimpleGraph V) (S : Finset V) :=
  G.induce {v | v ∉ S}

/--
Inducing away all but possibly one neighbour loses at most one unit of
degree.  This is the degree-bookkeeping lemma used in the separator
arguments.
-/
theorem finiteDegree_le_induce_add_one
    [Fintype V]
    (G : SimpleGraph V) (U : Set V) (v : U) (z : V)
    [Fintype U]
    (houtside : ∀ w, G.Adj v.1 w → w ∉ U → w = z) :
    finiteDegree G v.1 ≤ finiteDegree (G.induce U) v + 1 := by
  let N : Set V := G.neighborSet v.1
  let NI : Set U := (G.induce U).neighborSet v
  have himage : Subtype.val '' NI = N ∩ U := by
    ext w
    simp [N, NI]
  have hsub : N ⊆ insert z (N ∩ U) := by
    intro w hw
    by_cases hwU : w ∈ U
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨hw, hwU⟩)
    · exact Set.mem_insert_iff.mpr
        (Or.inl (houtside w hw hwU))
  unfold finiteDegree
  change N.ncard ≤ NI.ncard + 1
  calc
    N.ncard ≤ (insert z (N ∩ U)).ncard :=
      Set.ncard_le_ncard hsub
    _ ≤ (N ∩ U).ncard + 1 := Set.ncard_insert_le _ _
    _ = NI.ncard + 1 := by
      rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- Inducing loses no degree when every neighbour of the vertex survives. -/
theorem finiteDegree_le_induce
    [Fintype V]
    (G : SimpleGraph V) (U : Set V) (v : U)
    [Fintype U]
    (hinside : ∀ w, G.Adj v.1 w → w ∈ U) :
    finiteDegree G v.1 ≤ finiteDegree (G.induce U) v := by
  let N : Set V := G.neighborSet v.1
  let NI : Set U := (G.induce U).neighborSet v
  have himage : Subtype.val '' NI = N := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hw
      exact ⟨⟨w, hinside w hw⟩, hw, rfl⟩
  unfold finiteDegree
  change N.ncard ≤ NI.ncard
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- Removing one edge does not change the degree of any other vertex. -/
theorem finiteDegree_sdiff_edge_of_ne
    [Fintype V]
    (G : SimpleGraph V) (x y v : V)
    (hvx : v ≠ x) (hvy : v ≠ y) :
    finiteDegree (G \ edge x y) v = finiteDegree G v := by
  unfold finiteDegree
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sdiff_adj,
    SimpleGraph.edge_adj]
  constructor
  · exact fun h => h.1
  · intro hvw
    refine ⟨hvw, ?_⟩
    rintro (⟨h₁, -⟩ | ⟨h₁, -⟩)
    · exact hvx h₁
    · exact hvy h₁

/--
`Q` is a connected component region of `G - S`.

The `closed` field says that an edge leaving `Q` must enter the deleted
separator.  Together with connectedness and nonemptiness this is exactly the
local component information used by the paper.
-/
structure ComponentRegion
    [DecidableEq V] (G : SimpleGraph V) (S Q : Finset V) : Prop where
  nonempty : Q.Nonempty
  disjoint : Disjoint Q S
  connected : (G.induce (↑Q : Set V)).Connected
  closed : ∀ ⦃u v : V⦄, u ∈ Q → G.Adj u v → v ∉ S → v ∈ Q

/-- The original-carrier vertices belonging to a component of `G - S`. -/
noncomputable def componentVertices
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    (C : (deleteVertices G S).ConnectedComponent) : Finset V := by
  classical
  exact C.supp.toFinset.image Subtype.val

/-- Deleting `S` leaves at least two connected components. -/
def IsVertexCut
    (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ C₀ C₁ : (deleteVertices G S).ConnectedComponent, C₀ ≠ C₁

/--
Deleting at most `r` vertices from a `(k+r)`-connected graph leaves a
`k`-connected graph.
-/
theorem isKConnected_deleteVertices
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k r : ℕ)
    (hconn : IsKConnected G (k + r))
    (S : Finset V) (hS : S.card ≤ r) :
    IsKConnected (deleteVertices G S) k := by
  classical
  have hmemberCard :
      Fintype.card {v : V // v ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hdeletedCard :
      Fintype.card {v : V // v ∉ S} =
        Fintype.card V - S.card := by
    rw [Fintype.card_subtype_compl]
    exact congrArg (Fintype.card V - ·) hmemberCard
  constructor
  · change k + 1 ≤ Fintype.card {v : V // v ∉ S}
    rw [hdeletedCard]
    have horder := hconn.1
    omega
  · intro T hT
    let R := S ∪ T.image Subtype.val
    have hRcard : R.card < k + r := by
      calc
        R.card ≤ S.card + (T.image Subtype.val).card :=
          by
            dsimp [R]
            exact Finset.card_union_le S (T.image Subtype.val)
        _ ≤ S.card + T.card :=
          Nat.add_le_add_left Finset.card_image_le S.card
        _ < k + r := by omega
    have hbase := hconn.2 R hRcard
    let f :
        G.induce {v | v ∉ R} →g
          (deleteVertices G S).induce {v | v ∉ T} := {
      toFun a := by
        have haS : a.1 ∉ S := by
          intro haS
          exact a.2 (Finset.mem_union_left _ haS)
        let aS : {v : V // v ∉ S} := ⟨a.1, haS⟩
        have haT : aS ∉ T := by
          intro haT
          have haImage : a.1 ∈ T.image Subtype.val :=
            Finset.mem_image.mpr ⟨aS, haT, rfl⟩
          exact a.2 (Finset.mem_union_right _ haImage)
        exact ⟨aS, haT⟩
      map_rel' := by
        intro a b hab
        exact hab
    }
    rw [connected_iff_exists_forall_reachable] at hbase ⊢
    obtain ⟨root, hroot⟩ := hbase
    refine ⟨f root, ?_⟩
    rintro ⟨⟨v, hvS⟩, hvT⟩
    have hvR : v ∉ R := by
      intro hv
      rcases Finset.mem_union.mp hv with hvS' | hvImage
      · exact hvS hvS'
      · obtain ⟨w, hwT, hwv⟩ := Finset.mem_image.mp hvImage
        have hwEq : w = ⟨v, hvS⟩ := by
          apply Subtype.ext
          exact hwv
        exact hvT (hwEq ▸ hwT)
    let vR : {w : V // w ∉ R} := ⟨v, hvR⟩
    have hreach := (hroot vR).map f
    have hfeq : f vR = ⟨⟨v, hvS⟩, hvT⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    rw [hfeq] at hreach
    exact hreach

@[simp] theorem mem_componentVertices_iff
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    (C : (deleteVertices G S).ConnectedComponent) (v : V) :
    v ∈ componentVertices G S C ↔
      ∃ hv : v ∉ S,
        (⟨v, hv⟩ : {w : V // w ∉ S}) ∈ C.supp := by
  classical
  simp only [componentVertices, Finset.mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨w, hwC, hwv⟩
    subst v
    exact ⟨w.2, hwC⟩
  · rintro ⟨hvS, hvC⟩
    exact ⟨⟨v, hvS⟩, hvC, rfl⟩

/-- Every actual connected component after deletion yields a component region. -/
theorem componentRegion_componentVertices
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    (C : (deleteVertices G S).ConnectedComponent) :
    ComponentRegion G S (componentVertices G S C) := by
  let Q := componentVertices G S C
  have hmem (v : V) :
      v ∈ Q ↔
        ∃ hv : v ∉ S,
          (⟨v, hv⟩ : {w : V // w ∉ S}) ∈ C.supp :=
    mem_componentVertices_iff G S C v
  refine {
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    closed := ?_
  }
  · obtain ⟨w, hwC⟩ := C.nonempty_supp
    exact ⟨w.1, hmem w.1 |>.2 ⟨w.2, hwC⟩⟩
  · apply Finset.disjoint_left.mpr
    intro v hvQ hvS
    obtain ⟨hvnotS, -⟩ := (hmem v).1 hvQ
    exact hvnotS hvS
  · let e : (↑Q : Set V) ≃ C := {
      toFun v := by
        let hex := (hmem v.1).1 v.2
        let hvS := Classical.choose hex
        let hvC := Classical.choose_spec hex
        exact ⟨⟨v.1, hvS⟩, hvC⟩
      invFun v := ⟨v.1.1, (hmem v.1.1).2 ⟨v.1.2, v.2⟩⟩
      left_inv v := by
        apply Subtype.ext
        rfl
      right_inv v := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
    }
    let iso : G.induce (↑Q : Set V) ≃g C.toSimpleGraph := {
      __ := e
      map_rel_iff' := by
        intro a b
        change G.Adj a.1 b.1 ↔ G.Adj a.1 b.1
        rfl
    }
    exact (SimpleGraph.Iso.connected_iff iso).mpr C.connected_toSimpleGraph
  · intro u v huQ huv hvS
    obtain ⟨huS, huC⟩ := (hmem u).1 huQ
    have hadj :
        (deleteVertices G S).Adj
          ⟨u, huS⟩ ⟨v, hvS⟩ :=
      huv
    have hvC : (⟨v, hvS⟩ : {w : V // w ∉ S}) ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp huC hadj
    exact (hmem v).2 ⟨hvS, hvC⟩

theorem disjoint_componentVertices
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    {C₀ C₁ : (deleteVertices G S).ConnectedComponent}
    (hne : C₀ ≠ C₁) :
    Disjoint (componentVertices G S C₀)
      (componentVertices G S C₁) := by
  apply Finset.disjoint_left.mpr
  intro v hv₀ hv₁
  obtain ⟨hvS₀, hvC₀⟩ :=
    (mem_componentVertices_iff G S C₀ v).1 hv₀
  obtain ⟨hvS₁, hvC₁⟩ :=
    (mem_componentVertices_iff G S C₁ v).1 hv₁
  have hvC₁' :
      (⟨v, hvS₀⟩ : {w : V // w ∉ S}) ∈ C₁.supp := by
    simpa using hvC₁
  exact hne
    (SimpleGraph.ConnectedComponent.eq_of_common_vertex hvC₀ hvC₁')

theorem IsVertexCut.exists_other_component
    {G : SimpleGraph V} {S : Finset V}
    (hcut : IsVertexCut G S)
    (C : (deleteVertices G S).ConnectedComponent) :
    ∃ C' : (deleteVertices G S).ConnectedComponent, C' ≠ C := by
  obtain ⟨C₀, C₁, hne⟩ := hcut
  by_cases h : C₀ = C
  · exact ⟨C₁, by
      intro h'
      exact hne (h.trans h'.symm)⟩
  · exact ⟨C₀, h⟩

namespace ComponentRegion

variable [DecidableEq V] {G : SimpleGraph V} {S Q : Finset V}

lemma not_mem_separator (hQ : ComponentRegion G S Q)
    {v : V} (hv : v ∈ Q) : v ∉ S :=
  Finset.disjoint_left.mp hQ.disjoint hv

lemma mem_of_adj_of_not_mem_separator
    (hQ : ComponentRegion G S Q)
    {u v : V} (hu : u ∈ Q) (huv : G.Adj u v) (hvS : v ∉ S) :
    v ∈ Q :=
  hQ.closed hu huv hvS

private theorem exists_adj_to_separator_of_walk
    (hQ : ComponentRegion G S Q)
    {s q : V} (hs : s ∈ S) (hq : q ∈ Q)
    (p : G.Walk q s)
    (havoid : ∀ v ∈ p.support, v ∉ S.erase s) :
    ∃ u ∈ Q, G.Adj u s := by
  let rec go {a : V} (ha : a ∈ Q) (p : G.Walk a s)
      (havoid : ∀ v ∈ p.support, v ∉ S.erase s) :
      ∃ u ∈ Q, G.Adj u s := by
    cases p with
    | nil =>
        exact False.elim
          (Finset.disjoint_left.mp hQ.disjoint ha hs)
    | cons hab p =>
        rename_i b
        by_cases hbQ : b ∈ Q
        · apply go hbQ p
          intro v hv
          exact havoid v (by simp [hv])
        · have hbS : b ∈ S := by
            by_contra hbnotS
            exact hbQ (hQ.closed ha hab hbnotS)
          have hbnotErase : b ∉ S.erase s :=
            havoid b (by simp)
          have hbs : b = s := by
            by_contra hne
            exact hbnotErase (Finset.mem_erase.mpr ⟨hne, hbS⟩)
          subst b
          exact ⟨a, ha, hab⟩
  exact go hq p havoid

/--
Follow an arbitrary walk from a component region to the deleted separator
and expose its first boundary edge.  The boundary endpoint is retained in
the walk support so later deletion arguments can prove that it avoids a
specified vertex.
-/
theorem exists_boundary_edge_of_walk
    (hQ : ComponentRegion G S Q)
    {q t : V} (hq : q ∈ Q) (ht : t ∈ S)
    (p : G.Walk q t) :
    ∃ u ∈ Q, u ∈ p.support ∧ ∃ s ∈ S,
      s ∈ p.support ∧ G.Adj u s := by
  let rec go {a : V} (ha : a ∈ Q)
      (p : G.Walk a t) :
      ∃ u ∈ Q, u ∈ p.support ∧ ∃ s ∈ S,
        s ∈ p.support ∧ G.Adj u s := by
    cases p with
    | nil =>
        exact False.elim
          (Finset.disjoint_left.mp hQ.disjoint ha ht)
    | cons hab p =>
        rename_i b
        by_cases hbQ : b ∈ Q
        · obtain ⟨u, huQ, huSupport, s, hsS, hsSupport, hus⟩ :=
            go hbQ p
          exact ⟨u, huQ, by simp [huSupport], s, hsS, by
            simp [hsSupport], hus⟩
        · have hbS : b ∈ S := by
            by_contra hbnotS
            exact hbQ (hQ.closed ha hab hbnotS)
          exact ⟨a, ha, by simp, b, hbS, by simp, hab⟩
  exact go hq p

/--
In a 2-connected graph, a component outside `S` has an attachment avoiding
any prescribed boundary vertex, provided another boundary target exists.
-/
theorem exists_attachment_avoiding_boundary_vertex
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hconn : IsKConnected G 2)
    {z t : V} (hzS : z ∈ S) (htS : t ∈ S)
    (hzt : z ≠ t) :
    ∃ q ∈ Q, ∃ s ∈ S, s ≠ z ∧ G.Adj q s := by
  obtain ⟨q, hqQ⟩ := hQ.nonempty
  have hqz : q ≠ z := by
    intro h
    exact hQ.not_mem_separator hqQ (h ▸ hzS)
  have hconnected :=
    hconn.2 ({z} : Finset V) (by simp)
  have hqDeleted : q ∉ ({z} : Finset V) := by
    simpa using hqz
  have htDeleted : t ∉ ({z} : Finset V) := by
    simpa using hzt.symm
  obtain ⟨p⟩ :=
    hconnected.preconnected
      ⟨q, hqDeleted⟩ ⟨t, htDeleted⟩
  let pG : G.Walk q t :=
    p.map (Embedding.induce {v | v ∉ ({z} : Finset V)}).toHom
  obtain ⟨u, huQ, -, s, hsS, hsSupport, hus⟩ :=
    hQ.exists_boundary_edge_of_walk hqQ htS pG
  have hsz : s ≠ z := by
    intro hsz
    subst s
    change z ∈
      (p.map (Embedding.induce
        {v | v ∉ ({z} : Finset V)}).toHom).support at hsSupport
    rw [SimpleGraph.Walk.support_map] at hsSupport
    obtain ⟨a, ha, haz⟩ := List.mem_map.mp hsSupport
    apply a.2
    change a.1 = z at haz
    simpa using haz
  exact ⟨u, huQ, s, hsS, hsz, hus⟩

/--
In a 2-connected graph, deleting one old component vertex still leaves an
attachment from the remainder of the component to the boundary.
-/
theorem exists_attachment_avoiding_old_vertex
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hconn : IsKConnected G 2)
    (w z : (↑Q : Set V)) (hzw : z ≠ w)
    {t : V} (htS : t ∈ S) :
    ∃ a : (↑Q : Set V), a ≠ w ∧
      ∃ s ∈ S, G.Adj a.1 s := by
  have htQ : t ∉ Q := by
    intro ht
    exact hQ.not_mem_separator ht htS
  have hconnected :=
    hconn.2 ({w.1} : Finset V) (by simp)
  have hzDeleted : z.1 ∉ ({w.1} : Finset V) := by
    intro hz
    simp only [Finset.mem_singleton] at hz
    exact hzw (Subtype.ext hz)
  have htDeleted : t ∉ ({w.1} : Finset V) := by
    intro ht
    simp only [Finset.mem_singleton] at ht
    exact hQ.not_mem_separator w.2 (ht ▸ htS)
  obtain ⟨p⟩ :=
    hconnected.preconnected
      ⟨z.1, hzDeleted⟩ ⟨t, htDeleted⟩
  let pG : G.Walk z.1 t :=
    p.map (Embedding.induce
      {v | v ∉ ({w.1} : Finset V)}).toHom
  have hwavoid : w.1 ∉ pG.support := by
    intro hw
    change w.1 ∈
      (p.map (Embedding.induce
        {v | v ∉ ({w.1} : Finset V)}).toHom).support at hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨b, hb, hbw⟩ := List.mem_map.mp hw
    apply b.2
    change b.1 = w.1 at hbw
    simpa using hbw
  obtain ⟨a, haQ, haSupport, s, hsS, -, has⟩ :=
    hQ.exists_boundary_edge_of_walk z.2 htS pG
  let aQ : (↑Q : Set V) := ⟨a, haQ⟩
  have haw : aQ ≠ w := by
    intro h
    apply hwavoid
    have haval : a = w.1 :=
      congrArg Subtype.val h
    simpa [pG, haval] using haSupport
  exact ⟨aQ, haw, s, hsS, has⟩

/--
The matching-of-size-two assertion used in the rank-two and one-part branches
of Lemma 6.3.  It is derived from 2-connectivity, rather than assumed as an
attachment axiom.
-/
theorem exists_independent_boundary_edges
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hconn : IsKConnected G 2)
    (hQcard : 2 ≤ Q.card)
    (hScard : 2 ≤ S.card) :
    ∃ q₁ q₂ : (↑Q : Set V), ∃ s₁ s₂ : V,
      s₁ ∈ S ∧ s₂ ∈ S ∧
      q₁ ≠ q₂ ∧ s₁ ≠ s₂ ∧
      G.Adj q₁.1 s₁ ∧ G.Adj q₂.1 s₂ := by
  obtain ⟨z, hzS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hErasePos : 0 < (S.erase z).card := by
    rw [Finset.card_erase_of_mem hzS]
    omega
  obtain ⟨t, htErase⟩ := Finset.card_pos.mp hErasePos
  have htS : t ∈ S := Finset.mem_of_mem_erase htErase
  have hzt : z ≠ t := by
    exact fun h => (Finset.mem_erase.mp htErase).1 h.symm
  obtain ⟨q₁val, hq₁Q, s₁, hs₁S, -, hq₁s₁⟩ :=
    hQ.exists_attachment_avoiding_boundary_vertex
      hconn hzS htS hzt
  let q₁ : (↑Q : Set V) := ⟨q₁val, hq₁Q⟩
  have hEraseS₁Pos : 0 < (S.erase s₁).card := by
    rw [Finset.card_erase_of_mem hs₁S]
    omega
  obtain ⟨t₁, ht₁Erase⟩ :=
    Finset.card_pos.mp hEraseS₁Pos
  have ht₁S : t₁ ∈ S :=
    Finset.mem_of_mem_erase ht₁Erase
  have hs₁t₁ : s₁ ≠ t₁ := by
    exact fun h => (Finset.mem_erase.mp ht₁Erase).1 h.symm
  obtain ⟨qAVal, hqAQ, sA, hsAS, hsAne, hqAsA⟩ :=
    hQ.exists_attachment_avoiding_boundary_vertex
      hconn hs₁S ht₁S hs₁t₁
  let qA : (↑Q : Set V) := ⟨qAVal, hqAQ⟩
  by_cases hqAq₁ : qA ≠ q₁
  · exact ⟨q₁, qA, s₁, sA,
      hs₁S, hsAS, hqAq₁.symm, hsAne.symm,
      hq₁s₁, hqAsA⟩
  · have hQErasePos : 0 < (Q.erase q₁.1).card := by
      rw [Finset.card_erase_of_mem q₁.2]
      omega
    obtain ⟨q₂val, hq₂Erase⟩ :=
      Finset.card_pos.mp hQErasePos
    let q₂start : (↑Q : Set V) :=
      ⟨q₂val, Finset.mem_of_mem_erase hq₂Erase⟩
    have hq₂start_ne : q₂start ≠ q₁ := by
      intro h
      exact (Finset.mem_erase.mp hq₂Erase).1
        (congrArg Subtype.val h)
    obtain ⟨q₂, hq₂ne, s₂, hs₂S, hq₂s₂⟩ :=
      hQ.exists_attachment_avoiding_old_vertex
        hconn q₁ q₂start hq₂start_ne hs₁S
    by_cases hs₂s₁ : s₂ ≠ s₁
    · exact ⟨q₁, q₂, s₁, s₂,
        hs₁S, hs₂S, hq₂ne.symm, hs₂s₁.symm,
        hq₁s₁, hq₂s₂⟩
    · have hqAValEq : qAVal = q₁.1 := by
        simpa [qA] using
          congrArg Subtype.val (not_ne_iff.mp hqAq₁)
      have hq₁sA : G.Adj q₁.1 sA := by
        rw [hqAValEq] at hqAsA
        exact hqAsA
      have hq₂s₁ : G.Adj q₂.1 s₁ := by
        simpa [not_ne_iff.mp hs₂s₁] using hq₂s₂
      exact ⟨q₁, q₂, sA, s₁,
        hsAS, hs₁S, hq₂ne.symm, hsAne,
        hq₁sA, hq₂s₁⟩

/--
A walk that starts in a component region and avoids its separator cannot
leave the region.
-/
theorem endpoint_mem_of_walk_avoiding_separator
    (hQ : ComponentRegion G S Q)
    {q x : V} (hqQ : q ∈ Q)
    (p : G.Walk q x)
    (havoid : ∀ v ∈ p.support, v ∉ S) :
    x ∈ Q := by
  induction p with
  | nil =>
      exact hqQ
  | @cons a b c hab p ih =>
      have hbS : b ∉ S := by
        apply havoid b
        simp
      have hbQ := hQ.closed hqQ hab hbS
      apply ih hbQ
      intro v hv
      exact havoid v (by simp [hv])

/--
If a component region has a surviving vertex on the far side of its
separator, `k`-connectivity forces the separator to have at least `k`
vertices.
-/
theorem connectivity_le_separator_card
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hconn : IsKConnected G k)
    {x : V} (hxQ : x ∉ Q) (hxS : x ∉ S) :
    k ≤ S.card := by
  by_contra hsmall
  have hScard : S.card < k := by omega
  have hdeleted := hconn.2 S hScard
  obtain ⟨q, hqQ⟩ := hQ.nonempty
  have hqS : q ∉ S :=
    hQ.not_mem_separator hqQ
  obtain ⟨p⟩ :=
    hdeleted.preconnected
      ⟨q, hqS⟩ ⟨x, hxS⟩
  let pG : G.Walk q x :=
    p.map (Embedding.induce {v | v ∉ S}).toHom
  have havoid :
      ∀ v ∈ pG.support, v ∉ S := by
    intro v hv
    change v ∈
      (p.map (Embedding.induce {v | v ∉ S}).toHom).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨a, ha, hav⟩ := List.mem_map.mp hv
    change a.1 = v at hav
    exact hav ▸ a.2
  exact hxQ
    (hQ.endpoint_mem_of_walk_avoiding_separator
      hqQ pG havoid)

/--
Follow a walk from a component region until it first enters the deleted
boundary.  If the walk avoids one old vertex `w`, its initial segment gives
an explicit reachability certificate in `Q - w`.  This is the cut-component
fact used to justify the auxiliary connectivity in Lemma 6.1.
-/
theorem reaches_boundary_of_walk_avoiding_vertex
    (hQ : ComponentRegion G S Q)
    (w z : (↑Q : Set V)) (hzw : z ≠ w)
    {t : V} (htQ : t ∉ Q)
    (p : G.Walk z.1 t)
    (hwavoid : w.1 ∉ p.support) :
    ∃ (a : (↑Q : Set V)) (haw : a ≠ w),
      ∃ s ∈ S, s ∈ p.support ∧ G.Adj a.1 s ∧
        ((G.induce (↑Q : Set V)).induce
          {u | u.1 ≠ w.1}).Reachable
          ⟨z, fun h => hzw (Subtype.ext h)⟩
          ⟨a, fun h => haw (Subtype.ext h)⟩ := by
  let rec go {a : V}
      (haQ : a ∈ Q) (haw : a ≠ w.1)
      (p : G.Walk a t)
      (hwavoid : w.1 ∉ p.support) :
      ∃ (b : (↑Q : Set V)) (hbw : b ≠ w),
        ∃ s ∈ S, s ∈ p.support ∧ G.Adj b.1 s ∧
          ((G.induce (↑Q : Set V)).induce
            {u | u.1 ≠ w.1}).Reachable
            ⟨⟨a, haQ⟩, by exact haw⟩
            ⟨b, fun h => hbw (Subtype.ext h)⟩ := by
    cases p with
    | nil =>
        exact False.elim (htQ haQ)
    | cons hab p =>
        rename_i b
        by_cases hbQ : b ∈ Q
        · have hbw : b ≠ w.1 := by
            intro hbw
            apply hwavoid
            simp only [SimpleGraph.Walk.support_cons,
              List.mem_cons]
            exact Or.inr (by
              simpa [hbw] using p.start_mem_support)
          obtain ⟨d, hdw, s, hsS, hsSupport, hds, hreach⟩ :=
            go hbQ hbw p (by
              intro hw
              exact hwavoid (by simp [hw]))
          have habDel :
              ((G.induce (↑Q : Set V)).induce
                {u | u.1 ≠ w.1}).Adj
                ⟨⟨a, haQ⟩, by exact haw⟩
                ⟨⟨b, hbQ⟩, by exact hbw⟩ :=
            hab
          exact ⟨d, hdw, s, hsS, by
              simp [hsSupport],
            hds,
            habDel.reachable.trans hreach⟩
        · have hbS : b ∈ S := by
            by_contra hbnotS
            exact hbQ (hQ.closed haQ hab hbnotS)
          let aQ : (↑Q : Set V) := ⟨a, haQ⟩
          have haQw : aQ ≠ w := by
            intro h
            exact haw (congrArg Subtype.val h)
          exact ⟨aQ, haQw, b, hbS, by
              simp,
            hab, .rfl⟩
  have hzwVal : z.1 ≠ w.1 := by
    intro h
    exact hzw (Subtype.ext h)
  exact go z.2 hzwVal p hwavoid

/--
In a 3-connected graph, every component of the deletion of a 3-set has a
neighbour at each separator vertex.
-/
theorem has_neighbor_at_each_vertex_of_three_separator
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hconn : IsKConnected G 3)
    (hScard : S.card = 3)
    {s : V} (hs : s ∈ S) :
    ∃ q ∈ Q, G.Adj q s := by
  obtain ⟨q, hqQ⟩ := hQ.nonempty
  have hqS : q ∉ S := hQ.not_mem_separator hqQ
  have hcard : (S.erase s).card < 3 := by
    rw [Finset.card_erase_of_mem hs, hScard]
    omega
  have hdeleted := hconn.2 (S.erase s) hcard
  have hqdel : q ∉ S.erase s := by
    exact fun h => hqS (Finset.mem_of_mem_erase h)
  have hsdel : s ∉ S.erase s := Finset.notMem_erase _ _
  obtain ⟨p⟩ :=
    hdeleted.preconnected ⟨q, hqdel⟩ ⟨s, hsdel⟩
  let pG : G.Walk q s := p.map (Embedding.induce _).toHom
  apply hQ.exists_adj_to_separator_of_walk hs hqQ pG
  intro v hv
  change v ∈ (p.map (Embedding.induce _).toHom).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact w.property

/-- A component behind a 3-set has at least two vertices at minimum degree four. -/
theorem two_le_card_of_three_separator
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    (hScard : S.card = 3)
    (hdeg : ∀ q ∈ Q, 4 ≤ finiteDegree G q) :
    2 ≤ Q.card := by
  by_contra hsmall
  have hcardle : Q.card ≤ 1 := by omega
  obtain ⟨q, hqQ⟩ := hQ.nonempty
  have hQeq : Q = {q} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hqQ, ?_⟩
    intro v hvQ
    exact Finset.card_le_one.mp hcardle v hvQ q hqQ
  have hneighbor : G.neighborSet q ⊆ (↑S : Set V) := by
    intro v hqv
    by_contra hvS
    have hvQ := hQ.closed hqQ hqv hvS
    have hvq : v = q := by simpa [hQeq] using hvQ
    exact G.irrefl (hvq ▸ hqv)
  have hncard :
      (G.neighborSet q).ncard ≤ (↑S : Set V).ncard :=
    Set.ncard_le_ncard hneighbor
  have hqdeg := hdeg q hqQ
  unfold finiteDegree at hqdeg
  simpa [hScard] using (Nat.le_trans hqdeg hncard)

end ComponentRegion

end DeanK5
