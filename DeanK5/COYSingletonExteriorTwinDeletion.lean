import DeanK5.Contraction
import DeanK5.Graph.Connectivity

/-!
# Deleting twin degree-two roots

This file isolates the connectivity argument needed in the type-3
singleton-exterior case of the COY induction.  Two nonadjacent vertices
`x` and `y` have the same two neighbors `a` and `b`.  After deleting
`x` and `y`, adjoining the edge `ab` preserves 2-connectivity, provided
the resulting carrier has the three vertices required by the project's
definition of 2-connectivity.

The order hypothesis is essential: a four-cycle with `x` and `y` opposite
has the stated twin-neighborhood property, but deleting them leaves only
the two vertices `a` and `b`.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

namespace SingletonTwinDeletion

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y a b : V}

/-- The ambient vertices that remain after deleting the two twins. -/
abbrev vertices (x y : V) : Set V :=
  {v | v ≠ x ∧ v ≠ y}

/-- The vertex type obtained by deleting the two twins. -/
abbrev Vertex (x y : V) :=
  vertices x y

/-- The graph induced after deleting the two twins. -/
def graph (G : SimpleGraph V) (x y : V) :
    SimpleGraph (Vertex x y) :=
  G.induce (vertices x y)

/-- A surviving ambient vertex regarded as a vertex of the deletion graph. -/
def vertex (x y v : V) (hvx : v ≠ x) (hvy : v ≠ y) :
    Vertex x y :=
  ⟨v, hvx, hvy⟩

/-- The deletion graph embeds in its ambient graph. -/
def embedding (G : SimpleGraph V) (x y : V) :
    graph G x y ↪g G :=
  Embedding.induce (vertices x y)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem vertex_val
    (x y v : V) (hvx : v ≠ x) (hvy : v ≠ y) :
    (vertex x y v hvx hvy : V) = v :=
  rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem embedding_apply
    (G : SimpleGraph V) (x y : V)
    (v : Vertex x y) :
    embedding G x y v = v.1 :=
  rfl

omit [DecidableEq V] in
/-- The twice-deleted graph has no more edges than the ambient graph. -/
theorem edgeSet_ncard_le
    (G : SimpleGraph V) (x y : V) :
    (graph G x y).edgeSet.ncard ≤ G.edgeSet.ncard := by
  let e := embedding G x y
  have hsubset :
      Sym2.map e '' (graph G x y).edgeSet ⊆ G.edgeSet :=
    e.toHom.image_edgeSet_subset
  calc
    (graph G x y).edgeSet.ncard =
        (Sym2.map e '' (graph G x y).edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective e.injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/-- Deleting two distinct vertices removes exactly two carrier elements. -/
theorem card_vertex
    (x y : V) (hxy : x ≠ y) :
    Fintype.card (Vertex x y) =
      Fintype.card V - 2 := by
  have hremoved :
      Fintype.card {v : V // v = x ∨ v = y} = 2 := by
    rw [Fintype.card_subtype]
    have hfilter :
        (Finset.univ.filter fun v : V => v = x ∨ v = y) =
          {x, y} := by
      ext v
      simp
    rw [hfilter]
    exact Finset.card_pair_eq_two_iff.mpr hxy
  have h :=
    Fintype.card_subtype_compl
      (fun v : V => v = x ∨ v = y)
  rw [hremoved] at h
  change
    Fintype.card {v : V // v ≠ x ∧ v ≠ y} =
      Fintype.card V - 2
  simpa only [not_or] using h

/--
A surviving vertex outside the two common neighbors loses no degree when
the twins are deleted.
-/
theorem finiteDegree_le_graph
    (v : Vertex x y)
    (hvAB : v.1 ∉ ({a, b} : Set V))
    (hNx : G.neighborSet x = ({a, b} : Set V))
    (hNy : G.neighborSet y = ({a, b} : Set V)) :
    finiteDegree G v.1 ≤ finiteDegree (graph G x y) v := by
  apply finiteDegree_le_induce G (vertices x y) v
  intro w hvw
  constructor
  · intro hwx
    subst w
    apply hvAB
    have hvN : v.1 ∈ G.neighborSet x := by
      simpa [SimpleGraph.mem_neighborSet] using hvw.symm
    rw [hNx] at hvN
    exact hvN
  · intro hwy
    subst w
    apply hvAB
    have hvN : v.1 ∈ G.neighborSet y := by
      simpa [SimpleGraph.mem_neighborSet] using hvw.symm
    rw [hNy] at hvN
    exact hvN

/--
A surjective vertex map that sends each edge either to an equality or to
an edge sends a connected graph to a connected graph.
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

omit [DecidableEq V] in
/-- A 2-connected graph is connected. -/
theorem connected_of_two_connected
    (hconn : IsTwoConnected G) :
    G.Connected := by
  have h :=
    hconn.2 (∅ : Finset V) (by simp)
  have hset :
      {v : V | v ∉ (∅ : Finset V)} =
        (Set.univ : Set V) := by
    ext v
    simp
  rw [hset] at h
  exact (G.induceUnivIso.connected_iff).1 h

omit [Fintype V] in
/--
The graph obtained after deleting the two twins and adding the edge between
their two common neighbors is connected.
-/
theorem augmented_connected
    (hconn : G.Connected)
    (hxy : x ≠ y)
    (hroots : ¬G.Adj x y)
    (hab : a ≠ b)
    (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hNx : G.neighborSet x = ({a, b} : Set V))
    (hNy : G.neighborSet y = ({a, b} : Set V)) :
    (graph G x y ⊔
      edge (vertex x y a hax hay) (vertex x y b hbx hby)).Connected := by
  classical
  let aA : Vertex x y := vertex x y a hax hay
  let bA : Vertex x y := vertex x y b hbx hby
  let H : SimpleGraph (Vertex x y) :=
    graph G x y ⊔ edge aA bA
  let rep : V → Vertex x y := fun v =>
    if hvx : v = x then aA
    else if hvy : v = y then aA
    else ⟨v, hvx, hvy⟩
  have hrepA : rep a = aA := by
    apply Subtype.ext
    simp [rep, hax, hay, aA]
  have hrepB : rep b = bA := by
    apply Subtype.ext
    simp [rep, hbx, hby, bA]
  have hrepX : rep x = aA := by
    simp [rep]
  have hrepY : rep y = aA := by
    simp [rep, hxy.symm]
  have hsurj : Function.Surjective rep := by
    intro v
    refine ⟨v.1, ?_⟩
    apply Subtype.ext
    simp [rep, v.2.1, v.2.2]
  have hedge :
      ∀ ⦃u v : V⦄, G.Adj u v →
        rep u = rep v ∨ H.Adj (rep u) (rep v) := by
    intro u v huv
    by_cases hux : u = x
    · have hvy : v ≠ y := by
        intro hvy
        exact hroots (by simpa [hux, hvy] using huv)
      have hvx : v ≠ x := by
        intro hvx
        subst u
        subst v
        exact G.loopless.irrefl x huv
      have hvAB : v = a ∨ v = b := by
        have hvN : v ∈ G.neighborSet x := by
          simpa [SimpleGraph.mem_neighborSet, hux] using huv
        rw [hNx] at hvN
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvN
      rcases hvAB with hva | hvb
      · subst u
        subst v
        left
        exact hrepX.trans hrepA.symm
      · subst u
        subst v
        right
        have habA : aA ≠ bA := by
          intro h
          exact hab (congrArg Subtype.val h)
        have hedgeAB : H.Adj aA bA := by
          simp [H, SimpleGraph.edge_adj, habA]
        simpa [hrepX, hrepB] using hedgeAB
    · by_cases huy : u = y
      · have hvy : v ≠ y := by
          intro hvy
          subst u
          subst v
          exact G.loopless.irrefl y huv
        have hvx : v ≠ x := by
          intro hvx
          exact hroots (by simpa [huy, hvx] using huv.symm)
        have hvAB : v = a ∨ v = b := by
          have hvN : v ∈ G.neighborSet y := by
            simpa [SimpleGraph.mem_neighborSet, huy] using huv
          rw [hNy] at hvN
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvN
        rcases hvAB with hva | hvb
        · subst u
          subst v
          left
          exact hrepY.trans hrepA.symm
        · subst u
          subst v
          right
          have habA : aA ≠ bA := by
            intro h
            exact hab (congrArg Subtype.val h)
          have hedgeAB : H.Adj aA bA := by
            simp [H, SimpleGraph.edge_adj, habA]
          simpa [hrepY, hrepB] using hedgeAB
      · by_cases hvx : v = x
        · have huAB : u = a ∨ u = b := by
            have huN : u ∈ G.neighborSet x := by
              simpa [SimpleGraph.mem_neighborSet, hvx] using huv.symm
            rw [hNx] at huN
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using huN
          rcases huAB with hua | hub
          · subst u
            subst v
            left
            exact hrepA.trans hrepX.symm
          · subst u
            subst v
            right
            have habA : aA ≠ bA := by
              intro h
              exact hab (congrArg Subtype.val h)
            have hedgeBA : H.Adj bA aA := by
              apply (le_sup_right : edge aA bA ≤ H)
              simpa [SimpleGraph.edge_adj] using habA.symm
            simpa [hrepB, hrepX] using hedgeBA
        · by_cases hvy : v = y
          · have huAB : u = a ∨ u = b := by
              have huN : u ∈ G.neighborSet y := by
                simpa [SimpleGraph.mem_neighborSet, hvy] using huv.symm
              rw [hNy] at huN
              simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using huN
            rcases huAB with hua | hub
            · subst u
              subst v
              left
              exact hrepA.trans hrepY.symm
            · subst u
              subst v
              right
              have habA : aA ≠ bA := by
                intro h
                exact hab (congrArg Subtype.val h)
              have hedgeBA : H.Adj bA aA := by
                apply (le_sup_right : edge aA bA ≤ H)
                simpa [SimpleGraph.edge_adj] using habA.symm
              simpa [hrepB, hrepY] using hedgeBA
          · right
            have hadj :
                (graph G x y).Adj
                  (⟨u, hux, huy⟩ : Vertex x y)
                  (⟨v, hvx, hvy⟩ : Vertex x y) :=
              huv
            exact (le_sup_left : graph G x y ≤ H) (by
              simpa [rep, hux, huy, hvx, hvy] using hadj)
  change H.Connected
  exact connected_of_surjective_mapOrContract
    hconn rep hsurj hedge

/--
After one surviving vertex is deleted as well, the graph obtained by
deleting the twins and adjoining their common-neighbor edge is connected.
-/
private theorem augmented_connected_delete_one
    (hconn : IsTwoConnected G)
    (hroots : ¬G.Adj x y)
    (hab : a ≠ b)
    (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hNx : G.neighborSet x = ({a, b} : Set V))
    (hNy : G.neighborSet y = ({a, b} : Set V))
    (r : Vertex x y) :
    ((graph G x y ⊔
      edge (vertex x y a hax hay) (vertex x y b hbx hby)).induce
        {v | v ≠ r}).Connected := by
  classical
  let aA : Vertex x y := vertex x y a hax hay
  let bA : Vertex x y := vertex x y b hbx hby
  let H : SimpleGraph (Vertex x y) :=
    graph G x y ⊔ edge aA bA
  let U : Set V := {v | v ≠ r.1}
  let A : SimpleGraph U := G.induce U
  let W : Set (Vertex x y) := {v | v ≠ r}
  let B : SimpleGraph W := H.induce W
  let s : Vertex x y := if aA = r then bA else aA
  have hsne : s ≠ r := by
    dsimp [s]
    split <;> rename_i ha
    · have habA : aA ≠ bA := by
        intro h
        exact hab (congrArg Subtype.val h)
      exact fun h => habA (ha.trans h.symm)
    · exact ha
  let sB : W := ⟨s, hsne⟩
  let rep : U → W := fun v =>
    if hvx : v.1 = x then sB
    else if hvy : v.1 = y then sB
    else
      ⟨⟨v.1, hvx, hvy⟩, by
        intro h
        exact v.2 (congrArg (fun w : Vertex x y => w.1) h)⟩
  have hsurj : Function.Surjective rep := by
    intro v
    let w : U := ⟨v.1.1, by
      intro h
      apply v.2
      apply Subtype.ext
      exact h⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp [rep, w, v.1.2.1, v.1.2.2]
  have hsClass : s = aA ∨ s = bA := by
    dsimp [s]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hedgeAdded :
      ∀ {c : Vertex x y}, c = aA ∨ c = bA →
        s = c ∨ H.Adj s c := by
    intro c hc
    rcases hsClass with hsa | hsb
    ·
      rcases hc with hca | hcb
      · exact Or.inl (hsa.trans hca.symm)
      · right
        rw [hsa, hcb]
        have habA : aA ≠ bA := by
          intro h
          exact hab (congrArg Subtype.val h)
        apply (le_sup_right : edge aA bA ≤ H)
        simpa [SimpleGraph.edge_adj] using habA
    ·
      rcases hc with hca | hcb
      · right
        rw [hsb, hca]
        have habA : aA ≠ bA := by
          intro h
          exact hab (congrArg Subtype.val h)
        apply (le_sup_right : edge aA bA ≤ H)
        simpa [SimpleGraph.edge_adj] using habA.symm
      · exact Or.inl (hsb.trans hcb.symm)
  have hstepRoot :
      ∀ {v : U}, v.1 = a ∨ v.1 = b →
        rep v = sB ∨ B.Adj sB (rep v) := by
    intro v hv
    have hvx : v.1 ≠ x := by
      rcases hv with hva | hvb
      · simpa [hva] using hax
      · simpa [hvb] using hbx
    have hvy : v.1 ≠ y := by
      rcases hv with hva | hvb
      · simpa [hva] using hay
      · simpa [hvb] using hby
    let vA : Vertex x y := ⟨v.1, hvx, hvy⟩
    have hvClass : vA = aA ∨ vA = bA := by
      rcases hv with hva | hvb
      · left
        apply Subtype.ext
        exact hva
      · right
        apply Subtype.ext
        exact hvb
    rcases hedgeAdded hvClass with heq | hadj
    · left
      apply Subtype.ext
      simpa [rep, hvx, hvy, vA] using heq.symm
    · right
      change H.Adj s (rep v).1
      simpa [rep, hvx, hvy, vA] using hadj
  have hedge :
      ∀ ⦃u v : U⦄, A.Adj u v →
        rep u = rep v ∨ B.Adj (rep u) (rep v) := by
    intro u v huv
    have huvG : G.Adj u.1 v.1 := huv
    by_cases hux : u.1 = x
    · have hvy : v.1 ≠ y := by
        intro hvy
        exact hroots (by simpa [hux, hvy] using huvG)
      have hvx : v.1 ≠ x := by
        intro hvx
        rw [hux, hvx] at huvG
        exact G.loopless.irrefl x huvG
      have hvAB : v.1 = a ∨ v.1 = b := by
        have hvN : v.1 ∈ G.neighborSet x := by
          simpa [SimpleGraph.mem_neighborSet, hux] using huvG
        rw [hNx] at hvN
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvN
      rcases hstepRoot hvAB with heq | hadj
      · left
        simpa [rep, hux, hvx, hvy] using heq.symm
      · right
        simpa [rep, hux] using hadj
    · by_cases huy : u.1 = y
      · have hvy : v.1 ≠ y := by
          intro hvy
          rw [huy, hvy] at huvG
          exact G.loopless.irrefl y huvG
        have hvx : v.1 ≠ x := by
          intro hvx
          exact hroots (by simpa [huy, hvx] using huvG.symm)
        have hvAB : v.1 = a ∨ v.1 = b := by
          have hvN : v.1 ∈ G.neighborSet y := by
            simpa [SimpleGraph.mem_neighborSet, huy] using huvG
          rw [hNy] at hvN
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvN
        rcases hstepRoot hvAB with heq | hadj
        · left
          simpa [rep, hux, huy, hvx, hvy] using heq.symm
        · right
          simpa [rep, hux, huy] using hadj
      · by_cases hvx : v.1 = x
        · have huAB : u.1 = a ∨ u.1 = b := by
            have huN : u.1 ∈ G.neighborSet x := by
              simpa [SimpleGraph.mem_neighborSet, hvx] using huvG.symm
            rw [hNx] at huN
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using huN
          rcases hstepRoot huAB with heq | hadj
          · left
            simpa [rep, hux, huy, hvx] using heq
          · right
            simpa [rep, hvx] using hadj.symm
        · by_cases hvy : v.1 = y
          · have huAB : u.1 = a ∨ u.1 = b := by
              have huN : u.1 ∈ G.neighborSet y := by
                simpa [SimpleGraph.mem_neighborSet, hvy] using huvG.symm
              rw [hNy] at huN
              simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using huN
            rcases hstepRoot huAB with heq | hadj
            · left
              simpa [rep, hux, huy, hvx, hvy] using heq
            · right
              simpa [rep, hux, huy, hvy] using hadj.symm
          · right
            have hadj :
                (graph G x y).Adj
                  (⟨u.1, hux, huy⟩ : Vertex x y)
                  (⟨v.1, hvx, hvy⟩ : Vertex x y) :=
              huvG
            change H.Adj (rep u).1 (rep v).1
            exact (le_sup_left : graph G x y ≤ H) (by
              simpa [rep, hux, huy, hvx, hvy] using hadj)
  have hsource : A.Connected := by
    have h :=
      hconn.2 ({r.1} : Finset V) (by simp)
    have hset :
        {v : V | v ∉ ({r.1} : Finset V)} =
          {v : V | v ≠ r.1} := by
      ext v
      simp
    rw [hset] at h
    simpa [A, U] using h
  change B.Connected
  exact connected_of_surjective_mapOrContract
    hsource rep hsurj hedge

/--
Deleting two nonadjacent vertices with the same two-element neighborhood
and then adjoining the edge between their common neighbors yields a
2-connected graph.

The explicit order hypothesis cannot be omitted: opposite vertices of a
four-cycle satisfy all structural hypotheses, while the deletion graph has
only two vertices.
-/
theorem sup_edge_two_connected
    (hconn : IsTwoConnected G)
    (horder : 3 ≤ Fintype.card (Vertex x y))
    (hxy : x ≠ y)
    (hroots : ¬G.Adj x y)
    (hab : a ≠ b)
    (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hNx : G.neighborSet x = ({a, b} : Set V))
    (hNy : G.neighborSet y = ({a, b} : Set V)) :
    IsTwoConnected
      (graph G x y ⊔
        edge (vertex x y a hax hay) (vertex x y b hbx hby)) := by
  classical
  apply isTwoConnected_of_connected_delete_one
  · exact horder
  · exact augmented_connected
      (connected_of_two_connected hconn)
      hxy hroots hab hax hay hbx hby hNx hNy
  · intro r
    exact augmented_connected_delete_one
      hconn hroots hab hax hay hbx hby hNx hNy r

/--
Ambient order at least five supplies the order hypothesis in
`sup_edge_two_connected`.
-/
theorem sup_edge_two_connected_of_five_le_card
    (hconn : IsTwoConnected G)
    (hfive : 5 ≤ Fintype.card V)
    (hxy : x ≠ y)
    (hroots : ¬G.Adj x y)
    (hab : a ≠ b)
    (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hNx : G.neighborSet x = ({a, b} : Set V))
    (hNy : G.neighborSet y = ({a, b} : Set V)) :
    IsTwoConnected
      (graph G x y ⊔
        edge (vertex x y a hax hay) (vertex x y b hbx hby)) := by
  exact sup_edge_two_connected
    (G := G) (x := x) (y := y) (a := a) (b := b)
    hconn
    (by
      rw [card_vertex x y hxy]
      omega)
    hxy hroots hab hax hay hbx hby hNx hNy

end SingletonTwinDeletion

end COY

end DeanK5
