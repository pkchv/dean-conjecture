import DeanK5.COYSingletonExterior
import DeanK5.COYPathOperations

/-!
# The singleton exterior with a type-2 COY core

This file formalizes COY Case 1.2.  In the singleton-exterior case, a
natural type-2 core has the two roots joined to the same two-element set
`S`.  Deleting the roots leaves a smaller rooted instance on the two
vertices of `S`; minimality solves that instance, and the two deleted root
edges lift its paths back to the alleged counterexample.

The connectivity assertion used by the source is proved explicitly.  After
one further vertex is deleted, each deleted root is retracted to a surviving
vertex of `S`.  Edges incident with a deleted root are replaced by two-edge
routes through a surviving vertex of the type-2 clique `T`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace SingletonTypeTwoDeletion

variable [Fintype V] [DecidableEq V]
  {q ℓ : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The carrier obtained by deleting the two original roots. -/
abbrev vertices (x y : V) : Set V :=
  {v | v ≠ x ∧ v ≠ y}

/-- The vertex type obtained by deleting the two original roots. -/
abbrev Vertex (x y : V) :=
  vertices x y

/-- The graph induced after deleting the two original roots. -/
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

/-- Identify the deletion graph with the redundant triple deletion at `x`. -/
private def graphIsoTripleAtLeft
    (G : SimpleGraph V) (x y : V) :
    graph G x y ≃g
      G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ x} where
  toFun v := ⟨v.1, v.2.1, v.2.2, v.2.1⟩
  invFun v := ⟨v.1, v.2.1, v.2.2.1⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl
  map_rel_iff' := Iff.rfl

/--
Deleting one vertex from the twice-deleted graph is the same as deleting
the corresponding three ambient vertices at once.
-/
private def deleteOneIso
    (G : SimpleGraph V) (x y : V)
    (r : Vertex x y) :
    (graph G x y).induce {v | v ≠ r} ≃g
      G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ r.1} where
  toFun v := ⟨v.1.1, v.1.2.1, v.1.2.2, by
    intro h
    apply v.2
    apply Subtype.ext
    exact h⟩
  invFun v := ⟨⟨v.1, v.2.1, v.2.2.1⟩, by
    intro h
    exact v.2.2.2 (congrArg Subtype.val h)⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    rfl
  map_rel_iff' := Iff.rfl

/--
After deleting one arbitrary ambient vertex in addition to the two roots,
the remaining graph is connected.  This is the precise connectivity
content behind COY Case 1.2.
-/
private theorem connected_after_deleting_roots_and
    (M : MinimalCounterexample q G x y z)
    (C : TypeTwoCore G x ℓ)
    (hyS : y ∉ C.S) (hyT : y ∉ C.T)
    {s₁ s₂ : V} (hsne : s₁ ≠ s₂)
    (hS : C.S = {s₁, s₂})
    (hNx : G.neighborSet x = (↑C.S : Set V))
    (hNy : G.neighborSet y = (↑C.S : Set V))
    (r : V) :
    (G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ r}).Connected := by
  classical
  have hTtwo : 2 ≤ C.T.card := by
    rw [C.card_T]
    exact C.rank_ge_two
  obtain ⟨ta, htaT, tb, htbT, htab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < C.T.card)
  let t₀ : V := if ta = r then tb else ta
  have ht₀T : t₀ ∈ C.T := by
    dsimp [t₀]
    split
    · exact htbT
    · exact htaT
  have ht₀r : t₀ ≠ r := by
    dsimp [t₀]
    split <;> rename_i hta
    · intro htb
      exact htab (hta.trans htb.symm)
    · exact hta
  let s₀ : V := if s₁ = r then s₂ else s₁
  have hs₀S : s₀ ∈ C.S := by
    rw [hS]
    dsimp [s₀]
    split <;> simp
  have hs₀r : s₀ ≠ r := by
    dsimp [s₀]
    split <;> rename_i hs₁
    · intro hs₂
      exact hsne (hs₁.trans hs₂.symm)
    · exact hs₁
  have hs₀x : s₀ ≠ x := by
    intro h
    exact C.root_not_mem_S (h ▸ hs₀S)
  have hs₀y : s₀ ≠ y := by
    intro h
    exact hyS (h ▸ hs₀S)
  have ht₀x : t₀ ≠ x := by
    intro h
    exact C.root_not_mem_T (h ▸ ht₀T)
  have ht₀y : t₀ ≠ y := by
    intro h
    exact hyT (h ▸ ht₀T)
  let U : Set V := {v | v ≠ x ∧ v ≠ y ∧ v ≠ r}
  let R : Set V := {v | v ≠ r}
  let s₀U : U := ⟨s₀, hs₀x, hs₀y, hs₀r⟩
  let t₀U : U := ⟨t₀, ht₀x, ht₀y, ht₀r⟩
  let rep : R → U := fun v =>
    if hvx : v.1 = x then s₀U
    else if hvy : v.1 = y then s₀U
    else ⟨v.1, hvx, hvy, v.2⟩
  have hcoreRoute (s : V) (hsS : s ∈ C.S) (hsr : s ≠ r) :
      (G.induce U).Reachable s₀U
        (⟨s,
          fun h => C.root_not_mem_S (h ▸ hsS),
          fun h => hyS (h ▸ hsS), hsr⟩ : U) := by
    let sU : U := ⟨s,
      fun h => C.root_not_mem_S (h ▸ hsS),
      fun h => hyS (h ▸ hsS), hsr⟩
    have hleft : (G.induce U).Adj s₀U t₀U :=
      C.cross_adj s₀ hs₀S t₀ ht₀T
    have hright : (G.induce U).Adj t₀U sU :=
      (C.cross_adj s hsS t₀ ht₀T).symm
    exact hleft.reachable.trans hright.reachable
  have hstep :
      ∀ a b : R, (G.induce R).Adj a b →
        (G.induce U).Reachable (rep a) (rep b) := by
    intro a b hab
    by_cases hax : a.1 = x
    · have hby : b.1 ≠ y := by
        intro hby
        exact M.roots_not_adj (by
          simpa [hax, hby] using hab)
      have hbx : b.1 ≠ x := by
        intro hbx
        change G.Adj a.1 b.1 at hab
        rw [hax, hbx] at hab
        exact G.loopless.irrefl x hab
      have hbS : b.1 ∈ C.S := by
        have hxb : G.Adj x b.1 := by
          simpa [hax] using hab
        have hbN : b.1 ∈ G.neighborSet x := by
          simpa [SimpleGraph.mem_neighborSet] using hxb
        rw [hNx] at hbN
        exact hbN
      have hroute := hcoreRoute b.1 hbS b.2
      simpa [rep, hax, hbx, hby] using hroute
    · by_cases hay : a.1 = y
      · have hby : b.1 ≠ y := by
          intro hby
          change G.Adj a.1 b.1 at hab
          rw [hay, hby] at hab
          exact G.loopless.irrefl y hab
        have hbx : b.1 ≠ x := by
          intro hbx
          exact M.roots_not_adj (by
            simpa [hay, hbx] using hab.symm)
        have hbS : b.1 ∈ C.S := by
          have hyb : G.Adj y b.1 := by
            simpa [hay] using hab
          have hbN : b.1 ∈ G.neighborSet y := by
            simpa [SimpleGraph.mem_neighborSet] using hyb
          rw [hNy] at hbN
          exact hbN
        have hroute := hcoreRoute b.1 hbS b.2
        simpa [rep, hax, hay, hbx, hby] using hroute
      · by_cases hbx : b.1 = x
        · have haS : a.1 ∈ C.S := by
            have hxa : G.Adj x a.1 := by
              simpa [hbx] using hab.symm
            have haN : a.1 ∈ G.neighborSet x := by
              simpa [SimpleGraph.mem_neighborSet] using hxa
            rw [hNx] at haN
            exact haN
          have hroute := (hcoreRoute a.1 haS a.2).symm
          simpa [rep, hax, hay, hbx] using hroute
        · by_cases hby : b.1 = y
          · have haS : a.1 ∈ C.S := by
              have hya : G.Adj y a.1 := by
                simpa [hby] using hab.symm
              have haN : a.1 ∈ G.neighborSet y := by
                simpa [SimpleGraph.mem_neighborSet] using hya
              rw [hNy] at haN
              exact haN
            have hroute := (hcoreRoute a.1 haS a.2).symm
            simpa [rep, hax, hay, hbx, hby] using hroute
          · have hadj :
                (G.induce U).Adj
                  (⟨a.1, hax, hay, a.2⟩ : U)
                  (⟨b.1, hbx, hby, b.2⟩ : U) :=
              hab
            simpa [rep, hax, hay, hbx, hby] using hadj.reachable
  have hbase :
      (G.induce R).Connected := by
    have h :=
      M.underlying_two_connected.2 ({r} : Finset V) (by simp)
    have hset :
        {v : V | v ∉ ({r} : Finset V)} =
          {v : V | v ≠ r} := by
      ext v
      simp
    rw [hset] at h
    simpa [R] using h
  refine {
    preconnected := ?_
    nonempty := ⟨s₀U⟩
  }
  intro a b
  let aR : R := ⟨a.1, a.2.2.2⟩
  let bR : R := ⟨b.1, b.2.2.2⟩
  have habR : (G.induce R).Reachable aR bR :=
    hbase.preconnected aR bR
  have habR' :
      Relation.ReflTransGen (G.induce R).Adj aR bR :=
    (SimpleGraph.reachable_iff_reflTransGen aR bR).mp habR
  have hstep' :
      (G.induce R).Adj ≤
        Function.onFun
          (Relation.ReflTransGen (G.induce U).Adj) rep := by
    intro v w hvw
    exact
      (SimpleGraph.reachable_iff_reflTransGen
        (rep v) (rep w)).mp (hstep v w hvw)
  have hlift :=
    habR'.lift' rep hstep'
  have hrepA : rep aR = a := by
    apply Subtype.ext
    simp [rep, aR, a.2.1, a.2.2.1]
  have hrepB : rep bR = b := by
    apply Subtype.ext
    simp [rep, bR, b.2.1, b.2.2.1]
  change
    Relation.ReflTransGen (G.induce U).Adj
      (rep aR) (rep bR) at hlift
  rw [hrepA, hrepB] at hlift
  exact (SimpleGraph.reachable_iff_reflTransGen a b).mpr
    (by simpa [U] using hlift)

/--
The graph left after deleting the two original roots is 2-connected.
The order bound and every one-vertex deletion are both recorded explicitly.
-/
theorem graph_two_connected
    (M : MinimalCounterexample q G x y z)
    (C : TypeTwoCore G x ℓ)
    (hyS : y ∉ C.S) (hyT : y ∉ C.T)
    {s₁ s₂ : V} (hsne : s₁ ≠ s₂)
    (hS : C.S = {s₁, s₂})
    (hNx : G.neighborSet x = (↑C.S : Set V))
    (hNy : G.neighborSet y = (↑C.S : Set V)) :
    IsTwoConnected (graph G x y) := by
  classical
  have horder : 3 ≤ Fintype.card (Vertex x y) := by
    rw [card_vertex x y M.roots_ne]
    have hfive := M.five_le_card
    omega
  have hconnectedTriple :=
    connected_after_deleting_roots_and
      M C hyS hyT hsne hS hNx hNy x
  have hconnected : (graph G x y).Connected :=
    (SimpleGraph.Iso.connected_iff
      (graphIsoTripleAtLeft G x y)).mpr hconnectedTriple
  apply isTwoConnected_of_connected_delete_one
    (graph G x y) horder hconnected
  intro r
  have htriple :=
    connected_after_deleting_roots_and
      M C hyS hyT hsne hS hNx hNy r.1
  exact
    (SimpleGraph.Iso.connected_iff
      (deleteOneIso G x y r)).mpr htriple

/--
COY Case 1.2 with its type-2 core and twin-root neighborhoods made
explicit.  The conclusion contradicts minimality.
-/
theorem contradiction
    (M : MinimalCounterexample q G x y z)
    (C : TypeTwoCore G x ℓ)
    (hyS : y ∉ C.S) (hyT : y ∉ C.T)
    (hNx : G.neighborSet x = (↑C.S : Set V))
    (hNy : G.neighborSet y = (↑C.S : Set V)) :
    False := by
  classical
  obtain ⟨s₁, s₂, hsne, hS⟩ :=
    Finset.card_eq_two.mp C.card_S
  have hs₁S : s₁ ∈ C.S := by
    rw [hS]
    simp
  have hs₂S : s₂ ∈ C.S := by
    rw [hS]
    simp
  have hs₁x : s₁ ≠ x := by
    intro h
    exact C.root_not_mem_S (h ▸ hs₁S)
  have hs₂x : s₂ ≠ x := by
    intro h
    exact C.root_not_mem_S (h ▸ hs₂S)
  have hs₁y : s₁ ≠ y := by
    intro h
    exact hyS (h ▸ hs₁S)
  have hs₂y : s₂ ≠ y := by
    intro h
    exact hyS (h ▸ hs₂S)
  let A := graph G x y
  let s₁A : Vertex x y :=
    vertex x y s₁ hs₁x hs₁y
  let s₂A : Vertex x y :=
    vertex x y s₂ hs₂x hs₂y
  have hs₁s₂A : s₁A ≠ s₂A := by
    intro h
    exact hsne (congrArg Subtype.val h)
  have hAtwo : IsTwoConnected A := by
    exact graph_two_connected
      M C hyS hyT hsne hS hNx hNy
  have hrooted :
      IsTwoConnected (A ⊔ edge s₁A s₂A) :=
    hAtwo.mono le_sup_left
  have hcomplexity :
      rootedComplexity A < rootedComplexity G := by
    apply rootedComplexity_lt_of_card_lt_of_edgeCount_le
    · rw [card_vertex x y M.roots_ne]
      have hfive := M.five_le_card
      omega
    · exact edgeSet_ncard_le G x y
  have hdegreeWithException :
      ∀ v : Vertex x y, v ≠ s₁A → v ≠ s₂A →
        v.1 ≠ z → q + 1 ≤ finiteDegree A v := by
    intro v hv₁ hv₂ hvz
    have hvS : v.1 ∉ C.S := by
      rw [hS]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hv
      rcases hv with hv | hv
      ·
        apply hv₁
        apply Subtype.ext
        exact hv
      ·
        apply hv₂
        apply Subtype.ext
        exact hv
    have hinside :
        ∀ w, G.Adj v.1 w → w ∈ vertices x y := by
      intro w hvw
      constructor
      · intro hwx
        subst w
        apply hvS
        have hvN : v.1 ∈ G.neighborSet x := by
          simpa [SimpleGraph.mem_neighborSet] using hvw.symm
        rw [hNx] at hvN
        exact hvN
      · intro hwy
        subst w
        apply hvS
        have hvN : v.1 ∈ G.neighborSet y := by
          simpa [SimpleGraph.mem_neighborSet] using hvw.symm
        rw [hNy] at hvN
        exact hvN
    calc
      q + 1 ≤ finiteDegree G v.1 := by
        exact M.degree_lower v.1 v.2.1 v.2.2 hvz
      _ ≤ finiteDegree A v :=
        finiteDegree_le_induce G (vertices x y) v hinside
  have hfamily :
      Nonempty (AdmissiblePathFamily A s₁A s₂A q) := by
    by_cases hz : z ≠ x ∧ z ≠ y
    · let zA : Vertex x y :=
        vertex x y z hz.1 hz.2
      obtain ⟨ta, htaT, tb, htbT, htab⟩ :=
        Finset.one_lt_card.mp
          (by
            rw [C.card_T]
            have hrank := C.rank_ge_two
            omega :
            1 < C.T.card)
      let t : V := if ta = z then tb else ta
      have htT : t ∈ C.T := by
        dsimp [t]
        split
        · exact htbT
        · exact htaT
      have htz : t ≠ z := by
        dsimp [t]
        split <;> rename_i hta
        · intro htb
          exact htab (hta.trans htb.symm)
        · exact hta
      have htNotS : t ∉ C.S :=
        fun htS =>
          Finset.disjoint_left.mp C.disjoint htS htT
      have htx : t ≠ x := by
        intro h
        exact C.root_not_mem_T (h ▸ htT)
      have hty : t ≠ y := by
        intro h
        exact hyT (h ▸ htT)
      let tA : Vertex x y :=
        vertex x y t htx hty
      let I : RootedInstance q A s₁A s₂A zA := {
        q_pos := M.q_pos
        q_le_four := M.q_le_four
        roots_ne := hs₁s₂A
        rooted_two_connected := hrooted
        ordinary_nonempty := by
          refine ⟨tA, ?_, ?_, ?_⟩
          · intro h
            apply htNotS
            rw [hS]
            simp only [Finset.mem_insert, Finset.mem_singleton]
            left
            exact congrArg Subtype.val h
          · intro h
            apply htNotS
            rw [hS]
            simp only [Finset.mem_insert, Finset.mem_singleton]
            right
            exact congrArg Subtype.val h
          · intro h
            exact htz (congrArg Subtype.val h)
        degree_lower := by
          intro v hv₁ hv₂ hvz
          apply hdegreeWithException v hv₁ hv₂
          intro h
          apply hvz
          apply Subtype.ext
          exact h
      }
      exact M.smaller_solvable I hcomplexity
    · have hzRemoved : z = x ∨ z = y := by
        by_cases hzx : z = x
        · exact Or.inl hzx
        · right
          by_contra hzy
          exact hz ⟨hzx, hzy⟩
      let I : RootedInstance q A s₁A s₂A s₁A :=
        RootedInstance.ofNoExtraException
          q A s₁A s₂A M.q_pos M.q_le_four
          hs₁s₂A hrooted
          (by
            intro v hv₁ hv₂
            apply hdegreeWithException v hv₁ hv₂
            rcases hzRemoved with rfl | rfl
            · exact v.2.1
            · exact v.2.2)
      exact M.smaller_solvable I hcomplexity
  obtain ⟨F⟩ := hfamily
  let mapped : AdmissiblePathFamily G s₁ s₂ q := by
    change AdmissiblePathFamily G
      ((s₁A : Vertex x y) : V)
      ((s₂A : Vertex x y) : V) q
    exact F.mapInjectiveHom
      (embedding G x y).toHom
      (embedding G x y).injective
  let left : SimplePath G x s₁ :=
    SimplePath.ofAdj (C.root_adj_S s₁ hs₁S)
  have hs₂yAdj : G.Adj s₂ y := by
    have hs₂N : s₂ ∈ G.neighborSet y := by
      rw [hNy]
      exact hs₂S
    simpa [SimpleGraph.mem_neighborSet] using hs₂N.symm
  let right : SimplePath G s₂ y :=
    SimplePath.ofAdj hs₂yAdj
  have hleftDisjoint :
      ∀ i, left.walk.support.Disjoint
        (mapped.path i).walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvLeft hvTail
    have hvClass : v = x ∨ v = s₁ := by
      simpa [left] using hvLeft
    rcases hvClass with hvx | hv₁
    · have hxSupport :
          x ∈ (mapped.path i).walk.support :=
        by
          apply List.mem_of_mem_tail
          simpa [hvx] using hvTail
      change
        x ∈ ((F.path i).mapInjectiveHom
          (embedding G x y).toHom
          (embedding G x y).injective).walk.support at hxSupport
      have hxRange :=
        SimplePath.mem_range_of_mem_mapInjectiveHom_support
          (P := F.path i)
          (f := (embedding G x y).toHom)
          (hinj := (embedding G x y).injective)
          hxSupport
      obtain ⟨w, hw⟩ := hxRange
      exact w.2.1 hw
    · exact (mapped.path i).start_not_mem_tail
        (by simpa [hv₁] using hvTail)
  let prep :=
    mapped.prependFixed left hleftDisjoint
  have hrightDisjoint :
      ∀ i, (prep.path i).walk.support.Disjoint
        right.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvPrep hvRight
    have hvy : v = y := by
      simpa [right] using hvRight
    subst v
    have hvParts :
        y ∈ left.walk.support ∨
          y ∈ (mapped.path i).walk.support := by
      simpa [prep, SimplePath.appendDisjoint] using hvPrep
    rcases hvParts with hyLeft | hyMapped
    · have hyClass : y = x ∨ y = s₁ := by
        simpa [left] using hyLeft
      exact hyClass.elim
        (fun hyx => M.roots_ne hyx.symm)
        (fun hys => hs₁y hys.symm)
    · have hyRange :=
        have hyMapped' :
            y ∈ ((F.path i).mapInjectiveHom
              (embedding G x y).toHom
              (embedding G x y).injective).walk.support := by
          change y ∈ (mapped.path i).walk.support
          exact hyMapped
        SimplePath.mem_range_of_mem_mapInjectiveHom_support
          (P := F.path i)
          (f := (embedding G x y).toHom)
          (hinj := (embedding G x y).injective)
          hyMapped'
      obtain ⟨w, hw⟩ := hyRange
      exact w.2.2 hw
  exact M.no_paths
    ⟨prep.appendFixed right hrightDisjoint⟩

end SingletonTypeTwoDeletion

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
COY Case 1.2 in the selected-core interface.  Claim 3.5 supplies the twin
two-element neighborhood, after which the explicit deletion argument above
eliminates the minimal counterexample.
-/
theorem false_of_natural_singleton_typeTwo
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty
        (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype : D.chosen.rooted.core.typeNumber = 2) :
    False := by
  have hneighbors :=
    D.neighborSets_eq_S_of_natural_singleton
      M hnot hregion htype
  cases hcore : D.chosen.rooted.core with
  | typeOne C =>
      simp [hcore, Core.typeNumber] at htype
  | typeThree C =>
      simp [hcore, Core.typeNumber] at htype
  | typeTwo C =>
      have hyS : y ∉ C.S := by
        intro hy
        apply D.chosen.rooted.other_root_not_mem
        rw [hcore]
        simp [Core.carrier, Core.S, Core.T, hy]
      have hyT : y ∉ C.T := by
        intro hy
        apply D.chosen.rooted.other_root_not_mem
        rw [hcore]
        simp [Core.carrier, Core.S, Core.T, hy]
      have hNy :
          G.neighborSet y = (↑C.S : Set V) := by
        simpa [hcore, Core.S] using hneighbors.2
      have hNx :
          G.neighborSet x = (↑C.S : Set V) := by
        exact hneighbors.1.trans hNy
      exact SingletonTypeTwoDeletion.contradiction
        M C hyS hyT hNx hNy

end MinimalCounterexample

end COY

end DeanK5
