import DeanK5.Graph.Separation

/-!
# Existence of two end lobes

This file develops the ordinary finite block-cut argument needed by the
paper.  A lobe region is a connected component behind one cut vertex,
recorded on the original carrier.  Choosing such a region with minimum
interior cardinality forces its closure with the cut vertex to be
2-connected.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/-- A connected nonempty region whose only possible outside neighbor is one
distinguished cut vertex. -/
structure LobeRegion
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The vertices strictly inside the lobe region. -/
  inner : Finset V
  /-- The unique vertex through which the region may meet its complement. -/
  cut : V
  inner_nonempty : inner.Nonempty
  cut_not_inner : cut ∉ inner
  inner_connected :
    (G.induce (↑inner : Set V)).Connected
  closed :
    ∀ ⦃x y : V⦄, x ∈ inner → G.Adj x y →
      y ∈ inner ∨ y = cut
  cut_adj_inner :
    ∃ x ∈ inner, G.Adj cut x

namespace LobeRegion

variable [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}

/-- The vertices in the closure of a lobe region. -/
def carrier (L : LobeRegion G) : Finset V :=
  insert L.cut L.inner

/-- The graph induced by the closure of a lobe region. -/
abbrev blockGraph (L : LobeRegion G) :=
  G.induce (↑L.carrier : Set V)

/-- A lobe region lies inside an initial side of a separator. -/
def Within
    (L : LobeRegion G) (Q : Finset V) (c : V) : Prop :=
  L.inner ⊆ Q ∧ L.cut ∈ insert c Q

theorem within_self (L : LobeRegion G) :
    L.Within L.inner L.cut :=
  ⟨fun _ h => h, Finset.mem_insert_self _ _⟩

/-- Every lobe region contains a subregion of minimum interior cardinality. -/
theorem exists_minimal_within
    (L₀ : LobeRegion G) :
    ∃ L : LobeRegion G,
      L.Within L₀.inner L₀.cut ∧
      ∀ K : LobeRegion G,
        K.Within L₀.inner L₀.cut →
          L.inner.card ≤ K.inner.card := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ L : LobeRegion G,
      L.Within L₀.inner L₀.cut ∧
        L.inner.card = n
  have hP : ∃ n, P n :=
    ⟨L₀.inner.card, L₀,
      L₀.within_self, rfl⟩
  let n := Nat.find hP
  obtain ⟨L, hwithin, hcard⟩ :=
    Nat.find_spec hP
  refine ⟨L, hwithin, ?_⟩
  intro K hK
  have hnle :
      n ≤ K.inner.card :=
    Nat.find_min' hP
      ⟨K, hK, rfl⟩
  omega

/-- The closure of every lobe region is connected. -/
theorem block_connected
    (L : LobeRegion G) :
    L.blockGraph.Connected := by
  classical
  obtain ⟨q, hqInner, hcq⟩ :=
    L.cut_adj_inner
  let qI : (↑L.inner : Set V) :=
    ⟨q, hqInner⟩
  let qB : (↑L.carrier : Set V) :=
    ⟨q, Finset.mem_insert.mpr (Or.inr hqInner)⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨qB, ?_⟩
  intro z
  rcases Finset.mem_insert.mp z.2 with hzCut | hzInner
  · have hqz : L.blockGraph.Adj qB z := by
      change G.Adj q z.1
      simpa [hzCut] using hcq.symm
    exact hqz.reachable
  · let zI : (↑L.inner : Set V) :=
      ⟨z.1, hzInner⟩
    let f :
        G.induce (↑L.inner : Set V) →g
          L.blockGraph :=
      (G.induceHomOfLE
        (show (↑L.inner : Set V) ⊆
            (↑L.carrier : Set V) from
          fun x hx =>
            Finset.mem_insert.mpr (Or.inr hx))).toHom
    have hreach :
        (G.induce (↑L.inner : Set V)).Reachable
          qI zI :=
      L.inner_connected qI zI
    have hmapped := hreach.map f
    have hqeq : f qI = qB := by
      apply Subtype.ext
      rfl
    have hzeq : f zI = z := by
      apply Subtype.ext
      rfl
    simpa [hqeq, hzeq] using hmapped

/-- Ambient minimum degree three gives the lobe closure at least three
vertices. -/
theorem three_le_card_block
    (L : LobeRegion G)
    (hdegree : MinDegreeAtLeast G 3) :
    3 ≤ Fintype.card (↑L.carrier : Set V) := by
  classical
  obtain ⟨x, hx⟩ := L.inner_nonempty
  let xB : (↑L.carrier : Set V) :=
    ⟨x, Finset.mem_insert.mpr (Or.inr hx)⟩
  have hinside :
      ∀ y, G.Adj x y →
        y ∈ (↑L.carrier : Set V) := by
    intro y hxy
    rcases L.closed hx hxy with hy | rfl
    · exact Finset.mem_insert.mpr (Or.inr hy)
    · exact Finset.mem_insert_self _ _
  have hdegreeBlock :
      3 ≤ finiteDegree L.blockGraph xB :=
    (hdegree x).trans
      (finiteDegree_le_induce
        G (↑L.carrier : Set V) xB hinside)
  calc
    3 ≤ finiteDegree L.blockGraph xB :=
      hdegreeBlock
    _ ≤ (Set.univ :
        Set (↑L.carrier : Set V)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _)
    _ = Fintype.card (↑L.carrier : Set V) := by
      simp

/-- A component after deleting one vertex gives a lobe region, with its
interior and cut vertex exposed on the original carrier. -/
theorem exists_ofComponent
    (hconnected : G.Connected)
    (c : V)
    (C : (deleteVertices G {c}).ConnectedComponent) :
    ∃ L : LobeRegion G,
      L.inner = componentVertices G {c} C ∧
      L.cut = c := by
  classical
  let Q := componentVertices G {c} C
  have hQ : ComponentRegion G {c} Q :=
    componentRegion_componentVertices G {c} C
  obtain ⟨q, hq⟩ := hQ.nonempty
  obtain ⟨p, -⟩ :=
    hconnected.exists_isPath q c
  obtain ⟨x, hxQ, -, s, hs, -, hxs⟩ :=
    hQ.exists_boundary_edge_of_walk hq
      (by simp) p
  have hsc : s = c := by
    simpa using hs
  subst s
  exact ⟨{
    inner := Q
    cut := c
    inner_nonempty := hQ.nonempty
    cut_not_inner := by
      intro hcQ
      exact hQ.not_mem_separator hcQ (by simp)
    inner_connected := hQ.connected
    closed := by
      intro u v hu huv
      by_cases hvc : v = c
      · exact Or.inr hvc
      · exact Or.inl
          (hQ.mem_of_adj_of_not_mem_separator
            hu huv (by simpa using hvc))
    cut_adj_inner := ⟨x, hxQ, hxs.symm⟩
  }, rfl, rfl⟩

/-- The interior of a lobe region in `L.blockGraph`, transported back to the
ambient carrier. -/
def ambientInner
    (L : LobeRegion G)
    (K : LobeRegion L.blockGraph) : Finset V :=
  K.inner.map
    ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_ambientInner_iff
    (L : LobeRegion G)
    (K : LobeRegion L.blockGraph)
    (v : V) :
    v ∈ ambientInner L K ↔
      ∃ z : (↑L.carrier : Set V),
        z ∈ K.inner ∧ z.1 = v := by
  simp only [ambientInner, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, hzv⟩
    exact ⟨z, hz, hzv⟩
  · rintro ⟨z, hz, hzv⟩
    exact ⟨z, hz, hzv⟩

/-- The interior inclusion used to transport connectedness from a lobe of an
induced block to the ambient graph. -/
def ambientInnerEmbedding
    (L : LobeRegion G)
    (K : LobeRegion L.blockGraph) :
    (L.blockGraph.induce (↑K.inner :
      Set (↑L.carrier : Set V))) ↪g G where
  toFun z := z.1.1
  inj' := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  map_rel_iff' := Iff.rfl

theorem range_ambientInnerEmbedding
    (L : LobeRegion G)
    (K : LobeRegion L.blockGraph) :
    Set.range (ambientInnerEmbedding L K) =
      (↑(ambientInner L K) : Set V) := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact (mem_ambientInner_iff L K z.1.1).2
      ⟨z.1, z.2, rfl⟩
  · intro hv
    obtain ⟨z, hz, hzv⟩ :=
      (mem_ambientInner_iff L K v).1 hv
    exact ⟨⟨z, hz⟩, hzv⟩

/--
A lobe region inside `L.blockGraph` that avoids the old cut vertex in its
interior is again a lobe region of the ambient graph.
-/
noncomputable def ambientLobeRegion
    (L : LobeRegion G)
    (K : LobeRegion L.blockGraph)
    (hold :
      (⟨L.cut, Finset.mem_insert_self _ _⟩ :
        (↑L.carrier : Set V)) ∉ K.inner) :
    LobeRegion G where
  inner := ambientInner L K
  cut := K.cut.1
  inner_nonempty := by
    obtain ⟨z, hz⟩ := K.inner_nonempty
    exact ⟨z.1,
      (mem_ambientInner_iff L K z.1).2
        ⟨z, hz, rfl⟩⟩
  cut_not_inner := by
    intro hcut
    obtain ⟨z, hz, hzeq⟩ :=
      (mem_ambientInner_iff L K K.cut.1).1 hcut
    apply K.cut_not_inner
    have : z = K.cut :=
      Subtype.ext hzeq
    simpa [this] using hz
  inner_connected := by
    let f := ambientInnerEmbedding L K
    have hrange :
        Set.range f =
          (↑(ambientInner L K) : Set V) := by
      simpa [f] using range_ambientInnerEmbedding L K
    let e :
        L.blockGraph.induce
            (↑K.inner : Set (↑L.carrier : Set V)) ≃g
          G.induce (↑(ambientInner L K) : Set V) := by
      let e' := f.isoInduceRange
      rw [hrange] at e'
      exact e'
    exact (SimpleGraph.Iso.connected_iff e).mp
      K.inner_connected
  closed := by
    intro u v hu huv
    obtain ⟨uB, huK, huval⟩ :=
      (mem_ambientInner_iff L K u).1 hu
    have huInner : u ∈ L.inner := by
      rcases Finset.mem_insert.mp uB.2 with huCut | huInner
      · apply False.elim
        apply hold
        have huBEq :
            uB =
              (⟨L.cut, Finset.mem_insert_self _ _⟩ :
                (↑L.carrier : Set V)) := by
          apply Subtype.ext
          exact huCut
        simpa [huBEq] using huK
      · simpa [huval] using huInner
    have hvCarrier : v ∈ L.carrier := by
      rcases L.closed huInner (by simpa [huval] using huv) with
          hvInner | hvCut
      · exact Finset.mem_insert.mpr (Or.inr hvInner)
      · exact Finset.mem_insert.mpr (Or.inl hvCut)
    let vB : (↑L.carrier : Set V) :=
      ⟨v, hvCarrier⟩
    have huvB : L.blockGraph.Adj uB vB := by
      change G.Adj uB.1 vB.1
      simpa [huval]
    rcases K.closed huK huvB with hvK | hvCut
    · exact Or.inl
        ((mem_ambientInner_iff L K v).2
          ⟨vB, hvK, rfl⟩)
    · exact Or.inr (congrArg Subtype.val hvCut)
  cut_adj_inner := by
    obtain ⟨z, hzK, hcutz⟩ :=
      K.cut_adj_inner
    exact ⟨z.1,
      (mem_ambientInner_iff L K z.1).2
        ⟨z, hzK, rfl⟩,
      hcutz⟩

/-- The interior of a lobe region is a component region behind its cut. -/
theorem componentRegion
    (L : LobeRegion G) :
    ComponentRegion G {L.cut} L.inner where
  nonempty := L.inner_nonempty
  disjoint := by
    apply Finset.disjoint_left.mpr
    intro v hvInner hvCut
    apply L.cut_not_inner
    have hvEq : v = L.cut := by
      simpa using hvCut
    simpa [hvEq] using hvInner
  connected := L.inner_connected
  closed := by
    intro u v hu huv hvCut
    rcases L.closed hu huv with hvInner | rfl
    · exact hvInner
    · exact False.elim (hvCut (by simp))

/--
A simple path from the cut of a lobe to a vertex outside its interior cannot
enter the interior. Any such excursion would have to return through the cut
and repeat that vertex.
-/
theorem simplePath_from_cut_avoids_inner
    (L : LobeRegion G)
    {y : V} (hy : y ∉ L.inner)
    (P : SimplePath G L.cut y) :
    ∀ v ∈ P.walk.support, v ∉ L.inner := by
  intro v hvSupport hvInner
  let q := P.walk.takeUntil v hvSupport
  let r := P.walk.dropUntil v hvSupport
  have hcutR : L.cut ∈ r.support := by
    by_contra havoid
    have hyInner :=
      L.componentRegion.endpoint_mem_of_walk_avoiding_separator
        hvInner r (by
          intro z hz
          simpa using fun hzCut : z = L.cut =>
            havoid (hzCut ▸ hz))
    exact hy hyInner
  have hPathAppend :
      (q.append r).IsPath := by
    simpa [q, r] using P.isPath
  have hcutQ : L.cut ∈ q.support :=
    q.start_mem_support
  have hcutNeV : L.cut ≠ v := by
    intro h
    apply L.cut_not_inner
    simpa [h] using hvInner
  exact
    (hPathAppend.ne_of_mem_support_of_append
      hcutNeV hcutQ hcutR) rfl

/-- The reverse orientation of `simplePath_from_cut_avoids_inner`. -/
theorem simplePath_to_cut_avoids_inner
    (L : LobeRegion G)
    {x : V} (hx : x ∉ L.inner)
    (P : SimplePath G x L.cut) :
    ∀ v ∈ P.walk.support, v ∉ L.inner := by
  intro v hv
  apply L.simplePath_from_cut_avoids_inner
    hx P.reverse v
  simpa [SimplePath.reverse] using hv

/-- A certified 2-connected lobe region is an `EndLobe`. -/
def toEndLobe
    (L : LobeRegion G)
    (htwo : IsTwoConnected L.blockGraph) :
    EndLobe G where
  inner := L.inner
  cut := L.cut
  inner_nonempty := L.inner_nonempty
  cut_not_inner := L.cut_not_inner
  block_two_connected := htwo
  inner_connected := L.inner_connected
  closed := L.closed

end LobeRegion

namespace ClassicalGraphTheory

/--
Failure of 2-connectivity in a connected graph of minimum degree three is
witnessed by deletion of one vertex, with at least two resulting connected
components.
-/
private theorem exists_cut_with_two_components
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hconnected : G.Connected)
    (hnotTwo : ¬ IsTwoConnected G)
    (horder : 3 ≤ Fintype.card V) :
    ∃ c : V,
      ∃ C₀ C₁ : (deleteVertices G {c}).ConnectedComponent,
        C₀ ≠ C₁ := by
  classical
  have hnotDeletion :
      ¬ ∀ S : Finset V, S.card < 2 →
        (G.induce {v : V | v ∉ S}).Connected := by
    intro h
    exact hnotTwo ⟨horder, h⟩
  push Not at hnotDeletion
  obtain ⟨S, hScard, hSnot⟩ := hnotDeletion
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    apply hSnot
    have hInduced :
        (G.induce (Set.univ : Set V)).Connected :=
      (SimpleGraph.Iso.connected_iff
        (SimpleGraph.induceUnivIso G)).mpr hconnected
    have hset :
        {v : V | v ∉ (∅ : Finset V)} =
          (Set.univ : Set V) := by
      ext z
      simp
    rw [hset]
    exact hInduced
  have hScardOne : S.card = 1 := by
    have hpos := Finset.card_pos.mpr hSnonempty
    omega
  obtain ⟨c, rfl⟩ :=
    Finset.card_eq_one.mp hScardOne
  let M := deleteVertices G {c}
  have hMnonempty : Nonempty {v : V // v ∉ ({c} : Finset V)} := by
    have hproper :
        ({c} : Finset V).card <
          (Finset.univ : Finset V).card := by
      simp only [Finset.card_singleton,
        Finset.card_univ]
      omega
    obtain ⟨z, -, hz⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hproper
    exact ⟨⟨z, hz⟩⟩
  letI : Nonempty {v : V // v ∉ ({c} : Finset V)} :=
    hMnonempty
  have hMnotPreconnected : ¬M.Preconnected := by
    intro hpre
    exact hSnot {
      preconnected := hpre
      nonempty := hMnonempty
    }
  unfold SimpleGraph.Preconnected at hMnotPreconnected
  push Not at hMnotPreconnected
  obtain ⟨a, b, hab⟩ := hMnotPreconnected
  let C₀ : M.ConnectedComponent :=
    M.connectedComponentMk a
  let C₁ : M.ConnectedComponent :=
    M.connectedComponentMk b
  refine ⟨c, C₀, C₁, ?_⟩
  intro hEq
  exact hab
    (SimpleGraph.ConnectedComponent.exact hEq)

/--
Among two distinct components of a block with one vertex deleted, one avoids
the old cut vertex of the containing lobe.
-/
private theorem exists_component_avoiding_old_cut
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (L : LobeRegion G)
    (e : (↑L.carrier : Set V))
    (C₀ C₁ :
      (deleteVertices L.blockGraph {e}).ConnectedComponent)
    (hne : C₀ ≠ C₁) :
    ∃ C D :
        (deleteVertices L.blockGraph {e}).ConnectedComponent,
      C ≠ D ∧
      (⟨L.cut, Finset.mem_insert_self _ _⟩ :
        (↑L.carrier : Set V)) ∉
          componentVertices L.blockGraph {e} C := by
  classical
  let old :
      (↑L.carrier : Set V) :=
    ⟨L.cut, Finset.mem_insert_self _ _⟩
  by_cases holde : old = e
  · refine ⟨C₀, C₁, hne, ?_⟩
    intro holdC
    obtain ⟨holdNot, -⟩ :=
      (mem_componentVertices_iff
        L.blockGraph {e} C₀ old).1 holdC
    apply holdNot
    simp [holde]
  · have holdNotE : old ∉ ({e} :
        Finset (↑L.carrier : Set V)) := by
      simpa using holde
    let oldDeleted :
        {z : (↑L.carrier : Set V) //
          z ∉ ({e} :
            Finset (↑L.carrier : Set V))} :=
      ⟨old, holdNotE⟩
    let Croot :=
      (deleteVertices L.blockGraph {e}).connectedComponentMk
        oldDeleted
    have holdRoot :
        old ∈ componentVertices L.blockGraph {e} Croot := by
      apply (mem_componentVertices_iff
        L.blockGraph {e} Croot old).2
      exact ⟨holdNotE,
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    by_cases hC₀root : C₀ = Croot
    · have hC₁root : C₁ ≠ Croot := by
        intro hC₁
        exact hne (hC₀root.trans hC₁.symm)
      refine ⟨C₁, C₀, hne.symm, ?_⟩
      intro holdC₁
      exact Finset.disjoint_left.mp
        (disjoint_componentVertices
          L.blockGraph {e} hC₁root)
        holdC₁ holdRoot
    · refine ⟨C₀, C₁, hne, ?_⟩
      intro holdC₀
      exact Finset.disjoint_left.mp
        (disjoint_componentVertices
          L.blockGraph {e} hC₀root)
        holdC₀ holdRoot

/--
A component of a non-2-connected lobe block that avoids the old cut vertex
lifts to a strictly smaller ambient lobe region.
-/
private theorem exists_strict_subregion
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (L : LobeRegion G)
    (e : (↑L.carrier : Set V))
    (C D :
      (deleteVertices L.blockGraph {e}).ConnectedComponent)
    (hCD : C ≠ D)
    (hold :
      (⟨L.cut, Finset.mem_insert_self _ _⟩ :
        (↑L.carrier : Set V)) ∉
          componentVertices L.blockGraph {e} C) :
    ∃ K : LobeRegion G,
      K.Within L.inner L.cut ∧
      K.inner.card < L.inner.card := by
  classical
  obtain ⟨K, hKinner, hKcut⟩ :=
    LobeRegion.exists_ofComponent
      L.block_connected e C
  have holdK :
      (⟨L.cut, Finset.mem_insert_self _ _⟩ :
        (↑L.carrier : Set V)) ∉ K.inner := by
    simpa [hKinner] using hold
  let R : LobeRegion G :=
    LobeRegion.ambientLobeRegion L K holdK
  have hsubset : R.inner ⊆ L.inner := by
    intro v hvR
    obtain ⟨z, hzK, hzv⟩ :=
      (LobeRegion.mem_ambientInner_iff L K v).1 hvR
    rcases Finset.mem_insert.mp z.2 with hzCut | hzInner
    · have hzOld :
          z =
            (⟨L.cut, Finset.mem_insert_self _ _⟩ :
              (↑L.carrier : Set V)) := by
        apply Subtype.ext
        exact hzCut
      exact False.elim (holdK (by simpa [hzOld] using hzK))
    · simpa [hzv] using hzInner
  have hcutWithin :
      R.cut ∈ insert L.cut L.inner := by
    change K.cut.1 ∈ insert L.cut L.inner
    rw [hKcut]
    exact e.2
  have hwitness :
      ∃ v ∈ L.inner, v ∉ R.inner := by
    rcases Finset.mem_insert.mp e.2 with heCut | heInner
    · have hQD :
          ComponentRegion L.blockGraph {e}
            (componentVertices L.blockGraph {e} D) :=
        componentRegion_componentVertices
          L.blockGraph {e} D
      obtain ⟨q, hqD⟩ := hQD.nonempty
      have hqInner : q.1 ∈ L.inner := by
        rcases Finset.mem_insert.mp q.2 with hqCut | hqInner
        · have hqe : q = e := by
            apply Subtype.ext
            exact hqCut.trans heCut.symm
          exact False.elim
            (hQD.not_mem_separator hqD (by simp [hqe]))
        · exact hqInner
      refine ⟨q.1, hqInner, ?_⟩
      intro hqR
      obtain ⟨z, hzK, hzq⟩ :=
        (LobeRegion.mem_ambientInner_iff L K q.1).1 hqR
      have hzq' : z = q :=
        Subtype.ext hzq
      have hzC :
          q ∈ componentVertices L.blockGraph {e} C := by
        rw [hKinner] at hzK
        simpa [hzq'] using hzK
      exact Finset.disjoint_left.mp
        (disjoint_componentVertices
          L.blockGraph {e} hCD)
        hzC hqD
    · refine ⟨e.1, heInner, ?_⟩
      intro heR
      obtain ⟨z, hzK, hze⟩ :=
        (LobeRegion.mem_ambientInner_iff L K e.1).1 heR
      have hze' : z = e :=
        Subtype.ext hze
      apply K.cut_not_inner
      simpa [hKcut, hze'] using hzK
  have hne : R.inner ≠ L.inner := by
    rintro hEq
    obtain ⟨v, hvL, hvR⟩ := hwitness
    exact hvR (hEq ▸ hvL)
  exact ⟨R, ⟨hsubset, hcutWithin⟩,
    Finset.card_lt_card
      ((Finset.ssubset_iff_subset_ne).2
        ⟨hsubset, hne⟩)⟩

/--
An interior-cardinality-minimal lobe region inside a fixed initial side has
a 2-connected closure once that closure has at least three vertices.
-/
theorem minimal_within_block_two_connected_of_three_le_card
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (L₀ L : LobeRegion G)
    (hwithin : L.Within L₀.inner L₀.cut)
    (hminimal :
      ∀ K : LobeRegion G,
        K.Within L₀.inner L₀.cut →
          L.inner.card ≤ K.inner.card)
    (horder : 3 ≤ Fintype.card (↑L.carrier : Set V)) :
    IsTwoConnected L.blockGraph := by
  by_contra hnotTwo
  obtain ⟨e, C₀, C₁, hC₀C₁⟩ :=
    exists_cut_with_two_components
      L.blockGraph L.block_connected hnotTwo
      horder
  obtain ⟨C, D, hCD, hold⟩ :=
    exists_component_avoiding_old_cut
      L e C₀ C₁ hC₀C₁
  obtain ⟨K, hKwithinL, hsmaller⟩ :=
    exists_strict_subregion L e C D hCD hold
  have hKwithin₀ :
      K.Within L₀.inner L₀.cut := by
    refine ⟨fun v hv =>
      hwithin.1 (hKwithinL.1 hv), ?_⟩
    rcases Finset.mem_insert.mp hKwithinL.2 with
        hKcut | hKinner
    · rw [hKcut]
      exact hwithin.2
    · exact Finset.mem_insert.mpr
        (Or.inr (hwithin.1 hKinner))
  exact (Nat.not_le_of_gt hsmaller)
    (hminimal K hKwithin₀)

/--
The minimum-degree wrapper used by the ordinary two-end-lobe theorem.
-/
private theorem minimal_within_block_two_connected
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (L₀ L : LobeRegion G)
    (hwithin : L.Within L₀.inner L₀.cut)
    (hminimal :
      ∀ K : LobeRegion G,
        K.Within L₀.inner L₀.cut →
          L.inner.card ≤ K.inner.card)
    (hdegree : MinDegreeAtLeast G 3) :
    IsTwoConnected L.blockGraph :=
  minimal_within_block_two_connected_of_three_le_card
    L₀ L hwithin hminimal
    (L.three_le_card_block hdegree)

/--
The standard two-end-lobe consequence is proved by choosing two components
behind a cut vertex and minimizing a nested lobe region on each side.
-/
theorem two_end_lobes
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hconnected : G.Connected)
    (hnotTwo : ¬ IsTwoConnected G)
    (hdegree : MinDegreeAtLeast G 3) :
    Nonempty (EndLobePair G) := by
  classical
  let x : V := Classical.choice hconnected.nonempty
  have horder : 3 ≤ Fintype.card V := by
    calc
      3 ≤ finiteDegree G x := hdegree x
      _ ≤ (Set.univ : Set V).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
      _ = Fintype.card V := by simp
  obtain ⟨c, C₀, C₁, hC₀C₁⟩ :=
    exists_cut_with_two_components
      G hconnected hnotTwo horder
  let Q₀ := componentVertices G {c} C₀
  let Q₁ := componentVertices G {c} C₁
  obtain ⟨L₀, hL₀inner, hL₀cut⟩ :=
    LobeRegion.exists_ofComponent hconnected c C₀
  obtain ⟨R₀, hR₀inner, hR₀cut⟩ :=
    LobeRegion.exists_ofComponent hconnected c C₁
  obtain ⟨L, hLwithin, hLminimal⟩ :=
    L₀.exists_minimal_within
  obtain ⟨R, hRwithin, hRminimal⟩ :=
    R₀.exists_minimal_within
  have hLtwo : IsTwoConnected L.blockGraph :=
    minimal_within_block_two_connected
      L₀ L hLwithin hLminimal hdegree
  have hRtwo : IsTwoConnected R.blockGraph :=
    minimal_within_block_two_connected
      R₀ R hRwithin hRminimal hdegree
  have hLinnerQ₀ : L.inner ⊆ Q₀ := by
    intro v hv
    simpa [Q₀, hL₀inner] using hLwithin.1 hv
  have hRinnerQ₁ : R.inner ⊆ Q₁ := by
    intro v hv
    simpa [Q₁, hR₀inner] using hRwithin.1 hv
  have hQdisjoint : Disjoint Q₀ Q₁ := by
    exact disjoint_componentVertices G {c} hC₀C₁
  have hinnerDisjoint :
      Disjoint L.inner R.inner := by
    apply Finset.disjoint_left.mpr
    intro v hvL hvR
    exact Finset.disjoint_left.mp hQdisjoint
      (hLinnerQ₀ hvL) (hRinnerQ₁ hvR)
  have hLcutLocation :
      L.cut ∈ insert c Q₀ := by
    simpa [Q₀, hL₀inner, hL₀cut] using hLwithin.2
  have hRcutLocation :
      R.cut ∈ insert c Q₁ := by
    simpa [Q₁, hR₀inner, hR₀cut] using hRwithin.2
  have hcNotQ₀ : c ∉ Q₀ := by
    intro hc
    exact (componentRegion_componentVertices
      G {c} C₀).not_mem_separator hc (by simp)
  have hcNotQ₁ : c ∉ Q₁ := by
    intro hc
    exact (componentRegion_componentVertices
      G {c} C₁).not_mem_separator hc (by simp)
  have hLcutNotRinner : L.cut ∉ R.inner := by
    intro hcutR
    have hcutQ₁ := hRinnerQ₁ hcutR
    rcases Finset.mem_insert.mp hLcutLocation with
        hcutC | hcutQ₀
    · exact hcNotQ₁ (by simpa [hcutC] using hcutQ₁)
    · exact Finset.disjoint_left.mp hQdisjoint
        hcutQ₀ hcutQ₁
  have hRcutNotLinner : R.cut ∉ L.inner := by
    intro hcutL
    have hcutQ₀ := hLinnerQ₀ hcutL
    rcases Finset.mem_insert.mp hRcutLocation with
        hcutC | hcutQ₁
    · exact hcNotQ₀ (by simpa [hcutC] using hcutQ₀)
    · exact Finset.disjoint_left.mp hQdisjoint
        hcutQ₀ hcutQ₁
  obtain ⟨p, hp⟩ :=
    hconnected.exists_isPath L.cut R.cut
  let P : SimplePath G L.cut R.cut :=
    ⟨p, hp⟩
  exact ⟨{
    left := L.toEndLobe hLtwo
    right := R.toEndLobe hRtwo
    inner_disjoint := hinnerDisjoint
    left_cut_not_right_inner := hLcutNotRinner
    right_cut_not_left_inner := hRcutNotLinner
    connector := P
    connector_avoids_left :=
      L.simplePath_from_cut_avoids_inner
        hRcutNotLinner P
    connector_avoids_right :=
      R.simplePath_to_cut_avoids_inner
        hLcutNotRinner P
  }⟩

end ClassicalGraphTheory

end DeanK5
