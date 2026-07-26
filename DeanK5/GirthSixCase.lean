import DeanK5.FourCycleExclusion
import DeanK5.FinalResidue
import DeanK5.ClassicalGraphTheory
import DeanK5.SubdivisionK4
import DeanK5.ThetaResidue
import DeanK5.ThetaCore
import DeanK5.ThetaExistence
import DeanK5.EndLobeComponents

/-!
# The minimum-theta argument (paper Section 7)

This module formalizes the paper's final structural stage.  It first
derives the exact girth and forbidden-length hypotheses required by GHLM,
selects a minimum-order theta without an additional choice axiom, and
normalizes the internally proved theta-residue lemma to the `ZMod 5` form
used by the final arithmetic argument.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {W : Type u} {V : Type v}

/-- Finite vertex-connectivity is invariant under graph isomorphism. -/
theorem isKConnected_of_iso
    [Fintype W] [Fintype V]
    {G : SimpleGraph W} {H : SimpleGraph V}
    (e : G ≃g H) (k : ℕ)
    (hH : IsKConnected H k) :
    IsKConnected G k := by
  classical
  constructor
  · rw [Fintype.card_congr e.toEquiv]
    exact hH.1
  · intro S hS
    let T : Finset V := S.image e
    have hTcard : T.card = S.card := by
      simp [T, Finset.card_image_of_injective _ e.injective]
    have hHT :
        (H.induce {v | v ∉ T}).Connected :=
      hH.2 T (by omega)
    let f :
        G.induce {w | w ∉ S} ≃g
          H.induce {v | v ∉ T} := {
      toFun := fun w => ⟨e w.1, by
        intro heT
        obtain ⟨s, hsS, hse⟩ :=
          Finset.mem_image.mp heT
        exact w.2 (by
          have : s = w.1 :=
            e.injective hse
          simpa [this] using hsS)⟩
      invFun := fun v => ⟨e.symm v.1, by
        intro hsS
        apply v.2
        exact Finset.mem_image.mpr
          ⟨e.symm v.1, hsS, by simp⟩⟩
      left_inv := by
        intro w
        apply Subtype.ext
        simp
      right_inv := by
        intro v
        apply Subtype.ext
        simp
      map_rel_iff' := by
        intro a b
        exact e.map_rel_iff
    }
    exact hHT.map f.symm.toHom f.symm.surjective

@[simp] theorem SimplePath.attachEndpoints_tail_support
    {G : SimpleGraph W} {x x' y' y : W}
    (P : SimplePath G x' y')
    (hxx' : G.Adj x x') (hy'y : G.Adj y' y)
    (hxy : x ≠ y)
    (hx : x ∉ P.walk.support)
    (hy : y ∉ P.walk.support) :
    (P.attachEndpoints hxx' hy'y hxy hx hy).walk.support.tail =
      P.walk.support ++ [y] := by
  simp [SimplePath.attachEndpoints]

/-- Add one new edge at the start of a simple path. -/
def SimplePath.prependEdge
    {G : SimpleGraph W} {x y z : W}
    (P : SimplePath G y z)
    (hxy : G.Adj x y)
    (hx : x ∉ P.walk.support) :
    SimplePath G x z where
  walk := P.walk.cons hxy
  isPath := P.isPath.cons hx

@[simp] theorem SimplePath.prependEdge_length
    {G : SimpleGraph W} {x y z : W}
    (P : SimplePath G y z)
    (hxy : G.Adj x y) (hx) :
    (P.prependEdge hxy hx).length =
      P.length + 1 := by
  simp [SimplePath.prependEdge,
    SimplePath.length]

/-- Add one new edge at the end of a simple path. -/
def SimplePath.appendEdge
    {G : SimpleGraph W} {x y z : W}
    (P : SimplePath G x y)
    (hyz : G.Adj y z)
    (hz : z ∉ P.walk.support) :
    SimplePath G x z where
  walk := P.walk.concat hyz
  isPath := P.isPath.concat hz hyz

@[simp] theorem SimplePath.appendEdge_length
    {G : SimpleGraph W} {x y z : W}
    (P : SimplePath G x y)
    (hyz : G.Adj y z) (hz) :
    (P.appendEdge hyz hz).length =
      P.length + 1 := by
  simp [SimplePath.appendEdge,
    SimplePath.length]

/--
A simple 3-cycle produces the explicit labelled triangle configuration
consumed by Lemma 5.2.
-/
theorem three_cycle_has_triangle
    {J : SimpleGraph W}
    (hcycle : HasCycleLength J 3) :
    Nonempty (TriangleConfig J) := by
  classical
  obtain ⟨C, hClength⟩ := hcycle
  have hcontained :
      cycleGraph 3 ⊑ J :=
    (cycleGraph_isContained_iff (n := 3)
      (by omega)).2
      ⟨C.base, C.walk, C.isCycle, hClength⟩
  obtain ⟨K⟩ := hcontained
  refine ⟨{
    p := K (0 : Fin 3)
    q := K (1 : Fin 3)
    r := K (2 : Fin 3)
    p_ne_q := K.injective.ne (by decide)
    p_ne_r := K.injective.ne (by decide)
    q_ne_r := K.injective.ne (by decide)
    pq := K.toHom.map_adj (by decide)
    qr := K.toHom.map_adj (by decide)
    rp := K.toHom.map_adj (by decide)
  }⟩

/--
Any cycle length divisible by five in `J` would map injectively to such a
cycle in the ambient block `B`.
-/
theorem StandingSetup.no_cycle_length_of_five_dvd
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (n : ℕ) (hdiv : 5 ∣ n) :
    HasNoCycleLength J n := by
  intro C hClength
  apply setup.no_divisible_cycle
  refine ⟨C.mapInjectiveHom setup.inclusion.toHom
    setup.inclusion.injective, ?_⟩
  rw [SimpleCycle.mapInjectiveHom_length,
    hClength, Nat.mod_eq_zero_of_dvd hdiv]

theorem StandingSetup.no_five_cycle
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D) :
    HasNoCycleLength J 5 :=
  setup.no_cycle_length_of_five_dvd 5 (by simp)

theorem StandingSetup.no_ten_cycle
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D) :
    HasNoCycleLength J 10 :=
  setup.no_cycle_length_of_five_dvd 10 (by norm_num)

/-- Equation (6.6): the standing graph has girth at least six. -/
theorem StandingSetup.girth_at_least_six
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D) :
    GirthAtLeast J 6 := by
  intro C
  by_contra hshort
  have hcases :
      C.length = 3 ∨ C.length = 4 ∨
        C.length = 5 := by
    have hthree := C.three_le_length
    omega
  rcases hcases with hthree | hfour | hfive
  · apply setup.no_triangle
    exact three_cycle_has_triangle ⟨C, hthree⟩
  · exact setup.no_four_cycle ⟨C, hfour⟩
  · exact setup.no_five_cycle C hfive

/--
Well-ordering of natural-number vertex counts selects a minimum-order
theta from any nonempty theta family.
-/
theorem exists_minimum_order_theta
    [DecidableEq W]
    {J : SimpleGraph W}
    (hexists : Nonempty (Theta J)) :
    ∃ T : Theta J, T.IsMinimumOrder := by
  classical
  let P : ℕ → Prop :=
    fun n => ∃ T : Theta J, T.verts.card = n
  have hP : ∃ n, P n := by
    obtain ⟨T⟩ := hexists
    exact ⟨T.verts.card, T, rfl⟩
  let n := Nat.find hP
  obtain ⟨T, hTcard⟩ := Nat.find_spec hP
  refine ⟨T, ?_⟩
  intro U
  rw [hTcard]
  exact Nat.find_min' hP ⟨U, rfl⟩

/--
A natural-number residue inequality gives the corresponding inequality of
casts in `ZMod 5` required by Section 7.3.
-/
theorem zmod_five_ne_of_mod_ne
    {a b : ℕ} (h : a % 5 ≠ b % 5) :
    (a : ZMod 5) ≠ (b : ZMod 5) := by
  intro hab
  exact h
    ((ZMod.natCast_eq_natCast_iff' a b 5).1 hab)

/-- The internal theta-residue lemma normalized for the final closure grid. -/
theorem theta_three_distinct_zmod_paths
    [DecidableEq W]
    (J : SimpleGraph W) (hgirth : GirthAtLeast J 6)
    (T : Theta J) :
    ∃ (x y : W), x ≠ y ∧
      ∃ P : Fin 3 → SimplePath J x y,
        (∀ i, T.ContainsPath (P i)) ∧
        (∀ i j, i ≠ j →
          ((P i).length : ZMod 5) ≠
            ((P j).length : ZMod 5)) := by
  obtain ⟨x, y, hxy, P, hcontains,
      hres⟩ :=
    theta_three_distinct_residue_paths_of_girth_six
      J hgirth T
  exact ⟨x, y, hxy, P, hcontains,
    fun i j hij =>
      zmod_five_ne_of_mod_ne (hres i j hij)⟩

namespace Theta

/-- Either root belongs to the vertex set of a theta. -/
theorem x_mem_verts
    [DecidableEq W]
    {J : SimpleGraph W} (T : Theta J) :
    T.x ∈ T.verts := by
  simp only [Theta.verts, Finset.mem_biUnion]
  exact ⟨0, Finset.mem_univ _, by
    simp⟩

/-- Every endpoint of an edge belonging to a theta belongs to its vertex set. -/
theorem fst_mem_verts_of_mem_edges
    [DecidableEq W]
    {J : SimpleGraph W} (T : Theta J)
    {x y : W} (hxy : s(x, y) ∈ T.edges) :
    x ∈ T.verts := by
  simp only [Theta.edges, Finset.mem_biUnion] at hxy
  obtain ⟨i, -, hi⟩ := hxy
  have hxSupport :
      x ∈ (T.path i).walk.support :=
    (T.path i).walk.fst_mem_support_of_mem_edges
      (by simpa using hi)
  simp only [Theta.verts, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, by
    simpa using hxSupport⟩

theorem snd_mem_verts_of_mem_edges
    [DecidableEq W]
    {J : SimpleGraph W} (T : Theta J)
    {x y : W} (hxy : s(x, y) ∈ T.edges) :
    y ∈ T.verts := by
  rw [Sym2.eq_swap] at hxy
  exact T.fst_mem_verts_of_mem_edges hxy

/--
A nontrivial path using only theta edges has all of its support in the
theta vertex set.
-/
theorem support_subset_verts_of_containsPath
    [DecidableEq W]
    {J : SimpleGraph W} (T : Theta J)
    {x y : W} (P : SimplePath J x y)
    (hxy : x ≠ y)
    (hcontains : T.ContainsPath P) :
    ∀ z ∈ P.walk.support, z ∈ T.verts := by
  have hnil : ¬P.walk.Nil := by
    intro hnil
    exact hxy hnil.eq
  intro z hz
  rcases
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges
        (p := P.walk)).1 hz with
    rfl | ⟨e, he, hze⟩
  · have hend :=
      hcontains s(P.walk.penultimate, z)
        (P.walk.mk_penultimate_end_mem_edges hnil)
    exact T.snd_mem_verts_of_mem_edges hend
  · have heT := hcontains e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hzab : z = a ∨ z = b := by
          simpa using hze
        rcases hzab with hza | hzb
        · exact hza ▸
            T.fst_mem_verts_of_mem_edges heT
        · exact hzb ▸
            T.snd_mem_verts_of_mem_edges heT

end Theta

/--
The structural interface `T` obtained from a minimum theta and, when
necessary, the exceptional vertex of GHLM Lemma 5.10.

The later internal proof uses only these explicit consequences; the
construction from the two GHLM lemmas is kept as a separate theorem so the
dependency boundary remains auditable.
-/
structure ThetaEnvelope
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) where
  /-- Vertex set of the structural interface. -/
  carrier : Finset W
  nonempty : carrier.Nonempty
  two_connected :
    IsTwoConnected (J.induce (↑carrier : Set W))
  internal_degree_le_three :
    ∀ v : (↑carrier : Set W),
      finiteDegree (J.induce (↑carrier : Set W)) v ≤ 3
  outside_boundary_degree_le_one :
    ∀ v : W, v ∉ carrier →
      finiteBoundaryDegree J carrier v ≤ 1
  /-- Distinguished theta contained in the interface. -/
  theta : Theta J
  theta_vertices_subset : theta.verts ⊆ carrier

/-- The graph denoted by `M = J - V(T)` in Section 7. -/
abbrev outsideEnvelopeGraph
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (T : ThetaEnvelope J) :=
  deleteVertices J T.carrier

namespace EndLobe

/-- The vertices of an outside end-lobe interior, viewed in the original
carrier of `J`. -/
def ambientInner
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T)) :
    Finset W :=
  L.inner.image Subtype.val

@[simp] theorem mem_ambientInner
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T))
    (w : W) :
    w ∈ L.ambientInner ↔
      ∃ a : {v : W // v ∉ T.carrier},
        a ∈ L.inner ∧ a.1 = w := by
  constructor
  · intro hw
    obtain ⟨a, ha, haw⟩ :=
      Finset.mem_image.mp hw
    exact ⟨a, ha, haw⟩
  · rintro ⟨a, ha, rfl⟩
    exact Finset.mem_image.mpr
      ⟨a, ha, rfl⟩

/-- The distinct interface vertices adjacent to the lobe interior. -/
noncomputable def interfaceBoundary
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T)) :
    Finset W := by
  classical
  exact T.carrier.filter fun y =>
    ∃ a : {v : W // v ∉ T.carrier},
      a ∈ L.inner ∧ J.Adj a.1 y

@[simp] theorem mem_interfaceBoundary
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T))
    (y : W) :
    y ∈ L.interfaceBoundary ↔
      y ∈ T.carrier ∧
        ∃ a : {v : W // v ∉ T.carrier},
          a ∈ L.inner ∧ J.Adj a.1 y := by
  classical
  simp [interfaceBoundary]

/-- The nested induced lobe interior is exactly the induced graph on its
ambient image. -/
noncomputable def ambientInnerIso
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T)) :
    (outsideEnvelopeGraph T).induce
        {a | a ∈ L.inner} ≃g
      J.induce
        (↑(EndLobe.ambientInner L) : Set W) := by
  classical
  let forward :
      {a : {v : W // v ∉ T.carrier} //
        a ∈ L.inner} →
        {w : W //
          w ∈ EndLobe.ambientInner L} :=
    fun a => ⟨a.1.1, by
      exact (L.mem_ambientInner a.1.1).2
        ⟨a.1, a.2, rfl⟩⟩
  let backward :
      {w : W //
        w ∈ EndLobe.ambientInner L} →
        {a : {v : W // v ∉ T.carrier} //
          a ∈ L.inner} :=
    fun w =>
      let hex :=
        (L.mem_ambientInner w.1).1 w.2
      ⟨Classical.choose hex,
        (Classical.choose_spec hex).1⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec
        ((L.mem_ambientInner (forward a).1).1
          (forward a).2)).2
    right_inv := by
      intro w
      apply Subtype.ext
      exact (Classical.choose_spec
        ((L.mem_ambientInner w.1).1 w.2)).2
    map_rel_iff' := by
      intro a b
      rfl
  }

/-- The separator consisting of the lobe cut vertex and all its interface
attachments. -/
noncomputable def ambientSeparator
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T)) :
    Finset W :=
  insert L.cut.1 L.interfaceBoundary

/--
An end-lobe interior is a genuine component region of the ambient graph
after deleting its cut vertex and all of its interface attachments.
-/
theorem ambient_componentRegion
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T)) :
    ComponentRegion J L.ambientSeparator
      L.ambientInner := by
  classical
  refine {
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    closed := ?_
  }
  · obtain ⟨a, ha⟩ := L.inner_nonempty
    exact ⟨a.1, (L.mem_ambientInner a.1).2
      ⟨a, ha, rfl⟩⟩
  · apply Finset.disjoint_left.mpr
    intro w hwInner hwSeparator
    obtain ⟨a, haInner, haw⟩ :=
      (L.mem_ambientInner w).1 hwInner
    have hwCases :
        w = L.cut.1 ∨
          w ∈ L.interfaceBoundary := by
      simpa [ambientSeparator] using hwSeparator
    rcases hwCases with hwCut | hwBoundary
    · apply L.cut_not_inner
      have hacut : a = L.cut := by
        apply Subtype.ext
        exact haw.trans hwCut
      exact hacut ▸ haInner
    · have hwT :=
        (L.mem_interfaceBoundary w).1
          hwBoundary |>.1
      exact a.2 (haw ▸ hwT)
  · exact L.inner_connected.map
      (L.ambientInnerIso).toHom
      (L.ambientInnerIso).surjective
  · intro u v huInner huv hvSeparator
    obtain ⟨a, haInner, hau⟩ :=
      (L.mem_ambientInner u).1 huInner
    by_cases hvT : v ∈ T.carrier
    · have hvBoundary :
          v ∈ L.interfaceBoundary :=
        (L.mem_interfaceBoundary v).2
          ⟨hvT, a, haInner, by
            simpa [hau] using huv⟩
      exact False.elim
        (hvSeparator (by
          simp [ambientSeparator, hvBoundary]))
    · let b : {w : W // w ∉ T.carrier} :=
        ⟨v, hvT⟩
      have hab :
          (outsideEnvelopeGraph T).Adj a b := by
        change J.Adj a.1 b.1
        change J.Adj a.1 v
        rw [hau]
        exact huv
      rcases L.closed haInner hab with
        hbInner | hbCut
      · exact (L.mem_ambientInner v).2
          ⟨b, hbInner, rfl⟩
      · exfalso
        apply hvSeparator
        have hvCut : v = L.cut.1 := by
          simpa [b] using congrArg Subtype.val hbCut
        simp [ambientSeparator, hvCut]

end EndLobe

/--
Four-connectivity forces three distinct interface attachments from an end
lobe whenever there is a surviving outside vertex on the far side.
-/
theorem StandingSetup.three_le_endLobe_interfaceBoundary
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T))
    (z : {v : W // v ∉ T.carrier})
    (hzInner : z ∉ L.inner)
    (hzCut : z ≠ L.cut) :
    3 ≤ L.interfaceBoundary.card := by
  classical
  have hzAmbientInner :
      z.1 ∉ L.ambientInner := by
    intro hz
    obtain ⟨a, haInner, haz⟩ :=
      (L.mem_ambientInner z.1).1 hz
    apply hzInner
    have haz' : a = z := by
      apply Subtype.ext
      exact haz
    exact haz' ▸ haInner
  have hzSeparator :
      z.1 ∉ L.ambientSeparator := by
    intro hz
    have hcases :
        z.1 = L.cut.1 ∨
          z.1 ∈ L.interfaceBoundary := by
      simpa [EndLobe.ambientSeparator] using hz
    rcases hcases with hcut | hboundary
    · exact hzCut (Subtype.ext hcut)
    · have hzT :=
        (L.mem_interfaceBoundary z.1).1
          hboundary |>.1
      exact z.2 hzT
  have hfour :
      4 ≤ L.ambientSeparator.card :=
    (L.ambient_componentRegion).connectivity_le_separator_card
      setup.four_connected hzAmbientInner hzSeparator
  have hupper :
      L.ambientSeparator.card ≤
        L.interfaceBoundary.card + 1 := by
    unfold EndLobe.ambientSeparator
    exact Finset.card_insert_le _ _
  omega

/-- Both end lobes supplied by the block-cut tree have at least three
distinct neighbors in the interface `T`. -/
theorem StandingSetup.endLobePair_three_attachments
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (P : EndLobePair (outsideEnvelopeGraph T)) :
    3 ≤ P.left.interfaceBoundary.card ∧
      3 ≤ P.right.interfaceBoundary.card := by
  obtain ⟨zr, hzr⟩ := P.right.inner_nonempty
  obtain ⟨zl, hzl⟩ := P.left.inner_nonempty
  constructor
  · apply setup.three_le_endLobe_interfaceBoundary
      T P.left zr
    · intro hzrLeft
      exact Finset.disjoint_left.mp
        P.inner_disjoint hzrLeft hzr
    · intro h
      exact P.left_cut_not_right_inner
        (h ▸ hzr)
  · apply setup.three_le_endLobe_interfaceBoundary
      T P.right zl
    · intro hzlRight
      exact Finset.disjoint_left.mp
        P.inner_disjoint hzl hzlRight
    · intro h
      exact P.right_cut_not_left_inner
        (h ▸ hzl)

/-- One certified attachment edge from a lobe interior to the interface. -/
structure EndLobeAttachment
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T)) where
  /-- Interior endpoint of the attachment edge. -/
  innerVertex : ↑L.inner
  /-- Endpoint of the attachment edge on the envelope interface. -/
  interfaceVertex : W
  interface_mem : interfaceVertex ∈ L.interfaceBoundary
  adjacent : J.Adj innerVertex.1.1 interfaceVertex

namespace EndLobe

/-- Vertex set of the end block on the outside carrier. -/
abbrev blockCarrier
    {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph U} (L : EndLobe G) :
    Set U :=
  (↑(insert L.cut L.inner) : Set U)

/-- The induced end block on its cut vertex and interior. -/
abbrev blockGraph
    {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph U} (L : EndLobe G) :=
  G.induce L.blockCarrier

/-- An interior attachment vertex represented on the end-block carrier. -/
def attachmentRoot
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    {L : EndLobe (outsideEnvelopeGraph T)}
    (A : EndLobeAttachment T L) :
    L.blockCarrier :=
  ⟨A.innerVertex.1, by
    exact Finset.mem_insert.mpr
      (Or.inr A.innerVertex.2)⟩

/-- The cut vertex represented on the end-block carrier. -/
def cutRoot
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T)) :
    L.blockCarrier :=
  ⟨L.cut, Finset.mem_insert_self _ _⟩

/-- Deficient non-root vertices of a rooted end block. -/
noncomputable def rootedExceptions
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    {L : EndLobe (outsideEnvelopeGraph T)}
    (D : Finset W) (A : EndLobeAttachment T L) :
    Finset L.blockCarrier := by
  classical
  exact Finset.univ.filter fun z =>
    z.1.1 ∈ D ∧
      z ≠ L.attachmentRoot A ∧
      z ≠ L.cutRoot

@[simp] theorem mem_rootedExceptions
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    {L : EndLobe (outsideEnvelopeGraph T)}
    (D : Finset W) (A : EndLobeAttachment T L)
    (z : L.blockCarrier) :
    z ∈ L.rootedExceptions D A ↔
      z.1.1 ∈ D ∧
        z ≠ L.attachmentRoot A ∧
        z ≠ L.cutRoot := by
  classical
  unfold rootedExceptions
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- All deficient vertices of an end block, including a possible
attachment root or cut root. -/
noncomputable def blockDeficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T))
    (D : Finset W) :
    Finset L.blockCarrier := by
  classical
  exact Finset.univ.filter fun z =>
    z.1.1 ∈ D

@[simp] theorem mem_blockDeficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (L : EndLobe (outsideEnvelopeGraph T))
    (D : Finset W) (z : L.blockCarrier) :
    z ∈ L.blockDeficient D ↔ z.1.1 ∈ D := by
  classical
  unfold blockDeficient
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem rootedExceptions_subset_blockDeficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    {L : EndLobe (outsideEnvelopeGraph T)}
    (D : Finset W) (A : EndLobeAttachment T L) :
    L.rootedExceptions D A ⊆
      L.blockDeficient D := by
  intro z hz
  exact (L.mem_blockDeficient D z).2
    ((L.mem_rootedExceptions D A z).1 hz).1

/-- Inclusion of one end block into the ambient block `B`. -/
def blockHom
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T)) :
    L.blockGraph →g B where
  toFun z := setup.inclusion z.1.1
  map_rel' := by
    intro a b hab
    exact setup.inclusion.toHom.map_rel' hab

theorem blockHom_injective
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T)) :
    Function.Injective (L.blockHom setup T) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact setup.inclusion.injective hab

theorem c_not_range_blockHom
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T)) :
    c ∉ Set.range (L.blockHom setup T) := by
  rintro ⟨z, hz⟩
  apply setup.c_not_old
  refine ⟨z.1.1, ?_⟩
  exact hz

/-- Classify the old vertex represented by the block inclusion. -/
theorem classify_range_blockHom
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T))
    {v : V}
    (hv : v ∈ Set.range (L.blockHom setup T)) :
    v = setup.inclusion L.cut.1 ∨
      ∃ a : {w : W // w ∉ T.carrier},
        a ∈ L.inner ∧
          v = setup.inclusion a.1 := by
  obtain ⟨z, rfl⟩ := hv
  rcases Finset.mem_insert.mp z.2 with
    hzCut | hzInner
  · exact Or.inl (by
      change setup.inclusion z.1.1 =
        setup.inclusion L.cut.1
      exact congrArg
        (fun a => setup.inclusion a.1)
        hzCut)
  · exact Or.inr
      ⟨z.1, hzInner, rfl⟩

end EndLobe

/--
The two end lobes admit attachment edges with distinct endpoints in `T`.
The proof selects the second endpoint from an erased boundary finset, so
the distinctness is a certified choice rather than an informal relabeling.
-/
theorem StandingSetup.exists_distinct_endLobePair_attachments
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (P : EndLobePair (outsideEnvelopeGraph T)) :
    ∃ A₁ : EndLobeAttachment T P.left,
      ∃ A₂ : EndLobeAttachment T P.right,
        A₁.interfaceVertex ≠ A₂.interfaceVertex := by
  classical
  obtain ⟨hleft, hright⟩ :=
    setup.endLobePair_three_attachments T P
  obtain ⟨y₁, hy₁⟩ :=
    Finset.card_pos.mp (by omega :
      0 < P.left.interfaceBoundary.card)
  have hrightErase :
      0 <
        (P.right.interfaceBoundary.erase y₁).card := by
    by_cases hy₁Right :
        y₁ ∈ P.right.interfaceBoundary
    · rw [Finset.card_erase_of_mem hy₁Right]
      omega
    · rw [Finset.erase_eq_of_notMem hy₁Right]
      omega
  obtain ⟨y₂, hy₂Erase⟩ :=
    Finset.card_pos.mp hrightErase
  have hy₂ :=
    Finset.mem_of_mem_erase hy₂Erase
  have hy₁y₂ : y₁ ≠ y₂ := by
    exact fun h =>
      (Finset.mem_erase.mp hy₂Erase).1 h.symm
  obtain ⟨u₁, hu₁Inner, hu₁y₁⟩ :=
    ((P.left.mem_interfaceBoundary y₁).1
      hy₁).2
  obtain ⟨u₂, hu₂Inner, hu₂y₂⟩ :=
    ((P.right.mem_interfaceBoundary y₂).1
      hy₂).2
  let A₁ : EndLobeAttachment T P.left := {
    innerVertex := ⟨u₁, hu₁Inner⟩
    interfaceVertex := y₁
    interface_mem := hy₁
    adjacent := hu₁y₁
  }
  let A₂ : EndLobeAttachment T P.right := {
    innerVertex := ⟨u₂, hu₂Inner⟩
    interfaceVertex := y₂
    interface_mem := hy₂
    adjacent := hu₂y₂
  }
  exact ⟨A₁, A₂, hy₁y₂⟩

/--
When the carrier is split into `T` and its complement, ambient degree is
at most internal complement degree plus the exact number of neighbors in
`T`.
-/
theorem finiteDegree_le_outside_add_boundary
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (T : Finset W)
    (w : {v : W // v ∉ T}) :
    finiteDegree J w.1 ≤
      finiteDegree (deleteVertices J T) w +
        finiteBoundaryDegree J T w.1 := by
  let NM : Set W :=
    Subtype.val ''
      (deleteVertices J T).neighborSet w
  let NT : Set W :=
    J.neighborSet w.1 ∩ (↑T : Set W)
  have hsub :
      J.neighborSet w.1 ⊆ NM ∪ NT := by
    intro z hwz
    by_cases hzT : z ∈ T
    · exact Or.inr ⟨hwz, hzT⟩
    · exact Or.inl
        ⟨⟨z, hzT⟩, hwz, rfl⟩
  unfold finiteDegree finiteBoundaryDegree
  calc
    (J.neighborSet w.1).ncard
        ≤ (NM ∪ NT).ncard :=
      Set.ncard_le_ncard hsub
    _ ≤ NM.ncard + NT.ncard :=
      Set.ncard_union_le NM NT
    _ =
        ((deleteVertices J T).neighborSet w).ncard +
          (J.neighborSet w.1 ∩
            (↑T : Set W)).ncard := by
      rw [Set.ncard_image_of_injective _
        Subtype.val_injective]

/--
Equation (7.2), with the deficient and regular cases stated separately.
-/
theorem StandingSetup.outside_envelope_degree_bounds
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (w : {v : W // v ∉ T.carrier}) :
    (w.1 ∉ D →
      4 ≤ finiteDegree (outsideEnvelopeGraph T) w) ∧
    (w.1 ∈ D →
      3 ≤ finiteDegree (outsideEnvelopeGraph T) w) := by
  have hambient :=
    finiteDegree_le_outside_add_boundary
      J T.carrier w
  have hboundary :=
    T.outside_boundary_degree_le_one w.1 w.2
  constructor
  · intro hwD
    change
      4 ≤ finiteDegree
        (deleteVertices J T.carrier) w
    have hregular := setup.degree_regular w.1 hwD
    omega
  · intro hwD
    change
      3 ≤ finiteDegree
        (deleteVertices J T.carrier) w
    have hdeficient :=
      setup.degree_deficient w.1 hwD
    omega

/--
Lemma 3.3 on one rooted end block.  The exception set is exactly the
deficient non-root vertices.  When it has size at most one, the mapped
family is certified to avoid `c`, which is the paper's light-block
case.
-/
theorem StandingSetup.endLobe_admissible_paths
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T))
    (A : EndLobeAttachment T L) :
    AmbientRootLiftResult B c
      (setup.inclusion A.innerVertex.1.1)
      (setup.inclusion L.cut.1) 3
      (Set.range (L.blockHom setup T))
      ((L.rootedExceptions D A).card < 2) := by
  classical
  let E := L.blockGraph
  let x := L.attachmentRoot A
  let y := L.cutRoot
  let Z := L.rootedExceptions D A
  let G := E \ edge x y
  have hxy : x ≠ y := by
    intro h
    have hval :
        A.innerVertex.1 = L.cut :=
      congrArg Subtype.val h
    exact L.cut_not_inner
      (hval ▸ A.innerVertex.2)
  have hEle : E ≤ G ⊔ edge x y := by
    intro p q hpq
    by_cases hedge : (edge x y).Adj p q
    · exact Or.inr hedge
    · exact Or.inl ⟨hpq, hedge⟩
  have hconn :
      IsTwoConnected (G ⊔ edge x y) := by
    refine ⟨L.block_two_connected.1, ?_⟩
    intro S hS
    apply (L.block_two_connected.2 S hS).mono
    intro p q hpq
    exact hEle hpq
  have hnotadj : ¬G.Adj x y := by
    rintro ⟨-, hnotEdge⟩
    apply hnotEdge
    exact (SimpleGraph.edge_adj x y x y).2
      ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
  have hxZ : x ∉ Z := by
    intro hx
    have hxData :=
      (L.mem_rootedExceptions D A x).1 hx
    exact hxData.2.1 (by rfl)
  have hyZ : y ∉ Z := by
    intro hy
    have hyData :=
      (L.mem_rootedExceptions D A y).1 hy
    exact hyData.2.2 (by rfl)
  have hinner :
      ∀ z : L.blockCarrier,
        z ≠ y → z.1 ∈ L.inner := by
    intro z hzy
    have hz :
        z.1 = L.cut ∨ z.1 ∈ L.inner :=
      Finset.mem_insert.mp z.2
    rcases hz with hzcut | hzinner
    · exfalso
      apply hzy
      apply Subtype.ext
      exact hzcut
    · exact hzinner
  have hMEdegree :
      ∀ z : L.blockCarrier, z ≠ y →
        finiteDegree (outsideEnvelopeGraph T) z.1 ≤
          finiteDegree E z := by
    intro z hzy
    have hzInner := hinner z hzy
    apply finiteDegree_le_induce
      (outsideEnvelopeGraph T)
      L.blockCarrier z
    intro w hzw
    rcases L.closed hzInner hzw with
      hwInner | hwCut
    · exact Finset.mem_insert.mpr
        (Or.inr hwInner)
    · exact Finset.mem_insert.mpr
        (Or.inl hwCut)
  have hdeg :
      ∀ z, z ≠ x → z ≠ y → z ∉ Z →
        4 ≤ finiteDegree G z := by
    intro z hzx hzy hzZ
    have hzNotD : z.1.1 ∉ D := by
      intro hzD
      apply hzZ
      exact (L.mem_rootedExceptions D A z).2
        ⟨hzD, hzx, hzy⟩
    have hMlower :=
      (setup.outside_envelope_degree_bounds
        T z.1).1 hzNotD
    have hEbound := hMEdegree z hzy
    rw [finiteDegree_sdiff_edge_of_ne
      E x y z hzx hzy]
    exact hMlower.trans hEbound
  have hdegZ :
      ∀ z ∈ Z, 3 ≤ finiteDegree G z := by
    intro z hzZ
    have hzData :=
      (L.mem_rootedExceptions D A z).1 hzZ
    have hMlower :=
      (setup.outside_envelope_degree_bounds
        T z.1).2 hzData.1
    have hEbound :=
      hMEdegree z hzData.2.2
    rw [finiteDegree_sdiff_edge_of_ne
      E x y z hzData.2.1 hzData.2.2]
    exact hMlower.trans hEbound
  have horder :
      4 ≤ Fintype.card L.blockCarrier := by
    obtain ⟨a, haInner⟩ := L.inner_nonempty
    let aE : L.blockCarrier :=
      ⟨a, Finset.mem_insert.mpr
        (Or.inr haInner)⟩
    have haCut : aE ≠ y := by
      intro h
      have hval : a = L.cut :=
        congrArg Subtype.val h
      exact L.cut_not_inner (hval ▸ haInner)
    have hMlower :
        3 ≤ finiteDegree
          (outsideEnvelopeGraph T) a := by
      by_cases haD : a.1 ∈ D
      · exact
          (setup.outside_envelope_degree_bounds
            T a).2 haD
      · exact
          ((setup.outside_envelope_degree_bounds
            T a).1 haD).trans' (by omega)
    have hEbound := hMEdegree aE haCut
    have hfiniteEq :
        finiteDegree E aE = E.degree aE := by
      unfold finiteDegree SimpleGraph.degree
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hdegreeCard := E.degree_lt_card_verts aE
    have hMlower' :
        3 ≤ finiteDegree
          (outsideEnvelopeGraph T) aE.1 := by
      simpa [aE] using hMlower
    have hElower :
        3 ≤ finiteDegree E aE :=
      hMlower'.trans hEbound
    rw [← hfiniteEq] at hdegreeCard
    rw [hfiniteEq] at hElower
    omega
  have result : RootLiftResult G Z x y 3 := by
    apply root_lifting 3 G Z Z x y
    · omega
    · exact hxy
    · exact hnotadj
    · exact hconn
    · exact Finset.Subset.rfl
    · exact hxZ
    · exact hyZ
    · exact hdeg
    · exact hdegZ
    · intro _
      exact horder
  let f : G →g B := {
    toFun := fun z => setup.inclusion z.1.1
    map_rel' := by
      intro p q hpq
      exact setup.inclusion.toHom.map_rel' hpq.1
  }
  have mapped :=
    result.mapToAmbient f c
      (fun z hz =>
        setup.deficient_adjacent_to_c z.1.1
          ((L.mem_rootedExceptions
            D A z).1 hz |>.1))
      (by
        intro p q hpq
        apply Subtype.ext
        apply Subtype.ext
        exact setup.inclusion.injective hpq)
      (by
        rintro ⟨z, hz⟩
        apply setup.c_not_old
        exact ⟨z.1.1, by
          exact hz⟩)
  convert mapped using 1 <;>
    simp [f, G, E, x, y,
      EndLobe.blockHom] <;>
    rfl

/--
The heavy end-block construction.  The fresh root is joined to every
deficient block vertex (not merely to the light-case exception set), so
each deficient non-root recovers the one degree needed by the GHLM rooted
theorem.  The output is a `c`--cut-vertex family.
-/
theorem StandingSetup.heavy_endLobe_admissible_paths
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (L : EndLobe (outsideEnvelopeGraph T))
    (A : EndLobeAttachment T L)
    (hheavy : 2 ≤ (L.rootedExceptions D A).card) :
    AmbientRootLiftResult B c c
      (setup.inclusion L.cut.1) 3
      (Set.range (L.blockHom setup T)) False := by
  classical
  let E := L.blockGraph
  let DZ := L.blockDeficient D
  let y := L.cutRoot
  let K := adjoinRoot E DZ
  let rC : Option L.blockCarrier := none
  let rB : Option L.blockCarrier := some y
  let G := K \ edge rC rB
  have hDZcard : 2 ≤ DZ.card := by
    have hsub :=
      L.rootedExceptions_subset_blockDeficient
        D A
    exact hheavy.trans
      (Finset.card_le_card hsub)
  have hKtwo : IsTwoConnected K := by
    exact isTwoConnected_adjoinRoot E DZ
      L.block_two_connected hDZcard
  have hrne : rC ≠ rB := by simp [rC, rB]
  have hKle : K ≤ G ⊔ edge rC rB := by
    intro p q hpq
    by_cases hedge : (edge rC rB).Adj p q
    · exact Or.inr hedge
    · exact Or.inl ⟨hpq, hedge⟩
  have hconn :
      IsTwoConnected (G ⊔ edge rC rB) := by
    refine ⟨hKtwo.1, ?_⟩
    intro S hS
    apply (hKtwo.2 S hS).mono
    intro p q hpq
    exact hKle hpq
  have hinner :
      ∀ z : L.blockCarrier,
        z ≠ y → z.1 ∈ L.inner := by
    intro z hzy
    rcases Finset.mem_insert.mp z.2 with
      hzCut | hzInner
    · exfalso
      apply hzy
      apply Subtype.ext
      exact hzCut
    · exact hzInner
  have hMEdegree :
      ∀ z : L.blockCarrier, z ≠ y →
        finiteDegree (outsideEnvelopeGraph T) z.1 ≤
          finiteDegree E z := by
    intro z hzy
    have hzInner := hinner z hzy
    apply finiteDegree_le_induce
      (outsideEnvelopeGraph T)
      L.blockCarrier z
    intro w hzw
    rcases L.closed hzInner hzw with
      hwInner | hwCut
    · exact Finset.mem_insert.mpr
        (Or.inr hwInner)
    · exact Finset.mem_insert.mpr
        (Or.inl hwCut)
  have hdeg :
      ∀ v, v ≠ rC → v ≠ rB →
        4 ≤ finiteDegree G v := by
    intro v hvC hvB
    cases v with
    | none =>
        exact False.elim (hvC rfl)
    | some z =>
        have hzy : z ≠ y := by
          intro h
          exact hvB (by simp [rB, h])
        have hEbound := hMEdegree z hzy
        have hvC' :
            (some z : Option L.blockCarrier) ≠ rC := by
          simp [rC]
        have hvB' :
            (some z : Option L.blockCarrier) ≠ rB := by
          simpa [rB] using hzy
        rw [finiteDegree_sdiff_edge_of_ne
          K rC rB (some z) hvC' hvB']
        rw [finiteDegree_adjoinRoot_some]
        by_cases hzDZ : z ∈ DZ
        · have hzD :=
            (L.mem_blockDeficient D z).1 hzDZ
          have hMlower :=
            (setup.outside_envelope_degree_bounds
              T z.1).2 hzD
          have hElower :
              3 ≤ finiteDegree E z :=
            hMlower.trans hEbound
          simp [hzDZ]
          omega
        · have hzNotD : z.1.1 ∉ D := by
            intro hzD
            exact hzDZ
              ((L.mem_blockDeficient D z).2
                hzD)
          have hMlower :=
            (setup.outside_envelope_degree_bounds
              T z.1).1 hzNotD
          have hElower :
              4 ≤ finiteDegree E z :=
            hMlower.trans hEbound
          simp [hzDZ]
          exact hElower
  obtain ⟨F⟩ :=
    GHLM.rooted_admissible_paths
      3 G rC rB (by omega) hrne hconn hdeg
  let φ : K →g B :=
    adjoinRootHom E DZ
      (L.blockHom setup T) c
      (fun z hz =>
        setup.deficient_adjacent_to_c z.1.1
          ((L.mem_blockDeficient D z).1 hz))
  have hφ :
      Function.Injective φ :=
    adjoinRootHom_injective E DZ
      (L.blockHom setup T) c
      (fun z hz =>
        setup.deficient_adjacent_to_c z.1.1
          ((L.mem_blockDeficient D z).1 hz))
      (L.blockHom_injective setup T)
      (L.c_not_range_blockHom setup T)
  let f : G →g B := {
    toFun := φ
    map_rel' := by
      intro p q hpq
      exact φ.map_rel' hpq.1
  }
  have hf : Function.Injective f := hφ
  let F' := F.mapInjectiveHom f hf
  refine ⟨F', ?_⟩
  constructor
  · intro i v hv
    have hv' := hv
    change v ∈
      ((F.path i).walk.map f).support at hv'
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨w, -, rfl⟩ :=
      List.mem_map.mp hv'
    cases w with
    | none =>
        exact Or.inl (by rfl)
    | some z =>
        exact Or.inr ⟨z, by
          rfl⟩
  · intro hfalse
    exact False.elim hfalse

/--
The light/mixed part of Lemma 7.1.  The two rooted families are framed by
the attachment edges, the end-lobe connector, and one path through `T`.
Every append below is a `SimplePath` append with an explicit support
disjointness proof; the resulting grid therefore contains simple cycles,
not merely closed walks.
-/
theorem StandingSetup.endLobePair_contradiction_of_light
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (P : EndLobePair (outsideEnvelopeGraph T))
    (A₁ : EndLobeAttachment T P.left)
    (A₂ : EndLobeAttachment T P.right)
    (hyne :
      A₁.interfaceVertex ≠ A₂.interfaceVertex)
    (hlight :
      (P.left.rootedExceptions D A₁).card < 2 ∨
      (P.right.rootedExceptions D A₂).card < 2) :
    False := by
  classical
  obtain ⟨F₁, hF₁support, hF₁avoid⟩ :=
    setup.endLobe_admissible_paths T P.left A₁
  obtain ⟨F₂, hF₂support, hF₂avoid⟩ :=
    setup.endLobe_admissible_paths T P.right A₂
  let fM : outsideEnvelopeGraph T →g B := {
    toFun := fun z => setup.inclusion z.1
    map_rel' := by
      intro a b hab
      exact setup.inclusion.toHom.map_rel' hab
  }
  have hfM : Function.Injective fM := by
    intro a b hab
    apply Subtype.ext
    exact setup.inclusion.injective hab
  let R : SimplePath B
      (setup.inclusion P.left.cut.1)
      (setup.inclusion P.right.cut.1) :=
    P.connector.mapInjectiveHom fM
      hfM
  have hy₁T :
      A₁.interfaceVertex ∈ T.carrier :=
    (P.left.mem_interfaceBoundary
      A₁.interfaceVertex).1 A₁.interface_mem |>.1
  have hy₂T :
      A₂.interfaceVertex ∈ T.carrier :=
    (P.right.mem_interfaceBoundary
      A₂.interfaceVertex).1 A₂.interface_mem |>.1
  let y₁T : (↑T.carrier : Set W) :=
    ⟨A₁.interfaceVertex, hy₁T⟩
  let y₂T : (↑T.carrier : Set W) :=
    ⟨A₂.interfaceVertex, hy₂T⟩
  have hTconnected :
      (J.induce (↑T.carrier : Set W)).Connected :=
    by
      have hdeleted :=
        T.two_connected.2 ∅ (by simp)
      exact hdeleted.map
        (SimpleGraph.Embedding.induce
          {v : (↑T.carrier : Set W) |
            v ∉ (∅ : Finset (↑T.carrier : Set W))}).toHom
        (by
          intro v
          exact ⟨⟨v, by simp⟩, rfl⟩)
  obtain ⟨Qwalk, hQwalk⟩ :=
    hTconnected.exists_isPath y₁T y₂T
  let QJ : SimplePath
      (J.induce (↑T.carrier : Set W))
      y₁T y₂T :=
    ⟨Qwalk, hQwalk⟩
  let fT :
      J.induce (↑T.carrier : Set W) →g B := {
    toFun := fun z => setup.inclusion z.1
    map_rel' := by
      intro a b hab
      exact setup.inclusion.toHom.map_rel' hab
  }
  have hfT : Function.Injective fT := by
    intro a b hab
    apply Subtype.ext
    exact setup.inclusion.injective hab
  let Q : SimplePath B
      (setup.inclusion A₁.interfaceVertex)
      (setup.inclusion A₂.interfaceVertex) :=
    QJ.mapInjectiveHom fT hfT
  have hRsupport :
      ∀ z ∈ R.walk.support,
        ∃ r,
          r ∈ P.connector.walk.support ∧
          z = setup.inclusion r.1 := by
    intro z hz
    change z ∈
      (P.connector.walk.map fM).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨r, hr, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨r, hr, rfl⟩
  have hQsupport :
      ∀ z ∈ Q.walk.support,
        ∃ q : (↑T.carrier : Set W),
          z = setup.inclusion q.1 := by
    intro z hz
    change z ∈ (QJ.walk.map fT).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨q, -, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨q, rfl⟩
  have hF₁class :
      ∀ i z, z ∈ (F₁.path i).walk.support →
        z = c ∨
          ∃ m : {w : W // w ∉ T.carrier},
            z = setup.inclusion m.1 := by
    intro i z hz
    rcases hF₁support i z hz with
      rfl | ⟨a, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a.1, rfl⟩
  have hF₂class :
      ∀ i z, z ∈ (F₂.path i).walk.support →
        z = c ∨
          ∃ m : {w : W // w ∉ T.carrier},
            z = setup.inclusion m.1 := by
    intro i z hz
    rcases hF₂support i z hz with
      rfl | ⟨a, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a.1, rfl⟩
  have hy₁F₁ :
      ∀ i, setup.inclusion A₁.interfaceVertex ∉
        (F₁.path i).walk.support := by
    intro i hz
    rcases hF₁class i _ hz with hc | ⟨m, hm⟩
    · exact setup.c_not_old
        ⟨A₁.interfaceVertex, hc⟩
    · have heq :
          A₁.interfaceVertex = m.1 :=
        setup.inclusion.injective hm
      exact m.2 (heq ▸ hy₁T)
  have hy₂F₂ :
      ∀ i, setup.inclusion A₂.interfaceVertex ∉
        (F₂.path i).walk.support := by
    intro i hz
    rcases hF₂class i _ hz with hc | ⟨m, hm⟩
    · exact setup.c_not_old
        ⟨A₂.interfaceVertex, hc⟩
    · have heq :
          A₂.interfaceVertex = m.1 :=
        setup.inclusion.injective hm
      exact m.2 (heq ▸ hy₂T)
  have hblockIntersection :
      ∀ {z : V},
        z ∈ Set.range (P.left.blockHom setup T) →
        z ∈ Set.range (P.right.blockHom setup T) →
        z = setup.inclusion P.left.cut.1 ∧
          z = setup.inclusion P.right.cut.1 := by
    intro z hz₁ hz₂
    rcases P.left.classify_range_blockHom
        setup T hz₁ with hzCut₁ | ⟨a, ha, hza⟩
    · rcases P.right.classify_range_blockHom
          setup T hz₂ with hzCut₂ | ⟨b, hb, hzb⟩
      · exact ⟨hzCut₁, hzCut₂⟩
      · have hval :
            P.left.cut = b := by
          apply Subtype.ext
          exact setup.inclusion.injective
            (hzCut₁.symm.trans hzb)
        exact False.elim
          (P.left_cut_not_right_inner
            (hval ▸ hb))
    · rcases P.right.classify_range_blockHom
          setup T hz₂ with hzCut₂ | ⟨b, hb, hzb⟩
      · have hval :
            a = P.right.cut := by
          apply Subtype.ext
          exact setup.inclusion.injective
            (hza.symm.trans hzCut₂)
        exact False.elim
          (P.right_cut_not_left_inner
            (hval ▸ ha))
      · have hab : a = b := by
          apply Subtype.ext
          exact setup.inclusion.injective
            (hza.symm.trans hzb)
        exact False.elim
          (Finset.disjoint_left.mp
            P.inner_disjoint ha (hab ▸ hb))
  have hAdj₁ :
      B.Adj
        (setup.inclusion A₁.interfaceVertex)
        (setup.inclusion A₁.innerVertex.1.1) :=
    (setup.inclusion.toHom.map_rel'
      A₁.adjacent).symm
  have hAdj₂ :
      B.Adj
        (setup.inclusion A₂.innerVertex.1.1)
        (setup.inclusion A₂.interfaceVertex) :=
    setup.inclusion.toHom.map_rel'
      A₂.adjacent
  let P₁ : Fin 3 → SimplePath B
      (setup.inclusion A₁.interfaceVertex)
      (setup.inclusion P.left.cut.1) :=
    fun i => (F₁.path i).prependEdge
      hAdj₁ (hy₁F₁ i)
  have hP₁class :
      ∀ i z, z ∈ (P₁ i).walk.support →
        z = setup.inclusion A₁.interfaceVertex ∨
        z = c ∨
          ∃ m : {w : W // w ∉ T.carrier},
            z = setup.inclusion m.1 := by
    intro i z hz
    change z ∈
      ((F₁.path i).walk.cons hAdj₁).support at hz
    simp only [SimpleGraph.Walk.support_cons,
      List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · rcases hF₁class i z hz with hc | hm
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hm)
  have hP₁Rdisjoint :
      ∀ i,
        (P₁ i).walk.support.Disjoint
          R.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro z hzP hzR
    obtain ⟨r, hrSupport, hzr⟩ :=
      hRsupport z (List.mem_of_mem_tail hzR)
    rcases hP₁class i z hzP with
      hy₁ | hc | ⟨m, hm⟩
    · have hyr :
          A₁.interfaceVertex = r.1 :=
        setup.inclusion.injective
          (hy₁.symm.trans hzr)
      exact r.2 (hyr ▸ hy₁T)
    · exact setup.c_not_old
        ⟨r.1, hzr.symm.trans hc⟩
    · have hmr : m = r := by
        apply Subtype.ext
        exact setup.inclusion.injective
          (hm.symm.trans hzr)
      have hmSupport :
          m ∈ P.connector.walk.support :=
        hmr ▸ hrSupport
      have hmNotInner :=
        P.connector_avoids_left m hmSupport
      by_cases hmCut : m = P.left.cut
      · have hzStart :
            z =
              setup.inclusion P.left.cut.1 := by
          simpa [R, fM, hmCut] using hm
        exact R.start_not_mem_tail
          (hzStart ▸ hzR)
      · have hmCarrier :
            m ∈ insert P.left.cut
              P.left.inner := by
          have hzF :
              z ∈ (F₁.path i).walk.support := by
            change z ∈
              ((F₁.path i).walk.cons hAdj₁).support
                at hzP
            simp only [SimpleGraph.Walk.support_cons,
              List.mem_cons] at hzP
            rcases hzP with hzY | hzF
            · have hym :
                  A₁.interfaceVertex = m.1 :=
                setup.inclusion.injective
                  (hzY.symm.trans hm)
              exact False.elim
                (m.2 (hym ▸ hy₁T))
            · exact hzF
          have hzRange :
              z ∈ Set.range
                (P.left.blockHom setup T) := by
            rcases hF₁support i z hzF with
              hzc | hzRange
            · exact False.elim
                (setup.c_not_old
                  ⟨m.1, hm.symm.trans hzc⟩)
            · exact hzRange
          obtain ⟨a, ha⟩ := hzRange
          have ham : a.1 = m := by
            apply Subtype.ext
            exact setup.inclusion.injective
              (ha.trans hm)
          exact ham ▸ a.2
        exact hmNotInner
          ((Finset.mem_insert.mp hmCarrier).resolve_left
            (fun h => hmCut h))
  let P₂ : Fin 3 → SimplePath B
      (setup.inclusion A₁.interfaceVertex)
      (setup.inclusion P.right.cut.1) :=
    fun i => (P₁ i).appendDisjoint R
      (hP₁Rdisjoint i)
  have hP₂class :
      ∀ i z, z ∈ (P₂ i).walk.support →
        z = setup.inclusion A₁.interfaceVertex ∨
        z = c ∨
          ∃ m : {w : W // w ∉ T.carrier},
            z = setup.inclusion m.1 := by
    intro i z hz
    change z ∈
      ((P₁ i).walk.append R.walk).support at hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzP | hzR
    · exact hP₁class i z hzP
    · obtain ⟨r, -, hzr⟩ :=
        hRsupport z (List.mem_of_mem_tail hzR)
      exact Or.inr (Or.inr ⟨r, hzr⟩)
  have hP₂F₂disjoint :
      ∀ i j,
        (P₂ i).walk.support.Disjoint
          (F₂.path j).reverse.walk.support.tail := by
    intro i j
    apply List.disjoint_left.mpr
    intro z hzP hzF₂rev
    have hzF₂support :
        z ∈ (F₂.path j).walk.support := by
      have hz :
          z ∈ (F₂.path j).reverse.walk.support :=
        List.mem_of_mem_tail hzF₂rev
      simpa [SimplePath.reverse] using hz
    rcases hF₂support j z hzF₂support with
      hc | hzBlock₂
    · rcases hlight with hleft | hright
      · have hcNotP : c ∉ (P₂ i).walk.support := by
          intro hcP
          change c ∈
            ((P₁ i).walk.append R.walk).support
              at hcP
          rw [SimpleGraph.Walk.support_append]
            at hcP
          rcases List.mem_append.mp hcP with
            hcP₁ | hcR
          · change c ∈
              ((F₁.path i).walk.cons hAdj₁).support
                at hcP₁
            simp only [SimpleGraph.Walk.support_cons,
              List.mem_cons] at hcP₁
            rcases hcP₁ with hcY | hcF
            · exact setup.c_not_old
                ⟨A₁.interfaceVertex, hcY.symm⟩
            · exact hF₁avoid hleft i hcF
          · obtain ⟨r, -, hcr⟩ :=
              hRsupport c
                (List.mem_of_mem_tail hcR)
            exact setup.c_not_old
              ⟨r.1, hcr.symm⟩
        exact hcNotP (hc ▸ hzP)
      · exact hF₂avoid hright j
          (hc ▸ hzF₂support)
    · rcases hP₂class i z hzP with
        hy₁ | hc | ⟨m, hm⟩
      · obtain ⟨b, hb⟩ := hzBlock₂
        have hyb :
            A₁.interfaceVertex = b.1.1 :=
          setup.inclusion.injective
            (hy₁.symm.trans hb.symm)
        exact b.1.2 (hyb ▸ hy₁T)
      · exact P.right.c_not_range_blockHom
          setup T (hc ▸ hzBlock₂)
      · change z ∈
          ((P₁ i).walk.append R.walk).support
            at hzP
        rw [SimpleGraph.Walk.support_append]
          at hzP
        rcases List.mem_append.mp hzP with
          hzP₁ | hzR
        · change z ∈
            ((F₁.path i).walk.cons hAdj₁).support
              at hzP₁
          simp only [SimpleGraph.Walk.support_cons,
            List.mem_cons] at hzP₁
          rcases hzP₁ with hzY | hzF₁
          · obtain ⟨b, hb⟩ := hzBlock₂
            have hyb :
                A₁.interfaceVertex = b.1.1 :=
              setup.inclusion.injective
                (hzY.symm.trans hb.symm)
            exact b.1.2 (hyb ▸ hy₁T)
          · rcases hF₁support i z hzF₁ with
              hzc | hzBlock₁
            · exact P.right.c_not_range_blockHom
                setup T (hzc ▸ hzBlock₂)
            · obtain ⟨hzCut₁, hzCut₂⟩ :=
                hblockIntersection hzBlock₁
                  hzBlock₂
              have hzStart :
                  z =
                    setup.inclusion P.right.cut.1 := by
                simpa [SimplePath.reverse] using
                  hzCut₂
              exact
                (F₂.path j).reverse.start_not_mem_tail
                  (hzStart ▸ hzF₂rev)
        · obtain ⟨r, hr, hzr⟩ :=
            hRsupport z
              (List.mem_of_mem_tail hzR)
          rcases P.right.classify_range_blockHom
              setup T hzBlock₂ with
            hzCut | ⟨b, hbInner, hzb⟩
          · have hzStart :
                z =
                  setup.inclusion P.right.cut.1 := by
              simpa [SimplePath.reverse] using hzCut
            exact
              (F₂.path j).reverse.start_not_mem_tail
                (hzStart ▸ hzF₂rev)
          · have hrb : r = b := by
              apply Subtype.ext
              exact setup.inclusion.injective
                (hzr.symm.trans hzb)
            exact P.connector_avoids_right b
              (hrb ▸ hr) hbInner
  let P₃ : Fin 3 → Fin 3 → SimplePath B
      (setup.inclusion A₁.interfaceVertex)
      (setup.inclusion A₂.innerVertex.1.1) :=
    fun i j => (P₂ i).appendDisjoint
      (F₂.path j).reverse
      (hP₂F₂disjoint i j)
  have hP₃class :
      ∀ i j z, z ∈ (P₃ i j).walk.support →
        z = setup.inclusion A₁.interfaceVertex ∨
        z = c ∨
          ∃ m : {w : W // w ∉ T.carrier},
            z = setup.inclusion m.1 := by
    intro i j z hz
    change z ∈
      ((P₂ i).walk.append
        (F₂.path j).reverse.walk).support at hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzP | hzF
    · exact hP₂class i z hzP
    · have hzSupport :
          z ∈ (F₂.path j).walk.support := by
        have hzRev :
            z ∈ (F₂.path j).reverse.walk.support :=
          List.mem_of_mem_tail hzF
        simpa [SimplePath.reverse] using hzRev
      rcases hF₂class j z hzSupport with hc | hm
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hm)
  have hy₂P₃ :
      ∀ i j,
        setup.inclusion A₂.interfaceVertex ∉
          (P₃ i j).walk.support := by
    intro i j hz
    rcases hP₃class i j _ hz with
      hy₁ | hc | ⟨m, hm⟩
    · exact hyne
        (setup.inclusion.injective
          (hy₁.symm))
    · exact setup.c_not_old
        ⟨A₂.interfaceVertex, hc⟩
    · have heq :
          A₂.interfaceVertex = m.1 :=
        setup.inclusion.injective hm
      exact m.2 (heq ▸ hy₂T)
  let side : Fin 3 → Fin 3 → SimplePath B
      (setup.inclusion A₁.interfaceVertex)
      (setup.inclusion A₂.interfaceVertex) :=
    fun i j => (P₃ i j).appendEdge hAdj₂
      (hy₂P₃ i j)
  have hsideClass :
      ∀ i j z, z ∈ (side i j).walk.support →
        z = setup.inclusion A₁.interfaceVertex ∨
        z = setup.inclusion A₂.interfaceVertex ∨
        z = c ∨
          ∃ m : {w : W // w ∉ T.carrier},
            z = setup.inclusion m.1 := by
    intro i j z hz
    change z ∈
      ((P₃ i j).walk.concat hAdj₂).support at hz
    simp only [SimpleGraph.Walk.support_concat,
      List.mem_append, List.mem_singleton] at hz
    rcases hz with hzP | rfl
    · rcases hP₃class i j z hzP with
        hy₁ | hc | hm
      · exact Or.inl hy₁
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hm))
    · exact Or.inr (Or.inl rfl)
  let returnPath := Q.reverse
  have hsideReturnDisjoint :
      ∀ i j,
        (side i j).walk.support.tail.Disjoint
          returnPath.walk.support.tail := by
    intro i j
    apply List.disjoint_left.mpr
    intro z hzSide hzReturn
    have hzSideSupport :=
      List.mem_of_mem_tail hzSide
    have hzQSupport :
        z ∈ Q.walk.support := by
      have hzReturnSupport :
          z ∈ returnPath.walk.support :=
        List.mem_of_mem_tail hzReturn
      simpa [returnPath, SimplePath.reverse]
        using hzReturnSupport
    obtain ⟨q, hzq⟩ :=
      hQsupport z hzQSupport
    rcases hsideClass i j z hzSideSupport with
      hy₁ | hy₂ | hc | ⟨m, hm⟩
    · have hzStart :
          z =
            setup.inclusion A₁.interfaceVertex := by
        simpa [side] using hy₁
      exact (side i j).start_not_mem_tail
        (hzStart ▸ hzSide)
    · have hzStart :
          z =
            setup.inclusion A₂.interfaceVertex := by
        simpa [returnPath, Q,
          SimplePath.reverse] using hy₂
      exact returnPath.start_not_mem_tail
        (hzStart ▸ hzReturn)
    · exact setup.c_not_old
        ⟨q.1, hzq.symm.trans hc⟩
    · have hmq : m.1 = q.1 :=
        setup.inclusion.injective
          (hm.symm.trans hzq)
      exact m.2 (hmq ▸ q.2)
  have hsideLength :
      ∀ i j,
        (side i j).length =
          (F₁.path i).length +
            (F₂.path j).length +
              (R.length + 2) := by
    intro i j
    simp [side, P₃, P₂, P₁,
      SimplePath.reverse_length]
    omega
  let grid :
      OffsetConcatenationGrid B F₁ F₂ :=
    OffsetConcatenationGrid.ofSidePaths
      B F₁ F₂ (R.length + 2)
      side returnPath hsideLength
      hsideReturnDisjoint
  apply setup.no_divisible_cycle
  exact offset_three_by_three_forces_cycle_divisible_by_five
    B F₁ F₂ grid

/--
The both-heavy part of Lemma 7.1.  Each family is rooted at the common
vertex `c`; the middle connector joins the two cut vertices.  The proof
explicitly handles the possible equality of those cut vertices: the
second reversed simple path omits its start from its tail, so the closure
is still a simple cycle.
-/
theorem StandingSetup.endLobePair_contradiction_of_heavy
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (P : EndLobePair (outsideEnvelopeGraph T))
    (A₁ : EndLobeAttachment T P.left)
    (A₂ : EndLobeAttachment T P.right)
    (hheavy₁ :
      2 ≤ (P.left.rootedExceptions D A₁).card)
    (hheavy₂ :
      2 ≤ (P.right.rootedExceptions D A₂).card) :
    False := by
  classical
  obtain ⟨F₁, hF₁support, -⟩ :=
    setup.heavy_endLobe_admissible_paths
      T P.left A₁ hheavy₁
  obtain ⟨F₂, hF₂support, -⟩ :=
    setup.heavy_endLobe_admissible_paths
      T P.right A₂ hheavy₂
  let fM : outsideEnvelopeGraph T →g B := {
    toFun := fun z => setup.inclusion z.1
    map_rel' := by
      intro a b hab
      exact setup.inclusion.toHom.map_rel' hab
  }
  have hfM : Function.Injective fM := by
    intro a b hab
    apply Subtype.ext
    exact setup.inclusion.injective hab
  let R : SimplePath B
      (setup.inclusion P.left.cut.1)
      (setup.inclusion P.right.cut.1) :=
    P.connector.mapInjectiveHom fM hfM
  have hRsupport :
      ∀ z ∈ R.walk.support,
        ∃ r,
          r ∈ P.connector.walk.support ∧
          z = setup.inclusion r.1 := by
    intro z hz
    change z ∈
      (P.connector.walk.map fM).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨r, hr, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨r, hr, rfl⟩
  have hblockIntersection :
      ∀ {z : V},
        z ∈ Set.range (P.left.blockHom setup T) →
        z ∈ Set.range (P.right.blockHom setup T) →
        z = setup.inclusion P.left.cut.1 ∧
          z = setup.inclusion P.right.cut.1 := by
    intro z hz₁ hz₂
    rcases P.left.classify_range_blockHom
        setup T hz₁ with hzCut₁ | ⟨a, ha, hza⟩
    · rcases P.right.classify_range_blockHom
          setup T hz₂ with hzCut₂ | ⟨b, hb, hzb⟩
      · exact ⟨hzCut₁, hzCut₂⟩
      · have hval : P.left.cut = b := by
          apply Subtype.ext
          exact setup.inclusion.injective
            (hzCut₁.symm.trans hzb)
        exact False.elim
          (P.left_cut_not_right_inner
            (hval ▸ hb))
    · rcases P.right.classify_range_blockHom
          setup T hz₂ with hzCut₂ | ⟨b, hb, hzb⟩
      · have hval : a = P.right.cut := by
          apply Subtype.ext
          exact setup.inclusion.injective
            (hza.symm.trans hzCut₂)
        exact False.elim
          (P.right_cut_not_left_inner
            (hval ▸ ha))
      · have hab : a = b := by
          apply Subtype.ext
          exact setup.inclusion.injective
            (hza.symm.trans hzb)
        exact False.elim
          (Finset.disjoint_left.mp
            P.inner_disjoint ha (hab ▸ hb))
  have hRF₂disjoint :
      ∀ j,
        R.walk.support.Disjoint
          (F₂.path j).reverse.walk.support.tail := by
    intro j
    apply List.disjoint_left.mpr
    intro z hzR hzF
    obtain ⟨r, hr, hzr⟩ :=
      hRsupport z hzR
    have hzFsupport :
        z ∈ (F₂.path j).walk.support := by
      have hz :
          z ∈ (F₂.path j).reverse.walk.support :=
        List.mem_of_mem_tail hzF
      simpa [SimplePath.reverse] using hz
    rcases hF₂support j z hzFsupport with
      hc | hzBlock
    · exact setup.c_not_old
        ⟨r.1, hzr.symm.trans hc⟩
    · rcases P.right.classify_range_blockHom
          setup T hzBlock with
        hzCut | ⟨b, hbInner, hzb⟩
      · have hzStart :
            z = setup.inclusion P.right.cut.1 :=
          hzCut
        exact (F₂.path j).reverse.start_not_mem_tail
          (hzStart ▸ hzF)
      · have hrb : r = b := by
          apply Subtype.ext
          exact setup.inclusion.injective
            (hzr.symm.trans hzb)
        exact P.connector_avoids_right b
          (hrb ▸ hr) hbInner
  let right : AdmissiblePathFamily B
      (setup.inclusion P.left.cut.1) c 3 := {
    start := F₂.start + R.length
    step := F₂.step
    admissible_step := F₂.admissible_step
    start_ge_two := by
      exact F₂.start_ge_two.trans
        (Nat.le_add_right F₂.start R.length)
    path := fun j =>
      R.appendDisjoint (F₂.path j).reverse
        (hRF₂disjoint j)
    length_path := by
      intro j
      rw [SimplePath.appendDisjoint_length,
        SimplePath.reverse_length,
        F₂.length_path]
      omega
  }
  have hF₁rightDisjoint :
      ∀ i j,
        (F₁.path i).walk.support.tail.Disjoint
          (right.path j).walk.support.tail := by
    intro i j
    apply List.disjoint_left.mpr
    intro z hzF₁ hzRight
    change z ∈
      (R.walk.append
        (F₂.path j).reverse.walk).support.tail
          at hzRight
    rw [SimpleGraph.Walk.tail_support_append]
      at hzRight
    rcases List.mem_append.mp hzRight with
      hzR | hzF₂
    · obtain ⟨r, hr, hzr⟩ :=
        hRsupport z
          (List.mem_of_mem_tail hzR)
      have hzF₁support :=
        List.mem_of_mem_tail hzF₁
      rcases hF₁support i z hzF₁support with
        hc | hzBlock
      · exact setup.c_not_old
          ⟨r.1, hzr.symm.trans hc⟩
      · rcases P.left.classify_range_blockHom
            setup T hzBlock with
          hzCut | ⟨a, haInner, hza⟩
        · have hzStart :
              z =
                setup.inclusion P.left.cut.1 :=
            hzCut
          exact R.start_not_mem_tail
            (hzStart ▸ hzR)
        · have hra : r = a := by
            apply Subtype.ext
            exact setup.inclusion.injective
              (hzr.symm.trans hza)
          exact P.connector_avoids_left a
            (hra ▸ hr) haInner
    · have hzF₁support :=
        List.mem_of_mem_tail hzF₁
      have hzF₂support :
          z ∈ (F₂.path j).walk.support := by
        have hz :
            z ∈ (F₂.path j).reverse.walk.support :=
          List.mem_of_mem_tail hzF₂
        simpa [SimplePath.reverse] using hz
      rcases hF₁support i z hzF₁support with
        hc₁ | hzBlock₁
      · exact F₁.path i |>.start_not_mem_tail
          (hc₁ ▸ hzF₁)
      · rcases hF₂support j z hzF₂support with
          hc₂ | hzBlock₂
        · exact F₁.path i |>.start_not_mem_tail
            (hc₂ ▸ hzF₁)
        · obtain ⟨-, hzCut₂⟩ :=
            hblockIntersection hzBlock₁ hzBlock₂
          exact (F₂.path j).reverse.start_not_mem_tail
            (hzCut₂ ▸ hzF₂)
  apply setup.no_divisible_cycle
  exact disjoint_three_by_three_forces_cycle_divisible_by_five
    B F₁ right hF₁rightDisjoint

/--
Lemma 7.1: every connected component of `M` is 2-connected.  The only
block-theory input is the explicit two-end-lobe certificate; all
attachment counts, light/heavy degree bookkeeping, and simple-cycle
closures are discharged above.
-/
theorem StandingSetup.outside_component_two_connected
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C] [DecidableEq C] :
    IsTwoConnected C.toSimpleGraph := by
  by_contra hnotTwo
  have hMdegree :
      MinDegreeAtLeast (outsideEnvelopeGraph T) 3 := by
    intro w
    by_cases hwD : w.1 ∈ D
    · exact
        (setup.outside_envelope_degree_bounds
          T w).2 hwD
    · exact
        ((setup.outside_envelope_degree_bounds
          T w).1 hwD).trans' (by omega)
  obtain ⟨P⟩ :=
    ClassicalGraphTheory.two_end_lobes_of_non_two_component
      (outsideEnvelopeGraph T) C hnotTwo
      hMdegree
  obtain ⟨A₁, A₂, hyne⟩ :=
    setup.exists_distinct_endLobePair_attachments
      T P
  by_cases hlight₁ :
      (P.left.rootedExceptions D A₁).card < 2
  · exact setup.endLobePair_contradiction_of_light
      T P A₁ A₂ hyne (Or.inl hlight₁)
  by_cases hlight₂ :
      (P.right.rootedExceptions D A₂).card < 2
  · exact setup.endLobePair_contradiction_of_light
      T P A₁ A₂ hyne (Or.inr hlight₂)
  exact setup.endLobePair_contradiction_of_heavy
    T P A₁ A₂ (by omega) (by omega)

namespace OutsideComponent

/-- Vertices of a component of `M`, viewed on the original carrier. -/
noncomputable def ambientVerts
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (C : (outsideEnvelopeGraph T).ConnectedComponent) :
    Finset W := by
  classical
  exact
    (Finset.univ.filter fun m =>
      m ∈ C.supp).image Subtype.val

@[simp] theorem mem_ambientVerts
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    (w : W) :
    w ∈ OutsideComponent.ambientVerts C ↔
      ∃ m : {v : W // v ∉ T.carrier},
        m ∈ C.supp ∧ m.1 = w := by
  classical
  constructor
  · intro hw
    obtain ⟨m, hm, hmw⟩ :=
      Finset.mem_image.mp hw
    have hmC :
        m ∈ C.supp := by
      exact (Finset.mem_filter.mp hm).2
    exact ⟨m, hmC, hmw⟩
  · rintro ⟨m, hm, rfl⟩
    exact Finset.mem_image.mpr
      ⟨m, by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hm⟩,
        rfl⟩

/-- Distinct interface neighbors of a component of `M`. -/
noncomputable def interfaceBoundary
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (C : (outsideEnvelopeGraph T).ConnectedComponent) :
    Finset W := by
  classical
  exact T.carrier.filter fun y =>
    ∃ m : {v : W // v ∉ T.carrier},
      m ∈ C.supp ∧ J.Adj m.1 y

@[simp] theorem mem_interfaceBoundary
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    (y : W) :
    y ∈ OutsideComponent.interfaceBoundary C ↔
      y ∈ T.carrier ∧
        ∃ m : {v : W // v ∉ T.carrier},
          m ∈ C.supp ∧ J.Adj m.1 y := by
  classical
  simp [interfaceBoundary]

/--
A component of `M` is a component region of `J` after its interface
neighbors are deleted.
-/
theorem ambient_componentRegion
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (C : (outsideEnvelopeGraph T).ConnectedComponent) :
    ComponentRegion J
      (OutsideComponent.interfaceBoundary C)
      (OutsideComponent.ambientVerts C) := by
  classical
  refine {
    nonempty := ?_
    disjoint := ?_
    connected := ?_
    closed := ?_
  }
  · obtain ⟨m, hm⟩ := C.nonempty_supp
    exact ⟨m.1,
      (OutsideComponent.mem_ambientVerts C m.1).2
      ⟨m, hm, rfl⟩⟩
  · apply Finset.disjoint_left.mpr
    intro w hwC hwBoundary
    obtain ⟨m, -, hmw⟩ :=
      (OutsideComponent.mem_ambientVerts C w).1 hwC
    have hwT :=
      (OutsideComponent.mem_interfaceBoundary C w).1
        hwBoundary |>.1
    exact m.2 (hmw ▸ hwT)
  · let f : C.toSimpleGraph →g
        J.induce
          (↑(OutsideComponent.ambientVerts C) :
            Set W) := {
      toFun := fun m => ⟨m.1.1,
        (OutsideComponent.mem_ambientVerts
          C m.1.1).2
          ⟨m.1, m.2, rfl⟩⟩
      map_rel' := by
        intro a b hab
        exact hab
    }
    have hf : Function.Surjective f := by
      intro w
      obtain ⟨m, hmC, hmw⟩ :=
        (OutsideComponent.mem_ambientVerts
          C w.1).1 w.2
      let mC : C := ⟨m, hmC⟩
      refine ⟨mC, ?_⟩
      apply Subtype.ext
      exact hmw
    exact C.connected_toSimpleGraph.map f hf
  · intro u v huC huv hvBoundary
    obtain ⟨m, hmC, hmu⟩ :=
      (OutsideComponent.mem_ambientVerts C u).1 huC
    by_cases hvT : v ∈ T.carrier
    · have hvB :
          v ∈ OutsideComponent.interfaceBoundary C :=
        (OutsideComponent.mem_interfaceBoundary C v).2
          ⟨hvT, m, hmC, by
            simpa [hmu] using huv⟩
      exact False.elim (hvBoundary hvB)
    · let n : {w : W // w ∉ T.carrier} :=
        ⟨v, hvT⟩
      have hmn :
          (outsideEnvelopeGraph T).Adj m n := by
        change J.Adj m.1 n.1
        change J.Adj m.1 v
        rw [hmu]
        exact huv
      have hnC :
          n ∈ C.supp :=
        C.mem_supp_of_adj_mem_supp hmC hmn
      exact
        (OutsideComponent.mem_ambientVerts C v).2
        ⟨n, hnC, rfl⟩

end OutsideComponent

/--
In the presence of a second component, 4-connectivity forces at least four
distinct interface neighbors of each component.
-/
theorem StandingSetup.four_le_component_interfaceBoundary
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C₁ C₂ :
      (outsideEnvelopeGraph T).ConnectedComponent)
    (hne : C₁ ≠ C₂) :
    4 ≤
      (OutsideComponent.interfaceBoundary C₁).card := by
  classical
  obtain ⟨m₂, hm₂C⟩ := C₂.nonempty_supp
  have hm₂notC₁ :
      m₂.1 ∉ OutsideComponent.ambientVerts C₁ := by
    intro hm
    obtain ⟨m₁, hm₁C, hm₁m₂⟩ :=
      (OutsideComponent.mem_ambientVerts
        C₁ m₂.1).1 hm
    have hmEq : m₁ = m₂ := by
      apply Subtype.ext
      exact hm₁m₂
    have hcomp :
        C₁ = C₂ := by
      have h₁ :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff
          C₁ m₁).1 hm₁C
      have h₂ :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff
          C₂ m₂).1 hm₂C
      calc
        C₁ =
            (outsideEnvelopeGraph T).connectedComponentMk
              m₁ := h₁.symm
        _ =
            (outsideEnvelopeGraph T).connectedComponentMk
              m₂ := congrArg
                (outsideEnvelopeGraph T).connectedComponentMk
                hmEq
        _ = C₂ := h₂
    exact hne hcomp
  have hm₂notBoundary :
      m₂.1 ∉
        OutsideComponent.interfaceBoundary C₁ := by
    intro hm
    have hmT :=
      (OutsideComponent.mem_interfaceBoundary
        C₁ m₂.1).1
        hm |>.1
    exact m₂.2 hmT
  exact
    (OutsideComponent.ambient_componentRegion
      C₁).connectivity_le_separator_card
      setup.four_connected hm₂notC₁
        hm₂notBoundary

/-- Distinct interface vertices cannot attach to the same outside vertex. -/
theorem ThetaEnvelope.distinct_interface_attachments
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W}
    (T : ThetaEnvelope J)
    (x y : W) (hxy : x ≠ y)
    (hxT : x ∈ T.carrier)
    (hyT : y ∈ T.carrier)
    (u v : {w : W // w ∉ T.carrier})
    (hux : J.Adj u.1 x)
    (hvy : J.Adj v.1 y) :
    u ≠ v := by
  intro huv
  have hval : u.1 = v.1 :=
    congrArg Subtype.val huv
  have hsub :
      (↑({x, y} : Finset W) : Set W) ⊆
        J.neighborSet u.1 ∩
          (↑T.carrier : Set W) := by
    intro z hz
    simp only [Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨hux, hxT⟩
    · exact ⟨by simpa [hval] using hvy, hyT⟩
  have hlower :
      2 ≤ finiteBoundaryDegree J T.carrier u.1 := by
    unfold finiteBoundaryDegree
    calc
      2 = ({x, y} : Finset W).card :=
        (Finset.card_pair hxy).symm
      _ =
          (↑({x, y} : Finset W) : Set W).ncard :=
        (Set.ncard_coe_finset _).symm
      _ ≤
          (J.neighborSet u.1 ∩
            (↑T.carrier : Set W)).ncard :=
        Set.ncard_le_ncard hsub
  have hupper :=
    T.outside_boundary_degree_le_one u.1 u.2
  omega

/-- Two independent attachment edges from one component of `M`. -/
structure ComponentAttachmentPair
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent) where
  /-- First component endpoint of the two attachment edges. -/
  root₁ : C
  /-- Second component endpoint of the two attachment edges. -/
  root₂ : C
  roots_ne : root₁ ≠ root₂
  /-- Interface endpoint adjacent to `root₁`. -/
  interface₁ : W
  /-- Interface endpoint adjacent to `root₂`. -/
  interface₂ : W
  interfaces_ne : interface₁ ≠ interface₂
  interface₁_mem :
    interface₁ ∈ OutsideComponent.interfaceBoundary C
  interface₂_mem :
    interface₂ ∈ OutsideComponent.interfaceBoundary C
  adjacent₁ : J.Adj root₁.1.1 interface₁
  adjacent₂ : J.Adj root₂.1.1 interface₂

namespace OutsideComponent

/-- Deficient component vertices other than the two selected roots. -/
noncomputable def rootedExceptions
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    {C : (outsideEnvelopeGraph T).ConnectedComponent}
    [Fintype C] [DecidableEq C]
    (D : Finset W) (A : ComponentAttachmentPair T C) :
    Finset C := by
  classical
  exact Finset.univ.filter fun z =>
    z.1.1 ∈ D ∧ z ≠ A.root₁ ∧ z ≠ A.root₂

@[simp] theorem mem_rootedExceptions
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    {C : (outsideEnvelopeGraph T).ConnectedComponent}
    [Fintype C] [DecidableEq C]
    (D : Finset W) (A : ComponentAttachmentPair T C)
    (z : C) :
    z ∈ OutsideComponent.rootedExceptions D A ↔
      z.1.1 ∈ D ∧ z ≠ A.root₁ ∧ z ≠ A.root₂ := by
  classical
  unfold rootedExceptions
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- All deficient vertices of a component. -/
noncomputable def deficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C]
    (D : Finset W) :
    Finset C := by
  classical
  exact Finset.univ.filter fun z => z.1.1 ∈ D

@[simp] theorem mem_deficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C]
    (D : Finset W) (z : C) :
    z ∈ OutsideComponent.deficient C D ↔
      z.1.1 ∈ D := by
  classical
  unfold deficient
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem rootedExceptions_subset_deficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {T : ThetaEnvelope J}
    {C : (outsideEnvelopeGraph T).ConnectedComponent}
    [Fintype C] [DecidableEq C]
    (D : Finset W) (A : ComponentAttachmentPair T C) :
    OutsideComponent.rootedExceptions D A ⊆
      OutsideComponent.deficient C D := by
  intro z hz
  exact (OutsideComponent.mem_deficient C D z).2
    ((OutsideComponent.mem_rootedExceptions
      D A z).1 hz |>.1)

/-- Inclusion of a component of `M` into the ambient block. -/
def hom
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent) :
    C.toSimpleGraph →g B where
  toFun z := setup.inclusion z.1.1
  map_rel' := by
    intro a b hab
    exact setup.inclusion.toHom.map_rel' hab

theorem hom_injective
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent) :
    Function.Injective
      (OutsideComponent.hom setup T C) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact setup.inclusion.injective hab

theorem c_not_range_hom
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent) :
    c ∉ Set.range
      (OutsideComponent.hom setup T C) := by
  rintro ⟨z, hz⟩
  apply setup.c_not_old
  exact ⟨z.1.1, hz⟩

end OutsideComponent

/--
Two distinct components admit two independent attachment edges each, with
all four interface endpoints pairwise distinct.
-/
theorem StandingSetup.exists_component_attachment_pairs
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C₁ C₂ :
      (outsideEnvelopeGraph T).ConnectedComponent)
    (hne : C₁ ≠ C₂) :
    ∃ A₁ : ComponentAttachmentPair T C₁,
      ∃ A₂ : ComponentAttachmentPair T C₂,
        Disjoint ({A₁.interface₁, A₁.interface₂} :
          Finset W)
          ({A₂.interface₁, A₂.interface₂} :
            Finset W) := by
  classical
  have hcard₁ :=
    setup.four_le_component_interfaceBoundary
      T C₁ C₂ hne
  have hcard₂ :=
    setup.four_le_component_interfaceBoundary
      T C₂ C₁ hne.symm
  obtain ⟨y₁₁, hy₁₁⟩ :=
    Finset.card_pos.mp (by omega :
      0 <
        (OutsideComponent.interfaceBoundary C₁).card)
  have hC₁erase :
      0 <
        ((OutsideComponent.interfaceBoundary C₁).erase
          y₁₁).card := by
    by_cases hy :
        y₁₁ ∈ OutsideComponent.interfaceBoundary C₁
    · rw [Finset.card_erase_of_mem hy]
      omega
    · rw [Finset.erase_eq_of_notMem hy]
      omega
  obtain ⟨y₁₂, hy₁₂Erase⟩ :=
    Finset.card_pos.mp hC₁erase
  have hy₁₂ :=
    Finset.mem_of_mem_erase hy₁₂Erase
  have hy₁ne : y₁₁ ≠ y₁₂ :=
    fun h =>
      (Finset.mem_erase.mp hy₁₂Erase).1 h.symm
  let S₂ :=
    ((OutsideComponent.interfaceBoundary C₂).erase
      y₁₁).erase y₁₂
  have hS₂card : 2 ≤ S₂.card := by
    have h₁ :=
      Finset.pred_card_le_card_erase
        (s := OutsideComponent.interfaceBoundary C₂)
        (a := y₁₁)
    have h₂ :=
      Finset.pred_card_le_card_erase
        (s :=
          (OutsideComponent.interfaceBoundary C₂).erase
            y₁₁)
        (a := y₁₂)
    dsimp [S₂]
    omega
  obtain ⟨y₂₁, hy₂₁S⟩ :=
    Finset.card_pos.mp (by omega :
      0 < S₂.card)
  have hS₂erase :
      0 < (S₂.erase y₂₁).card := by
    rw [Finset.card_erase_of_mem hy₂₁S]
    omega
  obtain ⟨y₂₂, hy₂₂Erase⟩ :=
    Finset.card_pos.mp hS₂erase
  have hy₂₂S :=
    Finset.mem_of_mem_erase hy₂₂Erase
  have hy₂ne : y₂₁ ≠ y₂₂ :=
    fun h =>
      (Finset.mem_erase.mp hy₂₂Erase).1 h.symm
  have hy₂₁Data :
      y₂₁ ∈
        OutsideComponent.interfaceBoundary C₂ ∧
      y₂₁ ≠ y₁₁ ∧ y₂₁ ≠ y₁₂ := by
    have hOuter :
        y₂₁ ∈
          (OutsideComponent.interfaceBoundary C₂).erase
            y₁₁ :=
      (Finset.mem_erase.mp hy₂₁S).2
    exact
      ⟨(Finset.mem_erase.mp hOuter).2,
        (Finset.mem_erase.mp hOuter).1,
        (Finset.mem_erase.mp hy₂₁S).1⟩
  have hy₂₂Data :
      y₂₂ ∈
        OutsideComponent.interfaceBoundary C₂ ∧
      y₂₂ ≠ y₁₁ ∧ y₂₂ ≠ y₁₂ := by
    have hy₂₂S' : y₂₂ ∈ S₂ :=
      Finset.mem_of_mem_erase hy₂₂Erase
    have hOuter :
        y₂₂ ∈
          (OutsideComponent.interfaceBoundary C₂).erase
            y₁₁ :=
      Finset.mem_of_mem_erase hy₂₂S'
    exact ⟨Finset.mem_of_mem_erase hOuter,
      (Finset.mem_erase.mp hOuter).1,
      (Finset.mem_erase.mp hy₂₂S').1⟩
  obtain ⟨u₁₁, hu₁₁C, hu₁₁y⟩ :=
    (OutsideComponent.mem_interfaceBoundary
      C₁ y₁₁).1 hy₁₁ |>.2
  obtain ⟨u₁₂, hu₁₂C, hu₁₂y⟩ :=
    (OutsideComponent.mem_interfaceBoundary
      C₁ y₁₂).1 hy₁₂ |>.2
  obtain ⟨u₂₁, hu₂₁C, hu₂₁y⟩ :=
    (OutsideComponent.mem_interfaceBoundary
      C₂ y₂₁).1 hy₂₁Data.1 |>.2
  obtain ⟨u₂₂, hu₂₂C, hu₂₂y⟩ :=
    (OutsideComponent.mem_interfaceBoundary
      C₂ y₂₂).1 hy₂₂Data.1 |>.2
  have hu₁ne : u₁₁ ≠ u₁₂ :=
    T.distinct_interface_attachments
      y₁₁ y₁₂ hy₁ne
      ((OutsideComponent.mem_interfaceBoundary
        C₁ y₁₁).1 hy₁₁ |>.1)
      ((OutsideComponent.mem_interfaceBoundary
        C₁ y₁₂).1 hy₁₂ |>.1)
      u₁₁ u₁₂ hu₁₁y hu₁₂y
  have hu₂ne : u₂₁ ≠ u₂₂ :=
    T.distinct_interface_attachments
      y₂₁ y₂₂ hy₂ne
      ((OutsideComponent.mem_interfaceBoundary
        C₂ y₂₁).1 hy₂₁Data.1 |>.1)
      ((OutsideComponent.mem_interfaceBoundary
        C₂ y₂₂).1 hy₂₂Data.1 |>.1)
      u₂₁ u₂₂ hu₂₁y hu₂₂y
  let A₁ : ComponentAttachmentPair T C₁ := {
    root₁ := ⟨u₁₁, hu₁₁C⟩
    root₂ := ⟨u₁₂, hu₁₂C⟩
    roots_ne := fun h => hu₁ne
      (congrArg Subtype.val h)
    interface₁ := y₁₁
    interface₂ := y₁₂
    interfaces_ne := hy₁ne
    interface₁_mem := hy₁₁
    interface₂_mem := hy₁₂
    adjacent₁ := hu₁₁y
    adjacent₂ := hu₁₂y
  }
  let A₂ : ComponentAttachmentPair T C₂ := {
    root₁ := ⟨u₂₁, hu₂₁C⟩
    root₂ := ⟨u₂₂, hu₂₂C⟩
    roots_ne := fun h => hu₂ne
      (congrArg Subtype.val h)
    interface₁ := y₂₁
    interface₂ := y₂₂
    interfaces_ne := hy₂ne
    interface₁_mem := hy₂₁Data.1
    interface₂_mem := hy₂₂Data.1
    adjacent₁ := hu₂₁y
    adjacent₂ := hu₂₂y
  }
  refine ⟨A₁, A₂, ?_⟩
  apply Finset.disjoint_left.mpr
  intro y hy₁ hy₂
  simp only [Finset.mem_insert,
    Finset.mem_singleton] at hy₁ hy₂
  rcases hy₁ with rfl | rfl <;>
    rcases hy₂ with h | h
  · exact hy₂₁Data.2.1 h.symm
  · exact hy₂₂Data.2.1 h.symm
  · exact hy₂₁Data.2.2 h.symm
  · exact hy₂₂Data.2.2 h.symm

/--
Lemma 3.3 on a 2-connected component of `M`, rooted at its two selected
attachment vertices.
-/
theorem StandingSetup.component_admissible_paths
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C] [DecidableEq C]
    (A : ComponentAttachmentPair T C) :
    AmbientRootLiftResult B c
      (setup.inclusion A.root₁.1.1)
      (setup.inclusion A.root₂.1.1) 3
      (Set.range (OutsideComponent.hom setup T C))
      ((OutsideComponent.rootedExceptions D A).card < 2) := by
  classical
  let E := C.toSimpleGraph
  let x := A.root₁
  let y := A.root₂
  let Z := OutsideComponent.rootedExceptions D A
  let G := E \ edge x y
  have hxy : x ≠ y := A.roots_ne
  have hEtwo : IsTwoConnected E :=
    setup.outside_component_two_connected T C
  have hEle : E ≤ G ⊔ edge x y := by
    intro p q hpq
    by_cases hedge : (edge x y).Adj p q
    · exact Or.inr hedge
    · exact Or.inl ⟨hpq, hedge⟩
  have hconn :
      IsTwoConnected (G ⊔ edge x y) := by
    refine ⟨hEtwo.1, ?_⟩
    intro S hS
    apply (hEtwo.2 S hS).mono
    intro p q hpq
    exact hEle hpq
  have hnotadj : ¬G.Adj x y := by
    rintro ⟨-, hnotEdge⟩
    apply hnotEdge
    exact (SimpleGraph.edge_adj x y x y).2
      ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
  have hxZ : x ∉ Z := by
    intro hx
    exact
      ((OutsideComponent.mem_rootedExceptions
        D A x).1 hx).2.1 rfl
  have hyZ : y ∉ Z := by
    intro hy
    exact
      ((OutsideComponent.mem_rootedExceptions
        D A y).1 hy).2.2 rfl
  have hMEdegree :
      ∀ z : C,
        finiteDegree (outsideEnvelopeGraph T) z.1 ≤
          finiteDegree E z := by
    intro z
    apply finiteDegree_le_induce
      (outsideEnvelopeGraph T) C.supp z
    intro w hzw
    exact C.mem_supp_of_adj_mem_supp z.2 hzw
  have hdeg :
      ∀ z, z ≠ x → z ≠ y → z ∉ Z →
        4 ≤ finiteDegree G z := by
    intro z hzx hzy hzZ
    have hzNotD : z.1.1 ∉ D := by
      intro hzD
      apply hzZ
      exact
        (OutsideComponent.mem_rootedExceptions
          D A z).2 ⟨hzD, hzx, hzy⟩
    have hMlower :=
      (setup.outside_envelope_degree_bounds
        T z.1).1 hzNotD
    have hEbound := hMEdegree z
    rw [finiteDegree_sdiff_edge_of_ne
      E x y z hzx hzy]
    exact hMlower.trans hEbound
  have hdegZ :
      ∀ z ∈ Z, 3 ≤ finiteDegree G z := by
    intro z hzZ
    have hzData :=
      (OutsideComponent.mem_rootedExceptions
        D A z).1 hzZ
    have hMlower :=
      (setup.outside_envelope_degree_bounds
        T z.1).2 hzData.1
    have hEbound := hMEdegree z
    rw [finiteDegree_sdiff_edge_of_ne
      E x y z hzData.2.1 hzData.2.2]
    exact hMlower.trans hEbound
  have horder : 4 ≤ Fintype.card C := by
    obtain ⟨m, hmC⟩ := C.nonempty_supp
    let mC : C := ⟨m, hmC⟩
    have hMlower :
        3 ≤ finiteDegree
          (outsideEnvelopeGraph T) m := by
      by_cases hmD : m.1 ∈ D
      · exact
          (setup.outside_envelope_degree_bounds
            T m).2 hmD
      · exact
          ((setup.outside_envelope_degree_bounds
            T m).1 hmD).trans' (by omega)
    have hEbound := hMEdegree mC
    have hElower :
        3 ≤ finiteDegree E mC := by
      have hMlower' :
          3 ≤ finiteDegree
            (outsideEnvelopeGraph T) mC.1 := by
        simpa [mC] using hMlower
      exact hMlower'.trans hEbound
    have hEq :
        finiteDegree E mC = E.degree mC := by
      unfold finiteDegree SimpleGraph.degree
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hlt := E.degree_lt_card_verts mC
    rw [hEq] at hElower
    omega
  have result : RootLiftResult G Z x y 3 := by
    apply root_lifting 3 G Z Z x y
    · omega
    · exact hxy
    · exact hnotadj
    · exact hconn
    · exact Finset.Subset.rfl
    · exact hxZ
    · exact hyZ
    · exact hdeg
    · exact hdegZ
    · intro _
      exact horder
  let f : G →g B := {
    toFun := fun z => setup.inclusion z.1.1
    map_rel' := by
      intro p q hpq
      exact setup.inclusion.toHom.map_rel' hpq.1
  }
  have mapped :=
    result.mapToAmbient f c
      (fun z hz =>
        setup.deficient_adjacent_to_c z.1.1
          ((OutsideComponent.mem_rootedExceptions
            D A z).1 hz |>.1))
      (by
        intro p q hpq
        apply Subtype.ext
        apply Subtype.ext
        exact setup.inclusion.injective hpq)
      (by
        rintro ⟨z, hz⟩
        apply setup.c_not_old
        exact ⟨z.1.1, hz⟩)
  convert mapped using 1 <;>
    simp [f, G, E, x, y,
      OutsideComponent.hom]

/--
The both-heavy component construction, rooted at `c` and the first
selected attachment vertex.
-/
theorem StandingSetup.heavy_component_admissible_paths
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C] [DecidableEq C]
    (A : ComponentAttachmentPair T C)
    (hheavy :
      2 ≤ (OutsideComponent.rootedExceptions D A).card) :
    AmbientRootLiftResult B c c
      (setup.inclusion A.root₁.1.1) 3
      (Set.range (OutsideComponent.hom setup T C))
      False := by
  classical
  let E := C.toSimpleGraph
  let DZ := OutsideComponent.deficient C D
  let y := A.root₁
  let K := adjoinRoot E DZ
  let rC : Option C := none
  let rY : Option C := some y
  let G := K \ edge rC rY
  have hDZcard : 2 ≤ DZ.card := by
    exact hheavy.trans
      (Finset.card_le_card
        (OutsideComponent.rootedExceptions_subset_deficient
          D A))
  have hEtwo : IsTwoConnected E :=
    setup.outside_component_two_connected T C
  have hKtwo : IsTwoConnected K :=
    isTwoConnected_adjoinRoot E DZ
      hEtwo hDZcard
  have hrne : rC ≠ rY := by simp [rC, rY]
  have hKle : K ≤ G ⊔ edge rC rY := by
    intro p q hpq
    by_cases hedge : (edge rC rY).Adj p q
    · exact Or.inr hedge
    · exact Or.inl ⟨hpq, hedge⟩
  have hconn :
      IsTwoConnected (G ⊔ edge rC rY) := by
    refine ⟨hKtwo.1, ?_⟩
    intro S hS
    apply (hKtwo.2 S hS).mono
    intro p q hpq
    exact hKle hpq
  have hMEdegree :
      ∀ z : C,
        finiteDegree (outsideEnvelopeGraph T) z.1 ≤
          finiteDegree E z := by
    intro z
    apply finiteDegree_le_induce
      (outsideEnvelopeGraph T) C.supp z
    intro w hzw
    exact C.mem_supp_of_adj_mem_supp z.2 hzw
  have hdeg :
      ∀ v, v ≠ rC → v ≠ rY →
        4 ≤ finiteDegree G v := by
    intro v hvC hvY
    cases v with
    | none =>
        exact False.elim (hvC rfl)
    | some z =>
        have hzy : z ≠ y := by
          intro h
          exact hvY (by simp [rY, h])
        have hvC' :
            (some z : Option C) ≠ rC := by
          simp [rC]
        have hvY' :
            (some z : Option C) ≠ rY := by
          simpa [rY] using hzy
        have hEbound := hMEdegree z
        rw [finiteDegree_sdiff_edge_of_ne
          K rC rY (some z) hvC' hvY']
        rw [finiteDegree_adjoinRoot_some]
        by_cases hzDZ : z ∈ DZ
        · have hzD :=
            (OutsideComponent.mem_deficient
              C D z).1 hzDZ
          have hMlower :=
            (setup.outside_envelope_degree_bounds
              T z.1).2 hzD
          have hElower :
              3 ≤ finiteDegree E z :=
            hMlower.trans hEbound
          simp [hzDZ]
          omega
        · have hzNotD : z.1.1 ∉ D := by
            intro hzD
            exact hzDZ
              ((OutsideComponent.mem_deficient
                C D z).2 hzD)
          have hMlower :=
            (setup.outside_envelope_degree_bounds
              T z.1).1 hzNotD
          have hElower :
              4 ≤ finiteDegree E z :=
            hMlower.trans hEbound
          simp [hzDZ]
          exact hElower
  obtain ⟨F⟩ :=
    GHLM.rooted_admissible_paths
      3 G rC rY (by omega) hrne hconn hdeg
  let φ : K →g B :=
    adjoinRootHom E DZ
      (OutsideComponent.hom setup T C) c
      (fun z hz =>
        setup.deficient_adjacent_to_c z.1.1
          ((OutsideComponent.mem_deficient
            C D z).1 hz))
  have hφ : Function.Injective φ :=
    adjoinRootHom_injective E DZ
      (OutsideComponent.hom setup T C) c
      (fun z hz =>
        setup.deficient_adjacent_to_c z.1.1
          ((OutsideComponent.mem_deficient
            C D z).1 hz))
      (OutsideComponent.hom_injective setup T C)
      (OutsideComponent.c_not_range_hom setup T C)
  let f : G →g B := {
    toFun := φ
    map_rel' := by
      intro p q hpq
      exact φ.map_rel' hpq.1
  }
  let F' := F.mapInjectiveHom f hφ
  refine ⟨F', ?_⟩
  constructor
  · intro i v hv
    have hv' := hv
    change v ∈ ((F.path i).walk.map f).support at hv'
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨w, -, rfl⟩ :=
      List.mem_map.mp hv'
    cases w with
    | none => exact Or.inl rfl
    | some z => exact Or.inr ⟨z, rfl⟩
  · intro hfalse
    exact False.elim hfalse

/-- A rooted component family relabeled to match an ordered pair of its
two selected interface vertices. -/
structure OrientedComponentFamily
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    (x y : (↑T.carrier : Set W))
    (small : Prop) where
  /-- Component root whose attachment is oriented toward `x`. -/
  rootX : C
  /-- Component root whose attachment is oriented toward `y`. -/
  rootY : C
  /-- Three admissible paths between the ambient images of the oriented roots. -/
  family : AdmissiblePathFamily B
    (setup.inclusion rootX.1.1)
    (setup.inclusion rootY.1.1) 3
  adjacentX : J.Adj rootX.1.1 x.1
  adjacentY : J.Adj rootY.1.1 y.1
  support :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = c ∨
        v ∈ Set.range
          (OutsideComponent.hom setup T C)
  avoid_c :
    small → ∀ i, c ∉ (family.path i).walk.support

/--
Relabel (or reverse) a two-root component family to agree with any ordered
listing of the selected two interface vertices.
-/
theorem StandingSetup.orient_component_family
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C : (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C] [DecidableEq C]
    (A : ComponentAttachmentPair T C)
    (x y : (↑T.carrier : Set W))
    (hx :
      x ∈ ({⟨A.interface₁,
          (OutsideComponent.mem_interfaceBoundary
            C A.interface₁).1 A.interface₁_mem |>.1⟩,
        ⟨A.interface₂,
          (OutsideComponent.mem_interfaceBoundary
            C A.interface₂).1 A.interface₂_mem |>.1⟩} :
        Finset (↑T.carrier : Set W)))
    (hy :
      y ∈ ({⟨A.interface₁,
          (OutsideComponent.mem_interfaceBoundary
            C A.interface₁).1 A.interface₁_mem |>.1⟩,
        ⟨A.interface₂,
          (OutsideComponent.mem_interfaceBoundary
            C A.interface₂).1 A.interface₂_mem |>.1⟩} :
        Finset (↑T.carrier : Set W)))
    (hxy : x ≠ y) :
    Nonempty
      (OrientedComponentFamily setup T C x y
        ((OutsideComponent.rootedExceptions D A).card < 2)) := by
  classical
  obtain ⟨F, hsupport, havoid⟩ :=
    setup.component_admissible_paths T C A
  let y₁ : (↑T.carrier : Set W) :=
    ⟨A.interface₁,
      (OutsideComponent.mem_interfaceBoundary
        C A.interface₁).1 A.interface₁_mem |>.1⟩
  let y₂ : (↑T.carrier : Set W) :=
    ⟨A.interface₂,
      (OutsideComponent.mem_interfaceBoundary
        C A.interface₂).1 A.interface₂_mem |>.1⟩
  have hxCases : x = y₁ ∨ x = y₂ := by
    simpa [y₁, y₂] using hx
  have hyCases : y = y₁ ∨ y = y₂ := by
    simpa [y₁, y₂] using hy
  rcases hxCases with rfl | rfl
  · have hy₂ : y = y₂ :=
      hyCases.resolve_left (fun h => hxy h.symm)
    subst y
    exact ⟨{
      rootX := A.root₁
      rootY := A.root₂
      family := F
      adjacentX := A.adjacent₁
      adjacentY := A.adjacent₂
      support := hsupport
      avoid_c := havoid
    }⟩
  · have hy₁ : y = y₁ :=
      hyCases.resolve_right (fun h => hxy h.symm)
    subst y
    let Fr := F.reverse
    refine ⟨{
      rootX := A.root₂
      rootY := A.root₁
      family := Fr
      adjacentX := A.adjacent₂
      adjacentY := A.adjacent₁
      support := ?_
      avoid_c := ?_
    }⟩
    · intro i v hv
      apply hsupport i v
      simpa [Fr, AdmissiblePathFamily.reverse,
        SimplePath.reverse] using hv
    · intro hsmall i hcSupport
      apply havoid hsmall i
      simpa [Fr, AdmissiblePathFamily.reverse,
        SimplePath.reverse] using hcSupport

/-- The both-heavy case in Lemma 7.2. -/
theorem StandingSetup.two_component_contradiction_of_heavy
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C₁ C₂ :
      (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C₁] [DecidableEq C₁]
    [Fintype C₂] [DecidableEq C₂]
    (hne : C₁ ≠ C₂)
    (A₁ : ComponentAttachmentPair T C₁)
    (A₂ : ComponentAttachmentPair T C₂)
    (hinterfaces :
      Disjoint ({A₁.interface₁, A₁.interface₂} :
        Finset W)
        ({A₂.interface₁, A₂.interface₂} :
          Finset W))
    (hheavy₁ :
      2 ≤ (OutsideComponent.rootedExceptions D A₁).card)
    (hheavy₂ :
      2 ≤ (OutsideComponent.rootedExceptions D A₂).card) :
    False := by
  classical
  obtain ⟨F₁, hF₁support, -⟩ :=
    setup.heavy_component_admissible_paths
      T C₁ A₁ hheavy₁
  obtain ⟨F₂, hF₂support, -⟩ :=
    setup.heavy_component_admissible_paths
      T C₂ A₂ hheavy₂
  have hyne :
      A₁.interface₁ ≠ A₂.interface₁ := by
    intro h
    have hleft :
        A₁.interface₁ ∈
          ({A₁.interface₁, A₁.interface₂} :
            Finset W) := by simp
    have hright :
        A₁.interface₁ ∈
          ({A₂.interface₁, A₂.interface₂} :
            Finset W) := by
      simp [h]
    exact Finset.disjoint_left.mp hinterfaces
      hleft hright
  have hy₁T :
      A₁.interface₁ ∈ T.carrier :=
    (OutsideComponent.mem_interfaceBoundary
      C₁ A₁.interface₁).1 A₁.interface₁_mem |>.1
  have hy₂T :
      A₂.interface₁ ∈ T.carrier :=
    (OutsideComponent.mem_interfaceBoundary
      C₂ A₂.interface₁).1 A₂.interface₁_mem |>.1
  let y₁T : (↑T.carrier : Set W) :=
    ⟨A₁.interface₁, hy₁T⟩
  let y₂T : (↑T.carrier : Set W) :=
    ⟨A₂.interface₁, hy₂T⟩
  have hTconnected :
      (J.induce (↑T.carrier : Set W)).Connected := by
    have hdeleted :=
      T.two_connected.2 ∅ (by simp)
    exact hdeleted.map
      (SimpleGraph.Embedding.induce
        {v : (↑T.carrier : Set W) |
          v ∉ (∅ : Finset (↑T.carrier : Set W))}).toHom
      (by
        intro v
        exact ⟨⟨v, by simp⟩, rfl⟩)
  obtain ⟨Qwalk, hQwalk⟩ :=
    hTconnected.exists_isPath y₁T y₂T
  let QJ : SimplePath
      (J.induce (↑T.carrier : Set W))
      y₁T y₂T := ⟨Qwalk, hQwalk⟩
  let fT :
      J.induce (↑T.carrier : Set W) →g B := {
    toFun := fun z => setup.inclusion z.1
    map_rel' := by
      intro a b hab
      exact setup.inclusion.toHom.map_rel' hab
  }
  have hfT : Function.Injective fT := by
    intro a b hab
    apply Subtype.ext
    exact setup.inclusion.injective hab
  let Q : SimplePath B
      (setup.inclusion A₁.interface₁)
      (setup.inclusion A₂.interface₁) :=
    QJ.mapInjectiveHom fT hfT
  have hQsupport :
      ∀ z ∈ Q.walk.support,
        ∃ q : (↑T.carrier : Set W),
          z = setup.inclusion q.1 := by
    intro z hz
    change z ∈ (QJ.walk.map fT).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨q, -, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨q, rfl⟩
  have hcomponentRangesDisjoint :
      ∀ {z : V},
        z ∈ Set.range (OutsideComponent.hom setup T C₁) →
        z ∈ Set.range (OutsideComponent.hom setup T C₂) →
        False := by
    intro z hz₁ hz₂
    obtain ⟨a, ha⟩ := hz₁
    obtain ⟨b, hb⟩ := hz₂
    have hab : a.1 = b.1 := by
      apply Subtype.ext
      exact setup.inclusion.injective
        (ha.trans hb.symm)
    have h₁ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff
        C₁ a.1).1 a.2
    have h₂ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff
        C₂ b.1).1 b.2
    apply hne
    calc
      C₁ =
          (outsideEnvelopeGraph T).connectedComponentMk
            a.1 := h₁.symm
      _ =
          (outsideEnvelopeGraph T).connectedComponentMk
            b.1 := congrArg
              (outsideEnvelopeGraph T).connectedComponentMk
              hab
      _ = C₂ := h₂
  have hu₁Q :
      setup.inclusion A₁.root₁.1.1 ∉
        Q.walk.support := by
    intro hz
    obtain ⟨q, hzq⟩ := hQsupport _ hz
    have hval :
        A₁.root₁.1.1 = q.1 :=
      setup.inclusion.injective hzq
    exact A₁.root₁.1.2 (hval ▸ q.2)
  have hAdj₁ :
      B.Adj
        (setup.inclusion A₁.root₁.1.1)
        (setup.inclusion A₁.interface₁) :=
    setup.inclusion.toHom.map_rel' A₁.adjacent₁
  let Q₁ : SimplePath B
      (setup.inclusion A₁.root₁.1.1)
      (setup.inclusion A₂.interface₁) :=
    Q.prependEdge hAdj₁ hu₁Q
  have hu₂Q₁ :
      setup.inclusion A₂.root₁.1.1 ∉
        Q₁.walk.support := by
    intro hz
    change setup.inclusion A₂.root₁.1.1 ∈
      (Q.walk.cons hAdj₁).support at hz
    simp only [SimpleGraph.Walk.support_cons,
      List.mem_cons] at hz
    rcases hz with hzRoot | hzQ
    · have hval : A₂.root₁.1 = A₁.root₁.1 := by
        apply Subtype.ext
        exact setup.inclusion.injective hzRoot
      have h₁ :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff
          C₁ A₁.root₁.1).1 A₁.root₁.2
      have h₂ :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff
          C₂ A₂.root₁.1).1 A₂.root₁.2
      apply hne
      calc
        C₁ =
            (outsideEnvelopeGraph T).connectedComponentMk
              A₁.root₁.1 := h₁.symm
        _ =
            (outsideEnvelopeGraph T).connectedComponentMk
              A₂.root₁.1 := congrArg
                (outsideEnvelopeGraph T).connectedComponentMk
                hval.symm
        _ = C₂ := h₂
    · obtain ⟨q, hzq⟩ := hQsupport _ hzQ
      have hval :
          A₂.root₁.1.1 = q.1 :=
        setup.inclusion.injective hzq
      exact A₂.root₁.1.2 (hval ▸ q.2)
  have hAdj₂ :
      B.Adj
        (setup.inclusion A₂.interface₁)
        (setup.inclusion A₂.root₁.1.1) :=
    (setup.inclusion.toHom.map_rel'
      A₂.adjacent₁).symm
  let bridge : SimplePath B
      (setup.inclusion A₁.root₁.1.1)
      (setup.inclusion A₂.root₁.1.1) :=
    Q₁.appendEdge hAdj₂ hu₂Q₁
  have hBridgeClass :
      ∀ z ∈ bridge.walk.support,
        z = setup.inclusion A₁.root₁.1.1 ∨
        z = setup.inclusion A₂.root₁.1.1 ∨
          ∃ q : (↑T.carrier : Set W),
            z = setup.inclusion q.1 := by
    intro z hz
    change z ∈
      ((Q.walk.cons hAdj₁).concat hAdj₂).support at hz
    simp only [SimpleGraph.Walk.support_concat,
      SimpleGraph.Walk.support_cons,
      List.mem_append, List.mem_cons] at hz
    rcases hz with (rfl | hzQ) | hzEnd
    · exact Or.inl rfl
    · exact Or.inr (Or.inr
        (hQsupport z hzQ))
    · rcases hzEnd with hzEnd | hzNil
      · exact Or.inr (Or.inl hzEnd)
      · simp at hzNil
  have hBridgeF₂disjoint :
      ∀ j,
        bridge.walk.support.Disjoint
          (F₂.path j).reverse.walk.support.tail := by
    intro j
    apply List.disjoint_left.mpr
    intro z hzBridge hzF
    have hzFsupport :
        z ∈ (F₂.path j).walk.support := by
      have hz :
          z ∈ (F₂.path j).reverse.walk.support :=
        List.mem_of_mem_tail hzF
      simpa [SimplePath.reverse] using hz
    rcases hF₂support j z hzFsupport with
      hc | hzC₂
    · rcases hBridgeClass z hzBridge with
        hzU₁ | hzU₂ | ⟨q, hzq⟩
      · exact setup.c_not_old
          ⟨A₁.root₁.1.1, hzU₁.symm.trans hc⟩
      · exact setup.c_not_old
          ⟨A₂.root₁.1.1, hzU₂.symm.trans hc⟩
      · exact setup.c_not_old
          ⟨q.1, hzq.symm.trans hc⟩
    · rcases hBridgeClass z hzBridge with
        hzU₁ | hzU₂ | ⟨q, hzq⟩
      · exact hcomponentRangesDisjoint
          ⟨A₁.root₁, by
            simpa [OutsideComponent.hom] using hzU₁.symm⟩
          hzC₂
      · exact (F₂.path j).reverse.start_not_mem_tail
          (hzU₂ ▸ hzF)
      · obtain ⟨b, hb⟩ := hzC₂
        have hval : q.1 = b.1.1 :=
          setup.inclusion.injective
            (hzq.symm.trans hb.symm)
        exact b.1.2 (hval ▸ q.2)
  let right : AdmissiblePathFamily B
      (setup.inclusion A₁.root₁.1.1) c 3 := {
    start := F₂.start + bridge.length
    step := F₂.step
    admissible_step := F₂.admissible_step
    start_ge_two := F₂.start_ge_two.trans
      (Nat.le_add_right F₂.start bridge.length)
    path := fun j =>
      bridge.appendDisjoint (F₂.path j).reverse
        (hBridgeF₂disjoint j)
    length_path := by
      intro j
      rw [SimplePath.appendDisjoint_length,
        SimplePath.reverse_length, F₂.length_path]
      omega
  }
  have hF₁rightDisjoint :
      ∀ i j,
        (F₁.path i).walk.support.tail.Disjoint
          (right.path j).walk.support.tail := by
    intro i j
    apply List.disjoint_left.mpr
    intro z hzF₁ hzRight
    change z ∈
      (bridge.walk.append
        (F₂.path j).reverse.walk).support.tail
          at hzRight
    rw [SimpleGraph.Walk.tail_support_append]
      at hzRight
    rcases List.mem_append.mp hzRight with
      hzBridge | hzF₂
    · have hzF₁support :=
        List.mem_of_mem_tail hzF₁
      rcases hF₁support i z hzF₁support with
        hc | hzC₁
      · exact F₁.path i |>.start_not_mem_tail
          (hc ▸ hzF₁)
      · rcases hBridgeClass z
            (List.mem_of_mem_tail hzBridge) with
          hzU₁ | hzU₂ | ⟨q, hzq⟩
        · exact bridge.start_not_mem_tail
            (hzU₁ ▸ hzBridge)
        · exact hcomponentRangesDisjoint hzC₁
            ⟨A₂.root₁, by
              simpa [OutsideComponent.hom] using
                hzU₂.symm⟩
        · obtain ⟨a, ha⟩ := hzC₁
          have hval : a.1.1 = q.1 :=
            setup.inclusion.injective
              (ha.trans hzq)
          exact a.1.2 (hval ▸ q.2)
    · have hzF₁support :=
        List.mem_of_mem_tail hzF₁
      have hzF₂support :
          z ∈ (F₂.path j).walk.support := by
        have hz :
            z ∈ (F₂.path j).reverse.walk.support :=
          List.mem_of_mem_tail hzF₂
        simpa [SimplePath.reverse] using hz
      rcases hF₁support i z hzF₁support with
        hc₁ | hzC₁
      · exact F₁.path i |>.start_not_mem_tail
          (hc₁ ▸ hzF₁)
      · rcases hF₂support j z hzF₂support with
          hc₂ | hzC₂
        · exact F₁.path i |>.start_not_mem_tail
            (hc₂ ▸ hzF₁)
        · exact hcomponentRangesDisjoint hzC₁ hzC₂
  apply setup.no_divisible_cycle
  exact disjoint_three_by_three_forces_cycle_divisible_by_five
    B F₁ right hF₁rightDisjoint

/--
The light/mixed case in Lemma 7.2.  The Menger dependency supplies the two
vertex-disjoint interface links; all orientation, attachment, and
simple-cycle bookkeeping is internal.
-/
theorem StandingSetup.two_component_contradiction_of_light
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (C₁ C₂ :
      (outsideEnvelopeGraph T).ConnectedComponent)
    [Fintype C₁] [DecidableEq C₁]
    [Fintype C₂] [DecidableEq C₂]
    (hne : C₁ ≠ C₂)
    (A₁ : ComponentAttachmentPair T C₁)
    (A₂ : ComponentAttachmentPair T C₂)
    (hinterfaces :
      Disjoint ({A₁.interface₁, A₁.interface₂} :
        Finset W)
        ({A₂.interface₁, A₂.interface₂} :
          Finset W))
    (hlight :
      (OutsideComponent.rootedExceptions D A₁).card < 2 ∨
      (OutsideComponent.rootedExceptions D A₂).card < 2) :
    False := by
  classical
  let a₁₀ : (↑T.carrier : Set W) :=
    ⟨A₁.interface₁,
      (OutsideComponent.mem_interfaceBoundary
        C₁ A₁.interface₁).1 A₁.interface₁_mem |>.1⟩
  let a₁₁ : (↑T.carrier : Set W) :=
    ⟨A₁.interface₂,
      (OutsideComponent.mem_interfaceBoundary
        C₁ A₁.interface₂).1 A₁.interface₂_mem |>.1⟩
  let b₁₀ : (↑T.carrier : Set W) :=
    ⟨A₂.interface₁,
      (OutsideComponent.mem_interfaceBoundary
        C₂ A₂.interface₁).1 A₂.interface₁_mem |>.1⟩
  let b₁₁ : (↑T.carrier : Set W) :=
    ⟨A₂.interface₂,
      (OutsideComponent.mem_interfaceBoundary
        C₂ A₂.interface₂).1 A₂.interface₂_mem |>.1⟩
  let AS : Finset (↑T.carrier : Set W) :=
    {a₁₀, a₁₁}
  let BS : Finset (↑T.carrier : Set W) :=
    {b₁₀, b₁₁}
  have hAScard : AS.card = 2 := by
    simp [AS, a₁₀, a₁₁, A₁.interfaces_ne]
  have hBScard : BS.card = 2 := by
    simp [BS, b₁₀, b₁₁, A₂.interfaces_ne]
  have hASBS : Disjoint AS BS := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    simp only [AS, BS, Finset.mem_insert,
      Finset.mem_singleton] at hzA hzB
    have hzA' :
        z.1 ∈ ({A₁.interface₁, A₁.interface₂} :
          Finset W) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hzA with hza | hza
      · left
        simpa [a₁₀] using congrArg Subtype.val hza
      · right
        simpa [a₁₁] using congrArg Subtype.val hza
    have hzB' :
        z.1 ∈ ({A₂.interface₁, A₂.interface₂} :
          Finset W) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hzB with hzb | hzb
      · left
        simpa [b₁₀] using congrArg Subtype.val hzb
      · right
        simpa [b₁₁] using congrArg Subtype.val hzb
    exact Finset.disjoint_left.mp hinterfaces hzA' hzB'
  obtain ⟨a₁, a₂, b₁, b₂,
      ha₁, ha₂, hb₁, hb₂, haNe, hbNe,
      L₁, L₂, hlinks⟩ :=
    ClassicalGraphTheory.two_disjoint_set_paths
      (J.induce (↑T.carrier : Set W))
      T.two_connected AS BS hAScard hBScard hASBS
  obtain ⟨O₁⟩ :=
    setup.orient_component_family T C₁ A₁
      a₁ a₂ (by simpa [AS] using ha₁)
      (by simpa [AS] using ha₂) haNe
  obtain ⟨O₂⟩ :=
    setup.orient_component_family T C₂ A₂
      b₁ b₂ (by simpa [BS] using hb₁)
      (by simpa [BS] using hb₂) hbNe
  let fT :
      J.induce (↑T.carrier : Set W) →g B := {
    toFun := fun z => setup.inclusion z.1
    map_rel' := by
      intro x y hxy
      exact setup.inclusion.toHom.map_rel' hxy
  }
  have hfT : Function.Injective fT := by
    intro x y hxy
    apply Subtype.ext
    exact setup.inclusion.injective hxy
  let Q₁ := L₁.mapInjectiveHom fT hfT
  let Q₂ := L₂.mapInjectiveHom fT hfT
  have hQ₁support :
      ∀ z ∈ Q₁.walk.support,
        ∃ q, q ∈ L₁.walk.support ∧
          z = setup.inclusion q.1 := by
    intro z hz
    change z ∈ (L₁.walk.map fT).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨q, hq, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨q, hq, rfl⟩
  have hQ₂support :
      ∀ z ∈ Q₂.walk.support,
        ∃ q, q ∈ L₂.walk.support ∧
          z = setup.inclusion q.1 := by
    intro z hz
    change z ∈ (L₂.walk.map fT).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨q, hq, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨q, hq, rfl⟩
  have hQdisjoint :
      Q₁.walk.support.Disjoint Q₂.walk.support := by
    apply List.disjoint_left.mpr
    intro z hz₁ hz₂
    obtain ⟨q₁, hq₁, hzq₁⟩ :=
      hQ₁support z hz₁
    obtain ⟨q₂, hq₂, hzq₂⟩ :=
      hQ₂support z hz₂
    have hqeq : q₁ = q₂ := by
      apply Subtype.ext
      exact setup.inclusion.injective
        (hzq₁.symm.trans hzq₂)
    exact List.disjoint_left.mp hlinks hq₁
      (hqeq ▸ hq₂)
  have hcomponentRangesDisjoint :
      ∀ {z : V},
        z ∈ Set.range (OutsideComponent.hom setup T C₁) →
        z ∈ Set.range (OutsideComponent.hom setup T C₂) →
        False := by
    intro z hz₁ hz₂
    obtain ⟨x, hx⟩ := hz₁
    obtain ⟨y, hy⟩ := hz₂
    have hxy : x.1 = y.1 := by
      apply Subtype.ext
      exact setup.inclusion.injective
        (hx.trans hy.symm)
    have h₁ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff
        C₁ x.1).1 x.2
    have h₂ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff
        C₂ y.1).1 y.2
    apply hne
    calc
      C₁ =
          (outsideEnvelopeGraph T).connectedComponentMk
            x.1 := h₁.symm
      _ =
          (outsideEnvelopeGraph T).connectedComponentMk
            y.1 := congrArg
              (outsideEnvelopeGraph T).connectedComponentMk
              hxy
      _ = C₂ := h₂
  have ha₂NotF₁ :
      ∀ i, setup.inclusion a₂.1 ∉
        (O₁.family.path i).walk.support := by
    intro i hz
    rcases O₁.support i _ hz with hc | ⟨x, hx⟩
    · exact setup.c_not_old ⟨a₂.1, hc⟩
    · have hval : a₂.1 = x.1.1 :=
        (setup.inclusion.injective hx).symm
      exact x.1.2 (hval ▸ a₂.2)
  have hAdjA₂ :
      B.Adj
        (setup.inclusion O₁.rootY.1.1)
        (setup.inclusion a₂.1) :=
    setup.inclusion.toHom.map_rel' O₁.adjacentY
  let P₁ : Fin 3 → SimplePath B
      (setup.inclusion O₁.rootX.1.1)
      (setup.inclusion a₂.1) :=
    fun i => (O₁.family.path i).appendEdge
      hAdjA₂ (ha₂NotF₁ i)
  have hP₁Q₂disjoint :
      ∀ i,
        (P₁ i).walk.support.Disjoint
          Q₂.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro z hzP hzQ
    obtain ⟨q, hq, hzq⟩ :=
      hQ₂support z (List.mem_of_mem_tail hzQ)
    change z ∈
      ((O₁.family.path i).walk.concat hAdjA₂).support
        at hzP
    simp only [SimpleGraph.Walk.support_concat,
      List.mem_append, List.mem_singleton] at hzP
    rcases hzP with hzF | rfl
    · rcases O₁.support i z hzF with hc | ⟨x, hx⟩
      · exact setup.c_not_old
          ⟨q.1, hzq.symm.trans hc⟩
      · have hval : x.1.1 = q.1 :=
          setup.inclusion.injective
            (hx.trans hzq)
        exact x.1.2 (hval ▸ q.2)
    · exact Q₂.start_not_mem_tail hzQ
  let P₂ : Fin 3 → SimplePath B
      (setup.inclusion O₁.rootX.1.1)
      (setup.inclusion b₂.1) :=
    fun i => (P₁ i).appendDisjoint Q₂
      (hP₁Q₂disjoint i)
  have hbRootNotP₂ :
      ∀ i, setup.inclusion O₂.rootY.1.1 ∉
        (P₂ i).walk.support := by
    intro i hz
    change setup.inclusion O₂.rootY.1.1 ∈
      ((P₁ i).walk.append Q₂.walk).support at hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzP | hzQ
    · change setup.inclusion O₂.rootY.1.1 ∈
        ((O₁.family.path i).walk.concat hAdjA₂).support
          at hzP
      simp only [SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton] at hzP
      rcases hzP with hzF | hzA₂
      · rcases O₁.support i _ hzF with hc | hzC₁
        · exact setup.c_not_old
            ⟨O₂.rootY.1.1, hc⟩
        · exact hcomponentRangesDisjoint hzC₁
            ⟨O₂.rootY, rfl⟩
      · have hval : O₂.rootY.1.1 = a₂.1 :=
          setup.inclusion.injective hzA₂
        exact O₂.rootY.1.2 (hval ▸ a₂.2)
    · obtain ⟨q, -, hzq⟩ :=
        hQ₂support _ (List.mem_of_mem_tail hzQ)
      have hval : O₂.rootY.1.1 = q.1 :=
        setup.inclusion.injective hzq
      exact O₂.rootY.1.2 (hval ▸ q.2)
  have hAdjB₂ :
      B.Adj (setup.inclusion b₂.1)
        (setup.inclusion O₂.rootY.1.1) :=
    (setup.inclusion.toHom.map_rel'
      O₂.adjacentY).symm
  let P₃ : Fin 3 → SimplePath B
      (setup.inclusion O₁.rootX.1.1)
      (setup.inclusion O₂.rootY.1.1) :=
    fun i => (P₂ i).appendEdge hAdjB₂
      (hbRootNotP₂ i)
  have hP₃F₂disjoint :
      ∀ i j,
        (P₃ i).walk.support.Disjoint
          (O₂.family.path j).reverse.walk.support.tail := by
    intro i j
    apply List.disjoint_left.mpr
    intro z hzP hzF
    have hzFsupport :
        z ∈ (O₂.family.path j).walk.support := by
      have hz :
          z ∈ (O₂.family.path j).reverse.walk.support :=
        List.mem_of_mem_tail hzF
      simpa [SimplePath.reverse] using hz
    rcases O₂.support j z hzFsupport with hc | hzC₂
    · rcases hlight with hsmall₁ | hsmall₂
      · have hcNotP : c ∉ (P₃ i).walk.support := by
          intro hcP
          change c ∈
            ((P₂ i).walk.concat hAdjB₂).support at hcP
          simp only [SimpleGraph.Walk.support_concat,
            List.mem_append, List.mem_singleton] at hcP
          rcases hcP with hcP₂ | hcRoot
          · change c ∈
              ((P₁ i).walk.append Q₂.walk).support
                at hcP₂
            rw [SimpleGraph.Walk.support_append] at hcP₂
            rcases List.mem_append.mp hcP₂ with
              hcP₁ | hcQ
            · change c ∈
                ((O₁.family.path i).walk.concat
                  hAdjA₂).support at hcP₁
              simp only [SimpleGraph.Walk.support_concat,
                List.mem_append, List.mem_singleton] at hcP₁
              rcases hcP₁ with hcF | hcA
              · exact O₁.avoid_c hsmall₁ i hcF
              · exact setup.c_not_old
                  ⟨a₂.1, hcA.symm⟩
            · obtain ⟨q, -, hcq⟩ :=
                hQ₂support c
                  (List.mem_of_mem_tail hcQ)
              exact setup.c_not_old
                ⟨q.1, hcq.symm⟩
          · exact setup.c_not_old
              ⟨O₂.rootY.1.1, hcRoot.symm⟩
        exact hcNotP (hc ▸ hzP)
      · exact O₂.avoid_c hsmall₂ j
          (hc ▸ hzFsupport)
    · change z ∈
        ((P₂ i).walk.concat hAdjB₂).support at hzP
      simp only [SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton] at hzP
      rcases hzP with hzP₂ | hzRoot
      · change z ∈
          ((P₁ i).walk.append Q₂.walk).support at hzP₂
        rw [SimpleGraph.Walk.support_append] at hzP₂
        rcases List.mem_append.mp hzP₂ with
          hzP₁ | hzQ
        · change z ∈
            ((O₁.family.path i).walk.concat hAdjA₂).support
              at hzP₁
          simp only [SimpleGraph.Walk.support_concat,
            List.mem_append, List.mem_singleton] at hzP₁
          rcases hzP₁ with hzF₁ | hzA₂
          · rcases O₁.support i z hzF₁ with hc | hzC₁
            · exact OutsideComponent.c_not_range_hom
                setup T C₂ (hc ▸ hzC₂)
            · exact hcomponentRangesDisjoint hzC₁ hzC₂
          · obtain ⟨x, hx⟩ := hzC₂
            have hval : a₂.1 = x.1.1 :=
              setup.inclusion.injective
                (hzA₂.symm.trans hx.symm)
            exact x.1.2 (hval ▸ a₂.2)
        · obtain ⟨q, -, hzq⟩ :=
            hQ₂support z
              (List.mem_of_mem_tail hzQ)
          obtain ⟨x, hx⟩ := hzC₂
          have hval : q.1 = x.1.1 :=
            setup.inclusion.injective
              (hzq.symm.trans hx.symm)
          exact x.1.2 (hval ▸ q.2)
      · exact (O₂.family.path j).reverse.start_not_mem_tail
          (hzRoot ▸ hzF)
  let side : Fin 3 → Fin 3 → SimplePath B
      (setup.inclusion O₁.rootX.1.1)
      (setup.inclusion O₂.rootX.1.1) :=
    fun i j => (P₃ i).appendDisjoint
      (O₂.family.path j).reverse
      (hP₃F₂disjoint i j)
  have hRoot₂NotQ₁ :
      setup.inclusion O₂.rootX.1.1 ∉
        Q₁.reverse.walk.support := by
    intro hz
    have hzQ :
        setup.inclusion O₂.rootX.1.1 ∈ Q₁.walk.support := by
      simpa [SimplePath.reverse] using hz
    obtain ⟨q, -, hzq⟩ := hQ₁support _ hzQ
    have hval : O₂.rootX.1.1 = q.1 :=
      setup.inclusion.injective hzq
    exact O₂.rootX.1.2 (hval ▸ q.2)
  have hAdjB₁ :
      B.Adj
        (setup.inclusion O₂.rootX.1.1)
        (setup.inclusion b₁.1) :=
    setup.inclusion.toHom.map_rel' O₂.adjacentX
  let R₁ : SimplePath B
      (setup.inclusion O₂.rootX.1.1)
      (setup.inclusion a₁.1) :=
    Q₁.reverse.prependEdge hAdjB₁ hRoot₂NotQ₁
  have hRoot₁NotR₁ :
      setup.inclusion O₁.rootX.1.1 ∉
        R₁.walk.support := by
    intro hz
    change setup.inclusion O₁.rootX.1.1 ∈
      (Q₁.reverse.walk.cons hAdjB₁).support at hz
    simp only [SimpleGraph.Walk.support_cons,
      List.mem_cons] at hz
    rcases hz with hzRoot | hzQ
    · exact hcomponentRangesDisjoint
        ⟨O₁.rootX, rfl⟩
        ⟨O₂.rootX, hzRoot.symm⟩
    · have hzQ' :
          setup.inclusion O₁.rootX.1.1 ∈
            Q₁.walk.support := by
        simpa [SimplePath.reverse] using hzQ
      obtain ⟨q, -, hzq⟩ := hQ₁support _ hzQ'
      have hval : O₁.rootX.1.1 = q.1 :=
        setup.inclusion.injective hzq
      exact O₁.rootX.1.2 (hval ▸ q.2)
  have hAdjA₁ :
      B.Adj (setup.inclusion a₁.1)
        (setup.inclusion O₁.rootX.1.1) :=
    (setup.inclusion.toHom.map_rel'
      O₁.adjacentX).symm
  let returnPath : SimplePath B
      (setup.inclusion O₂.rootX.1.1)
      (setup.inclusion O₁.rootX.1.1) :=
    R₁.appendEdge hAdjA₁ hRoot₁NotR₁
  have hsideReturnDisjoint :
      ∀ i j,
        (side i j).walk.support.tail.Disjoint
          returnPath.walk.support.tail := by
    intro i j
    apply List.disjoint_left.mpr
    intro z hzSide hzReturn
    have hzReturnSupport :=
      List.mem_of_mem_tail hzReturn
    change z ∈
      ((Q₁.reverse.walk.cons hAdjB₁).concat
        hAdjA₁).support at hzReturnSupport
    simp only [SimpleGraph.Walk.support_concat,
      SimpleGraph.Walk.support_cons,
      List.mem_append, List.mem_cons] at hzReturnSupport
    rcases hzReturnSupport with
      (hzRoot₂ | hzQ₁) | hzRoot₁
    · exact returnPath.start_not_mem_tail
        (hzRoot₂ ▸ hzReturn)
    · have hzQ₁' :
          z ∈ Q₁.walk.support := by
        simpa [SimplePath.reverse] using hzQ₁
      change z ∈
        ((P₃ i).walk.append
          (O₂.family.path j).reverse.walk).support.tail
            at hzSide
      rw [SimpleGraph.Walk.tail_support_append] at hzSide
      rcases List.mem_append.mp hzSide with
        hzP₃ | hzF₂
      · have hzP₃' :=
          List.mem_of_mem_tail hzP₃
        change z ∈
          ((P₂ i).walk.concat hAdjB₂).support at hzP₃'
        simp only [SimpleGraph.Walk.support_concat,
          List.mem_append, List.mem_singleton] at hzP₃'
        rcases hzP₃' with hzP₂ | hzRootY₂
        · change z ∈
            ((P₁ i).walk.append Q₂.walk).support at hzP₂
          rw [SimpleGraph.Walk.support_append] at hzP₂
          rcases List.mem_append.mp hzP₂ with
            hzP₁ | hzQ₂
          · change z ∈
              ((O₁.family.path i).walk.concat
                hAdjA₂).support at hzP₁
            simp only [SimpleGraph.Walk.support_concat,
              List.mem_append, List.mem_singleton] at hzP₁
            rcases hzP₁ with hzF₁ | hzA₂
            · rcases O₁.support i z hzF₁ with hc | ⟨x, hx⟩
              · obtain ⟨q, -, hzq⟩ :=
                  hQ₁support z hzQ₁'
                exact setup.c_not_old
                  ⟨q.1, hzq.symm.trans hc⟩
              · obtain ⟨q, -, hzq⟩ :=
                  hQ₁support z hzQ₁'
                have hval : x.1.1 = q.1 :=
                  setup.inclusion.injective
                    (hx.trans hzq)
                exact x.1.2 (hval ▸ q.2)
            · have hzQ₂start :
                  z ∈ Q₂.walk.support := by
                rw [hzA₂]
                exact Q₂.walk.start_mem_support
              exact List.disjoint_left.mp hQdisjoint
                hzQ₁' hzQ₂start
          · exact List.disjoint_left.mp hQdisjoint
              hzQ₁' (List.mem_of_mem_tail hzQ₂)
        · obtain ⟨q, -, hzq⟩ :=
            hQ₁support z hzQ₁'
          have hval : O₂.rootY.1.1 = q.1 :=
            setup.inclusion.injective
              (hzRootY₂.symm.trans hzq)
          exact O₂.rootY.1.2 (hval ▸ q.2)
      · have hzF₂support :
            z ∈ (O₂.family.path j).walk.support := by
          have hz :
              z ∈ (O₂.family.path j).reverse.walk.support :=
            List.mem_of_mem_tail hzF₂
          simpa [SimplePath.reverse] using hz
        rcases O₂.support j z hzF₂support with hc | ⟨x, hx⟩
        · obtain ⟨q, -, hzq⟩ :=
            hQ₁support z hzQ₁'
          exact setup.c_not_old
            ⟨q.1, hzq.symm.trans hc⟩
        · obtain ⟨q, -, hzq⟩ :=
            hQ₁support z hzQ₁'
          have hval : x.1.1 = q.1 :=
            setup.inclusion.injective
              (hx.trans hzq)
          exact x.1.2 (hval ▸ q.2)
    · rcases hzRoot₁ with hzRoot₁ | hzNil
      · exact side i j |>.start_not_mem_tail
          (hzRoot₁ ▸ hzSide)
      · simp at hzNil
  have hsideLength :
      ∀ i j,
        (side i j).length =
          (O₁.family.path i).length +
            (O₂.family.path j).length +
              (Q₂.length + 2) := by
    intro i j
    simp [side, P₃, P₂, P₁,
      SimplePath.reverse_length]
    omega
  let grid : OffsetConcatenationGrid B
      O₁.family O₂.family :=
    OffsetConcatenationGrid.ofSidePaths
      B O₁.family O₂.family (Q₂.length + 2)
      side returnPath hsideLength
      hsideReturnDisjoint
  apply setup.no_divisible_cycle
  exact offset_three_by_three_forces_cycle_divisible_by_five
    B O₁.family O₂.family grid

/--
The complement `M` is nonempty because a vertex of `T` has ambient degree
at least four but internal degree at most three.
-/
theorem StandingSetup.outside_envelope_nonempty
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J) :
    Nonempty {v : W // v ∉ T.carrier} := by
  obtain ⟨x, hxT⟩ := T.nonempty
  let xT : (↑T.carrier : Set W) := ⟨x, hxT⟩
  by_contra hempty
  have hall : ∀ y : W, y ∈ T.carrier := by
    intro y
    by_contra hyT
    exact hempty ⟨⟨y, hyT⟩⟩
  have hinside :
      ∀ y, J.Adj x y →
        y ∈ (↑T.carrier : Set W) :=
    fun y _ => hall y
  have hdegree :=
    finiteDegree_le_induce J
      (↑T.carrier : Set W) xT hinside
  change
    finiteDegree J x ≤
      finiteDegree
        (J.induce (↑T.carrier : Set W)) xT
    at hdegree
  have hlower := setup.degree_at_least_four x
  have hupper := T.internal_degree_le_three xT
  omega

/--
Lemma 7.2: the complement `M` of the theta envelope is connected.

If it had two components, four distinct interface attachments give either
the light/mixed construction or the both-heavy construction above.  In
either case the resulting simple-cycle grid contains a cycle whose length
is divisible by five.
-/
theorem StandingSetup.outside_envelope_connected
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J) :
    (outsideEnvelopeGraph T).Connected := by
  classical
  let M := outsideEnvelopeGraph T
  letI : Nonempty {v : W // v ∉ T.carrier} :=
    setup.outside_envelope_nonempty T
  by_contra hconnected
  have hnotPreconnected : ¬M.Preconnected := by
    intro hpre
    exact hconnected {
      preconnected := by
        simpa [M] using hpre
      nonempty := setup.outside_envelope_nonempty T
    }
  unfold SimpleGraph.Preconnected at hnotPreconnected
  push Not at hnotPreconnected
  obtain ⟨u, v, huv⟩ := hnotPreconnected
  let C₁ : M.ConnectedComponent :=
    M.connectedComponentMk u
  let C₂ : M.ConnectedComponent :=
    M.connectedComponentMk v
  have hne : C₁ ≠ C₂ := by
    intro heq
    exact huv
      (SimpleGraph.ConnectedComponent.exact heq)
  obtain ⟨A₁, A₂, hinterfaces⟩ :=
    setup.exists_component_attachment_pairs
      T C₁ C₂ hne
  letI : Fintype C₁ := Fintype.ofFinite C₁
  letI : DecidableEq C₁ := Classical.decEq C₁
  letI : Fintype C₂ := Fintype.ofFinite C₂
  letI : DecidableEq C₂ := Classical.decEq C₂
  by_cases hlight :
      (OutsideComponent.rootedExceptions D A₁).card < 2 ∨
      (OutsideComponent.rootedExceptions D A₂).card < 2
  · exact setup.two_component_contradiction_of_light
      T C₁ C₂ hne A₁ A₂ hinterfaces hlight
  · apply setup.two_component_contradiction_of_heavy
      T C₁ C₂ hne A₁ A₂ hinterfaces
    · omega
    · omega

/--
Lemmas 7.1 and 7.2 together imply that `M` itself is 2-connected: once
`M` is connected, its unique connected-component graph is isomorphic to
`M`.
-/
theorem StandingSetup.outside_envelope_two_connected
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J) :
    IsTwoConnected (outsideEnvelopeGraph T) := by
  classical
  let M := outsideEnvelopeGraph T
  have hMconnected : M.Connected := by
    simpa [M] using setup.outside_envelope_connected T
  obtain ⟨u⟩ := hMconnected.nonempty
  let C : M.ConnectedComponent :=
    M.connectedComponentMk u
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  let e : M ≃g C.toSimpleGraph := {
    toFun := fun m => ⟨m, by
      show M.connectedComponentMk m = C
      simpa [C] using
        SimpleGraph.ConnectedComponent.sound
          (hMconnected m u)⟩
    invFun := fun z => z.1
    left_inv := by
      intro m
      rfl
    right_inv := by
      intro z
      apply Subtype.ext
      rfl
    map_rel_iff' := by
      intro a b
      rfl
  }
  apply isKConnected_of_iso e 2
  exact setup.outside_component_two_connected T C

/--
Every interface vertex has an attachment in `M`: otherwise all of its
ambient neighbors would lie in `T`, contradicting degrees four versus
three.
-/
theorem StandingSetup.exists_outside_envelope_neighbor
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (x : W) (hxT : x ∈ T.carrier) :
    ∃ x' : {v : W // v ∉ T.carrier},
      J.Adj x x'.1 := by
  by_contra hnone
  have hinside :
      ∀ y, J.Adj x y →
        y ∈ (↑T.carrier : Set W) := by
    intro y hxy
    by_contra hyT
    exact hnone ⟨⟨y, hyT⟩, hxy⟩
  let xT : (↑T.carrier : Set W) := ⟨x, hxT⟩
  have hdegree :=
    finiteDegree_le_induce J
      (↑T.carrier : Set W) xT hinside
  change
    finiteDegree J x ≤
      finiteDegree
        (J.induce (↑T.carrier : Set W)) xT
    at hdegree
  have hlower := setup.degree_at_least_four x
  have hupper := T.internal_degree_le_three xT
  omega

/--
Attachments of two distinct interface vertices are distinct because an
outside vertex has at most one neighbor in `T`.
-/
theorem ThetaEnvelope.outside_neighbors_ne
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W}
    (T : ThetaEnvelope J)
    (x y : W) (hxy : x ≠ y)
    (hxT : x ∈ T.carrier)
    (hyT : y ∈ T.carrier)
    (x' y' : {v : W // v ∉ T.carrier})
    (hxx' : J.Adj x x'.1)
    (hyy' : J.Adj y y'.1) :
    x' ≠ y' := by
  intro hroots
  have hval : x'.1 = y'.1 :=
    congrArg Subtype.val hroots
  have hsub :
      (↑({x, y} : Finset W) : Set W) ⊆
        J.neighborSet x'.1 ∩
          (↑T.carrier : Set W) := by
    intro z hz
    simp only [Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨hxx'.symm, hxT⟩
    · exact ⟨by simpa [hval] using hyy'.symm,
        hyT⟩
  have hlower :
      2 ≤ finiteBoundaryDegree J T.carrier x'.1 := by
    unfold finiteBoundaryDegree
    calc
      2 = ({x, y} : Finset W).card :=
        (Finset.card_pair hxy).symm
      _ =
          (↑({x, y} : Finset W) : Set W).ncard :=
        (Set.ncard_coe_finset _).symm
      _ ≤
          (J.neighborSet x'.1 ∩
            (↑T.carrier : Set W)).ncard :=
        Set.ncard_le_ncard hsub
  have hupper :=
    T.outside_boundary_degree_le_one x'.1 x'.2
  omega

/-- Deficient vertices represented on the complement subtype `M`. -/
def outsideEnvelopeDeficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (T : ThetaEnvelope J)
    (D : Finset W) :
    Finset {v : W // v ∉ T.carrier} :=
  Finset.univ.filter fun v => v.1 ∈ D

@[simp] theorem mem_outsideEnvelopeDeficient
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (T : ThetaEnvelope J)
    (D : Finset W)
    (v : {w : W // w ∉ T.carrier}) :
    v ∈ outsideEnvelopeDeficient T D ↔ v.1 ∈ D := by
  simp [outsideEnvelopeDeficient]

/-- The Lemma 3.3 exception set after excluding the two roots. -/
def outsideEnvelopeExceptions
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (T : ThetaEnvelope J)
    (D : Finset W)
    (x' y' : {v : W // v ∉ T.carrier}) :
    Finset {v : W // v ∉ T.carrier} :=
  (outsideEnvelopeDeficient T D).filter
    fun v => v ≠ x' ∧ v ≠ y'

@[simp] theorem mem_outsideEnvelopeExceptions
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (T : ThetaEnvelope J)
    (D : Finset W)
    (x' y' v : {w : W // w ∉ T.carrier}) :
    v ∈ outsideEnvelopeExceptions T D x' y' ↔
      v.1 ∈ D ∧ v ≠ x' ∧ v ≠ y' := by
  simp [outsideEnvelopeExceptions]

/-- Inclusion of the old complement graph into the ambient block. -/
def StandingSetup.outsideEnvelopeHom
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J) :
    outsideEnvelopeGraph T →g B where
  toFun v := setup.inclusion v.1
  map_rel' := by
    intro x y hxy
    exact setup.inclusion.toHom.map_rel' hxy

/--
Lemma 3.3 applied to `M-x'y'`, then mapped into the ambient block.
This is the path-family production step of Section 7.3.
-/
theorem StandingSetup.outside_envelope_admissible_paths
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (hMtwo : IsTwoConnected (outsideEnvelopeGraph T))
    (x' y' : {v : W // v ∉ T.carrier})
    (hroots : x' ≠ y') :
    AmbientRootLiftResult B c
      (setup.inclusion x'.1)
      (setup.inclusion y'.1) 3
      (Set.range (setup.outsideEnvelopeHom T))
      ((outsideEnvelopeExceptions T D x' y').card < 2) := by
  classical
  let M := outsideEnvelopeGraph T
  let A := M \ edge x' y'
  let DM := outsideEnvelopeDeficient T D
  let Z := outsideEnvelopeExceptions T D x' y'
  have hMle : M ≤ A ⊔ edge x' y' := by
    intro p q hpq
    by_cases hedge : (edge x' y').Adj p q
    · exact Or.inr hedge
    · exact Or.inl ⟨hpq, hedge⟩
  have hconn :
      IsTwoConnected (A ⊔ edge x' y') := by
    refine ⟨hMtwo.1, ?_⟩
    intro S hS
    apply (hMtwo.2 S hS).mono
    intro p q hpq
    exact hMle hpq
  have hnotadj : ¬A.Adj x' y' := by
    rintro ⟨_, hnotEdge⟩
    apply hnotEdge
    exact (SimpleGraph.edge_adj
      x' y' x' y').2
      ⟨Or.inl ⟨rfl, rfl⟩, hroots⟩
  have hZD : Z ⊆ DM := by
    intro z hz
    have hzData :=
      (mem_outsideEnvelopeExceptions
        T D x' y' z).1 hz
    exact (mem_outsideEnvelopeDeficient
      T D z).2 hzData.1
  have hxZ : x' ∉ Z := by
    simp [Z]
  have hyZ : y' ∉ Z := by
    simp [Z]
  have hdeg :
      ∀ z, z ≠ x' → z ≠ y' → z ∉ Z →
        4 ≤ finiteDegree A z := by
    intro z hzx hzy hzZ
    have hzNotD : z.1 ∉ D := by
      intro hzD
      exact hzZ
        ((mem_outsideEnvelopeExceptions
          T D x' y' z).2
          ⟨hzD, hzx, hzy⟩)
    have hzLower :=
      (setup.outside_envelope_degree_bounds
        T z).1 hzNotD
    change 4 ≤ finiteDegree M z at hzLower
    rw [finiteDegree_sdiff_edge_of_ne
      M x' y' z hzx hzy]
    exact hzLower
  have hdegZ :
      ∀ z ∈ Z, 3 ≤ finiteDegree A z := by
    intro z hz
    have hzData :=
      (mem_outsideEnvelopeExceptions
        T D x' y' z).1 hz
    have hzLower :=
      (setup.outside_envelope_degree_bounds
        T z).2 hzData.1
    change 3 ≤ finiteDegree M z at hzLower
    rw [finiteDegree_sdiff_edge_of_ne
      M x' y' z hzData.2.1 hzData.2.2]
    exact hzLower
  have horder : 4 ≤ Fintype.card
      {v : W // v ∉ T.carrier} := by
    have hxLower :
        3 ≤ finiteDegree M x' := by
      by_cases hxD : x'.1 ∈ D
      · exact
          (setup.outside_envelope_degree_bounds
            T x').2 hxD
      · exact
          ((setup.outside_envelope_degree_bounds
            T x').1 hxD).trans' (by omega)
    have hxUpper :=
      M.degree_lt_card_verts x'
    have hxEq :
        finiteDegree M x' = M.degree x' := by
      unfold finiteDegree SimpleGraph.degree
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [hxEq] at hxLower
    have hthree :
        3 < Fintype.card
          {v : W // v ∉ T.carrier} :=
      hxLower.trans_lt hxUpper
    omega
  have result :
      RootLiftResult A Z x' y' 3 := by
    apply root_lifting 3 A DM Z x' y'
    · omega
    · exact hroots
    · exact hnotadj
    · exact hconn
    · exact hZD
    · exact hxZ
    · exact hyZ
    · exact hdeg
    · exact hdegZ
    · intro _
      exact horder
  let f : A →g B := {
    toFun := fun z => setup.inclusion z.1
    map_rel' := by
      intro p q hpq
      exact setup.inclusion.toHom.map_rel' hpq.1
  }
  have mapped :=
    result.mapToAmbient f c
      (fun z hz =>
        setup.deficient_adjacent_to_c z.1
          ((mem_outsideEnvelopeExceptions
            T D x' y' z).1 hz |>.1))
      (by
        intro p q hpq
        apply Subtype.ext
        exact setup.inclusion.injective hpq)
      (by
        rintro ⟨z, hz⟩
        exact setup.c_not_old ⟨z.1, by
          simpa [f] using hz⟩)
  convert mapped using 1 <;>
    simp [f, A, M, Z,
      StandingSetup.outsideEnvelopeHom]
  rfl

/--
Section 7.3, conditional only on the already isolated structural conclusion
that `M` is 2-connected.  All attachment selection, endpoint
distinctness, Lemma 3.3 degree bookkeeping, ambient mapping, support
disjointness, and the final modulo-five selection are proved here.
-/
theorem StandingSetup.final_residue_contradiction_of_envelope
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (T : ThetaEnvelope J)
    (hMtwo : IsTwoConnected (outsideEnvelopeGraph T)) :
    False := by
  classical
  obtain ⟨x, y, hxy, insideJ, hinsideTheta,
      hresJ⟩ :=
    theta_three_distinct_zmod_paths
      J setup.girth_at_least_six T.theta
  have hinsideCarrier :
      ∀ i z, z ∈ (insideJ i).walk.support →
        z ∈ T.carrier := by
    intro i z hz
    exact T.theta_vertices_subset
      (T.theta.support_subset_verts_of_containsPath
        (insideJ i) hxy (hinsideTheta i) z hz)
  have hxT : x ∈ T.carrier :=
    hinsideCarrier 0 x
      (insideJ 0).walk.start_mem_support
  have hyT : y ∈ T.carrier :=
    hinsideCarrier 0 y
      (insideJ 0).walk.end_mem_support
  obtain ⟨x', hxx'J⟩ :=
    setup.exists_outside_envelope_neighbor
      T x hxT
  obtain ⟨y', hyy'J⟩ :=
    setup.exists_outside_envelope_neighbor
      T y hyT
  have hroots : x' ≠ y' :=
    T.outside_neighbors_ne x y hxy hxT hyT
      x' y' hxx'J hyy'J
  obtain ⟨outside, houtsideSupport, -⟩ :=
    setup.outside_envelope_admissible_paths
      T hMtwo x' y' hroots
  let inside : Fin 3 →
      SimplePath B (setup.inclusion x)
        (setup.inclusion y) :=
    fun i => (insideJ i).mapInjectiveHom
      setup.inclusion.toHom setup.inclusion.injective
  have hres :
      ∀ i j, i ≠ j →
        ((inside i).length : ZMod 5) ≠
          ((inside j).length : ZMod 5) := by
    intro i j hij
    simpa [inside] using hresJ i j hij
  have hxx'B :
      B.Adj (setup.inclusion x)
        (setup.inclusion x'.1) :=
    setup.inclusion.toHom.map_rel' hxx'J
  have hy'yB :
      B.Adj (setup.inclusion y'.1)
        (setup.inclusion y) :=
    (setup.inclusion.toHom.map_rel' hyy'J).symm
  have hxyB :
      setup.inclusion x ≠ setup.inclusion y :=
    setup.inclusion.injective.ne hxy
  have hxOutside :
      ∀ i, setup.inclusion x ∉
        (outside.path i).walk.support := by
    intro i hxSupport
    rcases houtsideSupport i (setup.inclusion x)
        hxSupport with hc | ⟨z, hz⟩
    · exact setup.c_not_old
        ⟨x, hc⟩
    · have hxz :
          x = z.1 :=
        setup.inclusion.injective hz.symm
      exact z.2 (hxz ▸ hxT)
  have hyOutside :
      ∀ i, setup.inclusion y ∉
        (outside.path i).walk.support := by
    intro i hySupport
    rcases houtsideSupport i (setup.inclusion y)
        hySupport with hc | ⟨z, hz⟩
    · exact setup.c_not_old
        ⟨y, hc⟩
    · have hyz :
          y = z.1 :=
        setup.inclusion.injective hz.symm
      exact z.2 (hyz ▸ hyT)
  have hinsideSupport :
      ∀ j z, z ∈ (inside j).walk.support →
        ∃ w : W, w ∈ T.carrier ∧
          z = setup.inclusion w := by
    intro j z hz
    change z ∈
      ((insideJ j).walk.map
        setup.inclusion.toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w, hw, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨w, hinsideCarrier j w hw, rfl⟩
  have hdisjoint :
      ∀ i j,
        ((outside.path i).attachEndpoints
          hxx'B hy'yB hxyB
          (hxOutside i) (hyOutside i)).walk.support.tail.Disjoint
          (inside j).reverse.walk.support.tail := by
    intro i j
    apply List.disjoint_left.mpr
    intro z hzOutside hzInside
    rw [SimplePath.attachEndpoints_tail_support]
      at hzOutside
    simp only [List.mem_append,
      List.mem_singleton] at hzOutside
    rcases hzOutside with hzPath | hzY
    · have hzInsideSupport :
          z ∈ (inside j).walk.support := by
        have hzReverse :
            z ∈ (inside j).reverse.walk.support :=
          List.mem_of_mem_tail hzInside
        simpa [SimplePath.reverse] using hzReverse
      obtain ⟨w, hwT, hzw⟩ :=
        hinsideSupport j z hzInsideSupport
      rcases houtsideSupport i z hzPath with
        rfl | ⟨m, hzm⟩
      · exact setup.c_not_old
          ⟨w, hzw.symm⟩
      · have hwm :
            w = m.1 :=
          setup.inclusion.injective
            (hzw.symm.trans hzm.symm)
        exact m.2 (hwm ▸ hwT)
    · subst z
      exact (inside j).reverse.start_not_mem_tail
        hzInside
  have hcycle :=
    final_residue_argument_of_attachments
      B outside inside hres hxx'B hy'yB hxyB
      hxOutside hyOutside hdisjoint
  exact setup.no_divisible_cycle hcycle

/--
Turn an isomorphism from an induced vertex set to the canonical
one-subdivision of `K₄` into the oriented copy consumed by the internally
proved subdivision-attachment lemma.
-/
def subdivisionCopyOfInducedIso
    {J : SimpleGraph W} (S : Finset W)
    (e : J.induce (↑S : Set W) ≃g
      oneSubdivisionK4) :
    SimpleGraph.Copy oneSubdivisionK4 J where
  toHom :=
    (SimpleGraph.Embedding.induce
      (G := J) (↑S : Set W)).toHom.comp
        e.symm.toHom
  injective' :=
    (SimpleGraph.Embedding.induce
      (G := J) (↑S : Set W)).injective.comp
        e.symm.injective

theorem range_subdivisionCopyOfInducedIso
    {J : SimpleGraph W} (S : Finset W)
    (e : J.induce (↑S : Set W) ≃g
      oneSubdivisionK4) :
    Set.range (subdivisionCopyOfInducedIso S e) =
      (↑S : Set W) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).2
  · intro hw
    let wS : (↑S : Set W) := ⟨w, hw⟩
    refine ⟨e wS, ?_⟩
    simp [subdivisionCopyOfInducedIso, wS]

instance oneSubdivisionK4DecidableAdj :
    DecidableRel oneSubdivisionK4.Adj := by
  intro a b
  cases a <;> cases b <;>
    simp only [oneSubdivisionK4] <;>
    infer_instance

/-- Every canonical subdivision vertex has degree at most three. -/
theorem oneSubdivisionK4_degree_le_three
    (v : Fin 4 ⊕ K4Edge) :
    oneSubdivisionK4.degree v ≤ 3 := by
  decide +revert

/--
The canonical one-subdivision of `K₄` is 2-connected.  This finite
verification is kernel-reduced with `decide`: after
deleting no vertex or one explicitly enumerated vertex, a fixed surviving
root reaches every other surviving vertex.
-/
theorem oneSubdivisionK4_two_connected :
    IsTwoConnected oneSubdivisionK4 := by
  classical
  constructor
  · decide
  · intro S hS
    have hcard : S.card = 0 ∨ S.card = 1 := by omega
    rcases hcard with hzero | hone
    · have hS : S = ∅ := Finset.card_eq_zero.mp hzero
      subst S
      rw [connected_iff_exists_forall_reachable]
      refine ⟨⟨Sum.inl 0, by simp⟩, ?_⟩
      rintro ⟨w, hw⟩
      fin_cases w <;> decide +revert
    · obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hone
      rw [connected_iff_exists_forall_reachable]
      let r : Fin 4 ⊕ K4Edge :=
        if z = Sum.inl 0 then Sum.inl 1 else Sum.inl 0
      have hr : r ≠ z := by
        simp only [r]
        split_ifs with hz
        · subst z
          decide
        · exact Ne.symm hz
      refine ⟨⟨r, by simpa using hr⟩, ?_⟩
      rintro ⟨w, hw⟩
      fin_cases z <;> fin_cases w <;> decide +revert

/-- Transfer the two elementary structural properties of the canonical
one-subdivision across the induced isomorphism. -/
theorem properties_of_induces_oneSubdivisionK4
    {J : SimpleGraph W} {S : Finset W}
    (hS : InducesOneSubdivisionK4 J S) :
    IsTwoConnected (J.induce (↑S : Set W)) ∧
      ∀ v : (↑S : Set W),
        finiteDegree (J.induce (↑S : Set W)) v ≤ 3 := by
  classical
  obtain ⟨e⟩ := hS
  constructor
  · exact isKConnected_of_iso e 2
      oneSubdivisionK4_two_connected
  · intro v
    have hdegree :=
      oneSubdivisionK4_degree_le_three (e v)
    have heq :
        finiteDegree
            (J.induce (↑S : Set W)) v =
          (J.induce (↑S : Set W)).degree v := by
      unfold finiteDegree SimpleGraph.degree
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [heq, ← e.degree_eq v]
    exact hdegree

/--
The second case in (7.1): once `T` induces a one-subdivision of `K₄`, a
further outside vertex with two distinct neighbors in `T` would give the
forbidden 5- or 10-cycle by the internally proved subdivision-attachment
lemma.
-/
theorem StandingSetup.outside_boundary_degree_le_one_of_subdivision
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (S : Finset W)
    (hsubdivision : InducesOneSubdivisionK4 J S) :
    ∀ z : W, z ∉ S →
      finiteBoundaryDegree J S z ≤ 1 := by
  classical
  obtain ⟨e⟩ := hsubdivision
  let K := subdivisionCopyOfInducedIso S e
  intro z hzS
  by_contra hdegree
  have hone :
      1 <
        (J.neighborSet z ∩
          (↑S : Set W)).ncard := by
    unfold finiteBoundaryDegree at hdegree
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard
      (s := J.neighborSet z ∩
        (↑S : Set W))).1 hone
  let aS : (↑S : Set W) := ⟨a, ha.2⟩
  let bS : (↑S : Set W) := ⟨b, hb.2⟩
  let ia : Fin 4 ⊕ K4Edge := e aS
  let ib : Fin 4 ⊕ K4Edge := e bS
  have hia : K ia = a := by
    simp [K, ia, aS,
      subdivisionCopyOfInducedIso]
  have hib : K ib = b := by
    simp [K, ib, bS,
      subdivisionCopyOfInducedIso]
  have hiab : ia ≠ ib := by
    intro hij
    exact hab (by
      rw [← hia, ← hib, hij])
  have hzRange : z ∉ Set.range K := by
    rw [show Set.range K = (↑S : Set W) by
      simpa [K] using
        range_subdivisionCopyOfInducedIso S e]
    exact hzS
  have hbad :=
    GHLM.outside_vertex_on_subdivided_K4
      J
      (fun C => (setup.girth_at_least_six C).trans'
        (by omega))
      K z hzRange ia ib hiab
      (by simpa [hia] using ha.1)
      (by simpa [hib] using hb.1)
  rcases hbad with hfive | hten
  · obtain ⟨C, hC⟩ := hfive
    exact setup.no_five_cycle C hC
  · obtain ⟨C, hC⟩ := hten
    exact setup.no_ten_cycle C hC

/--
Construct the interface in (7.1) from a minimum theta, once the two
elementary intrinsic facts about an induced theta (2-connectivity and
maximum degree three) have been supplied.

All use of GHLM Lemma 5.10 is visible here.  In the exceptional branch the
intrinsic facts are re-established independently from the certified
one-subdivision of `K₄`; they are not inherited from the original theta.
-/
theorem StandingSetup.exists_thetaEnvelope_of_minimum
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D)
    (H : Theta J) (hminimum : H.IsMinimumOrder) :
    Nonempty (ThetaEnvelope J) := by
  classical
  obtain ⟨hHinduced, hatMostOne, hsubdivision⟩ :=
    GHLM.minimum_theta_structure J
      setup.girth_at_least_six
      setup.no_ten_cycle H hminimum
  obtain ⟨hHtwo, hHdegree⟩ :=
    ClassicalGraphTheory.induced_theta_core_properties
      J H hHinduced
  by_cases hbad :
      ∃ z : W, z ∉ H.verts ∧
        2 ≤
          (J.neighborSet z ∩
            (↑H.verts : Set W)).ncard
  · obtain ⟨z, hzOutside, hzDegree⟩ := hbad
    let S : Finset W := insert z H.verts
    have hsub : InducesOneSubdivisionK4 J S := by
      simpa [S] using
        hsubdivision z hzOutside hzDegree
    obtain ⟨hStwo, hSdegree⟩ :=
      properties_of_induces_oneSubdivisionK4 hsub
    refine ⟨{
      carrier := S
      nonempty := ⟨z, by simp [S]⟩
      two_connected := hStwo
      internal_degree_le_three := hSdegree
      outside_boundary_degree_le_one :=
        setup.outside_boundary_degree_le_one_of_subdivision
          S hsub
      theta := H
      theta_vertices_subset := ?_
    }⟩
    intro w hw
    simp [S, hw]
  · refine ⟨{
      carrier := H.verts
      nonempty := ⟨H.x, H.x_mem_verts⟩
      two_connected := hHtwo
      internal_degree_le_three := hHdegree
      outside_boundary_degree_le_one := ?_
      theta := H
      theta_vertices_subset := Finset.Subset.rfl
    }⟩
    intro z hzOutside
    by_contra hlarge
    apply hbad
    refine ⟨z, hzOutside, ?_⟩
    unfold finiteBoundaryDegree at hlarge
    omega

/--
The complete construction of the interface `T` in (7.1).  Theta existence
uses only 2-connectivity and the standing degree lower bound; minimum order
is selected by well-ordering rather than by an additional choice axiom.
-/
theorem StandingSetup.exists_thetaEnvelope
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D) :
    Nonempty (ThetaEnvelope J) := by
  classical
  have hJtwo : IsTwoConnected J := by
    constructor
    · have horder := setup.three_connected.1
      omega
    · intro S hS
      exact setup.three_connected.2 S (by omega)
  have hWnonempty : Nonempty W := by
    rw [← Fintype.card_pos_iff]
    have horder := setup.three_connected.1
    omega
  let w : W := Classical.choice hWnonempty
  have htheta : Nonempty (Theta J) :=
    ClassicalGraphTheory.exists_theta_of_two_connected
      J hJtwo ⟨w,
        (setup.degree_at_least_four w).trans'
          (by omega)⟩
  obtain ⟨H, hminimum⟩ :=
    exists_minimum_order_theta htheta
  exact setup.exists_thetaEnvelope_of_minimum
    H hminimum

/--
The assembled contradiction of Sections 7.1--7.3.  Starting from the
standing counterexample data, construct the minimum-theta envelope, prove
its complement 2-connected by Lemmas 7.1 and 7.2, and invoke the final
modulo-five path argument.
-/
theorem StandingSetup.girth_six_case_contradiction
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}
    (setup : StandingSetup J B c D) :
    False := by
  obtain ⟨T⟩ := setup.exists_thetaEnvelope
  exact setup.final_residue_contradiction_of_envelope
    T (setup.outside_envelope_two_connected T)

end DeanK5
