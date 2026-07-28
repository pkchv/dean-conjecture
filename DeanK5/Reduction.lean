import DeanK5.GirthSixCase
import DeanK5.TwoConnectedCase
import DeanK5.Structural
import DeanK5.ClassicalGraphTheory
import DeanK5.EndLobeAttachments
import DeanK5.GHLMRootedInternal

/-!
# Rooted end-block reduction and completion (paper Sections 3 and 8)

This file completes the paper's Section 3 reduction and performs the final
assembly in Section 8.  The ordinary connected-component and end-block facts
are proved in `ClassicalGraphTheory`; the degree bookkeeping,
root-deletion argument, and construction of `StandingSetup` are internal.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {W : Type u} {V : Type v}

/--
The data obtained from a nontrivial end block before Lemmas 3.1 and 3.2
are applied.
-/
structure RootedBlockSetup
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    (J : SimpleGraph W) (B : SimpleGraph V) (c : V) where
  /-- The embedding of the root-deleted graph `J` into the ambient block `B`. -/
  inclusion : J ↪g B
  c_not_old : c ∉ Set.range inclusion
  vertex_decomposition :
    ∀ z : V, z = c ∨ z ∈ Set.range inclusion
  block_two_connected : IsTwoConnected B
  root_degree_lower : 2 ≤ finiteDegree B c
  old_degree_lower :
    ∀ w : W, 5 ≤ finiteDegree B (inclusion w)
  deleted_degree_lower :
    MinDegreeAtLeast J 4
  degree_four_adjacent_to_root :
    ∀ w : W, finiteDegree J w = 4 →
      B.Adj c (inclusion w)
  deleted_connected : J.Connected
  no_divisible_cycle : ¬ HasCycleDivisibleBy B 5

namespace RootedBlockSetup

variable [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V} {c : V}

/-- The vertices losing one degree when the root is deleted. -/
noncomputable def deficient
    (_R : RootedBlockSetup J B c) : Finset W := by
  classical
  exact Finset.univ.filter fun w =>
    finiteDegree J w = 4

@[simp] theorem mem_deficient
    (R : RootedBlockSetup J B c) (w : W) :
    w ∈ R.deficient ↔ finiteDegree J w = 4 := by
  classical
  simp [deficient]

/--
The root degree is at most four.  If it were at least five, the internally
proved two-connected minimum-degree-five case applied to the end block would
give a cycle of length divisible by five.
-/
theorem root_degree_upper
    (R : RootedBlockSetup J B c) :
    finiteDegree B c ≤ 4 := by
  by_contra hlarge
  have hdegree : MinDegreeAtLeast B 5 := by
    intro z
    rcases R.vertex_decomposition z with rfl | ⟨w, rfl⟩
    · omega
    · exact R.old_degree_lower w
  exact R.no_divisible_cycle
    (divisible_cycle_of_two_connected_min_degree_five_internal
      B R.block_two_connected hdegree)

/-- The deficient set injects into the root neighborhood. -/
theorem deficient_card_le_root_degree
    (R : RootedBlockSetup J B c) :
    R.deficient.card ≤ finiteDegree B c := by
  classical
  let f : W → V := R.inclusion
  have himage :
      R.deficient.image f ⊆
        (B.neighborSet c).toFinset := by
    intro z hz
    obtain ⟨w, hwD, rfl⟩ :=
      Finset.mem_image.mp hz
    rw [Set.mem_toFinset]
    exact R.degree_four_adjacent_to_root w
      ((R.mem_deficient w).1 hwD)
  calc
    R.deficient.card =
        (R.deficient.image f).card := by
      symm
      exact Finset.card_image_of_injective
        R.deficient R.inclusion.injective
    _ ≤ (B.neighborSet c).toFinset.card :=
      Finset.card_le_card himage
    _ = finiteDegree B c := by
      unfold finiteDegree
      rw [Set.ncard_eq_toFinset_card']

/-- Inclusion of an end block of `J` into the ambient block `B`. -/
def endLobeBlockHom
    (R : RootedBlockSetup J B c) (L : EndLobe J) :
    L.blockGraph →g B where
  toFun z := R.inclusion z.1
  map_rel' := by
    intro x y hxy
    exact R.inclusion.toHom.map_rel' hxy

theorem classify_range_endLobeBlockHom
    (R : RootedBlockSetup J B c) (L : EndLobe J)
    {z : V}
    (hz : z ∈ Set.range (R.endLobeBlockHom L)) :
    z = R.inclusion L.cut ∨
      ∃ x : W, x ∈ L.inner ∧
        z = R.inclusion x := by
  obtain ⟨a, rfl⟩ := hz
  rcases Finset.mem_insert.mp a.2 with
    ha | ha
  · exact Or.inl (by
      exact congrArg R.inclusion ha)
  · exact Or.inr ⟨a.1, ha, rfl⟩

/--
The rooted admissible-path theorem applied inside one end block of `J`,
then mapped to `B` and prefixed by its attachment edge to `c`.
-/
theorem endLobe_rooted_paths
    (R : RootedBlockSetup J B c)
    (L : EndLobe J)
    (x : (↑L.inner : Set W))
    (hcx : B.Adj c (R.inclusion x.1)) :
    ∃ F : AdmissiblePathFamily B c
        (R.inclusion L.cut) 3,
      ∀ i z, z ∈ (F.path i).walk.support →
        z = c ∨
          z ∈ Set.range (R.endLobeBlockHom L) := by
  classical
  let E := L.blockGraph
  let xE : L.blockCarrier :=
    ⟨x.1, Finset.mem_insert.mpr (Or.inr x.2)⟩
  let bE : L.blockCarrier :=
    ⟨L.cut, Finset.mem_insert_self _ _⟩
  let A := E \ edge xE bE
  have hroots : xE ≠ bE := by
    intro h
    have hxcut : x.1 = L.cut :=
      congrArg (fun z : L.blockCarrier => z.1) h
    exact L.cut_not_inner (hxcut ▸ x.2)
  have hEle : E ≤ A ⊔ edge xE bE := by
    intro p q hpq
    by_cases hedge : (edge xE bE).Adj p q
    · exact Or.inr hedge
    · exact Or.inl ⟨hpq, hedge⟩
  have hconn :
      IsTwoConnected (A ⊔ edge xE bE) := by
    refine ⟨L.block_two_connected.1, ?_⟩
    intro S hS
    apply (L.block_two_connected.2 S hS).mono
    intro p q hpq
    exact hEle hpq
  have hnotadj : ¬A.Adj xE bE := by
    rintro ⟨-, hnotEdge⟩
    apply hnotEdge
    exact (SimpleGraph.edge_adj
      xE bE xE bE).2
      ⟨Or.inl ⟨rfl, rfl⟩, hroots⟩
  have hdegree :
      ∀ z, z ≠ xE → z ≠ bE →
        4 ≤ finiteDegree A z := by
    intro z hzx hzb
    have hzInner : z.1 ∈ L.inner := by
      rcases Finset.mem_insert.mp z.2 with
        hzCut | hzInner
      · exact False.elim
          (hzb (Subtype.ext hzCut))
      · exact hzInner
    have hinside :
        ∀ y, J.Adj z.1 y →
          y ∈ L.blockCarrier := by
      intro y hzy
      rcases L.closed hzInner hzy with
        hyInner | rfl
      · exact Finset.mem_insert.mpr
          (Or.inr hyInner)
      · exact Finset.mem_insert_self _ _
    have hle :=
      finiteDegree_le_induce J
        L.blockCarrier z hinside
    have hlower := R.deleted_degree_lower z.1
    have hEdegree : 4 ≤ finiteDegree E z := by
      exact hlower.trans hle
    rw [finiteDegree_sdiff_edge_of_ne
      E xE bE z hzx hzb]
    exact hEdegree
  obtain ⟨F⟩ :=
    GHLM.rooted_admissible_paths_internal
      3 A xE bE (by omega) hroots
      hconn hdegree
  let f : A →g B := {
    toFun := fun z => R.inclusion z.1
    map_rel' := by
      intro p q hpq
      exact R.inclusion.toHom.map_rel' hpq.1
  }
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact R.inclusion.injective hpq
  let FM := F.mapInjectiveHom f hf
  have hcNotFM :
      ∀ i, c ∉ (FM.path i).walk.support := by
    intro i hc
    have hcRange :
        c ∈ Set.range f :=
      (F.path i).mem_range_of_mem_mapInjectiveHom_support
        f hf hc
    obtain ⟨a, ha⟩ := hcRange
    exact R.c_not_old ⟨a.1, ha⟩
  have hAdj :
      B.Adj c (f xE) := by
    simpa [f, xE] using hcx
  let FB : AdmissiblePathFamily B c
      (R.inclusion L.cut) 3 := {
    start := FM.start + 1
    step := FM.step
    admissible_step := FM.admissible_step
    start_ge_two := by
      have hstart := FM.start_ge_two
      omega
    path := fun i =>
      (FM.path i).prependEdge hAdj (hcNotFM i)
    length_path := by
      intro i
      rw [SimplePath.prependEdge_length,
        FM.length_path]
      omega
  }
  refine ⟨FB, ?_⟩
  intro i z hz
  change z ∈
    ((FM.path i).walk.cons hAdj).support at hz
  simp only [SimpleGraph.Walk.support_cons,
    List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact Or.inl rfl
  · right
    have hzRange :
        z ∈ Set.range f :=
      (F.path i).mem_range_of_mem_mapInjectiveHom_support
        f hf hz
    obtain ⟨a, rfl⟩ := hzRange
    exact ⟨a, rfl⟩

/--
Paper Lemma 3.1.  The two end-lobe attachments are the explicit
ordinary block-theory dependency; production of both admissible families,
all support intersections, and the simple-cycle contradiction are checked
here.
-/
theorem root_deletion_two_connected
    (R : RootedBlockSetup J B c) :
    IsTwoConnected J := by
  by_contra hnotTwo
  have hdegree : MinDegreeAtLeast J 3 := by
    intro w
    exact (R.deleted_degree_lower w).trans'
      (by omega)
  obtain ⟨P, x₁, x₂, hcx₁, hcx₂⟩ :=
    ClassicalGraphTheory.two_end_lobes_with_root_attachments
      J B c R.inclusion R.c_not_old
      R.vertex_decomposition R.block_two_connected
      R.deleted_connected hnotTwo hdegree
  obtain ⟨F₁, hF₁support⟩ :=
    R.endLobe_rooted_paths P.left x₁ hcx₁
  obtain ⟨F₂, hF₂support⟩ :=
    R.endLobe_rooted_paths P.right x₂ hcx₂
  let connector : SimplePath B
      (R.inclusion P.left.cut)
      (R.inclusion P.right.cut) :=
    P.connector.mapInjectiveHom
      R.inclusion.toHom R.inclusion.injective
  have hconnectorSupport :
      ∀ z ∈ connector.walk.support,
        ∃ r,
          r ∈ P.connector.walk.support ∧
          z = R.inclusion r := by
    intro z hz
    change z ∈
      (P.connector.walk.map
        R.inclusion.toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨r, hr, rfl⟩ :=
      List.mem_map.mp hz
    exact ⟨r, hr, rfl⟩
  have hblockIntersection :
      ∀ {z : V},
        z ∈ Set.range
          (R.endLobeBlockHom P.left) →
        z ∈ Set.range
          (R.endLobeBlockHom P.right) →
        z = R.inclusion P.left.cut ∧
          z = R.inclusion P.right.cut := by
    intro z hz₁ hz₂
    rcases R.classify_range_endLobeBlockHom
        P.left hz₁ with
      hzCut₁ | ⟨a, ha, hza⟩
    · rcases R.classify_range_endLobeBlockHom
          P.right hz₂ with
        hzCut₂ | ⟨b, hb, hzb⟩
      · exact ⟨hzCut₁, hzCut₂⟩
      · have hab : P.left.cut = b :=
          R.inclusion.injective
            (hzCut₁.symm.trans hzb)
        exact False.elim
          (P.left_cut_not_right_inner
            (hab ▸ hb))
    · rcases R.classify_range_endLobeBlockHom
          P.right hz₂ with
        hzCut₂ | ⟨b, hb, hzb⟩
      · have hab : a = P.right.cut :=
          R.inclusion.injective
            (hza.symm.trans hzCut₂)
        exact False.elim
          (P.right_cut_not_left_inner
            (hab ▸ ha))
      · have hab : a = b :=
          R.inclusion.injective
            (hza.symm.trans hzb)
        exact False.elim
          (Finset.disjoint_left.mp
            P.inner_disjoint ha (hab ▸ hb))
  have hconnectorF₂disjoint :
      ∀ j,
        connector.walk.support.Disjoint
          (F₂.path j).reverse.walk.support.tail := by
    intro j
    apply List.disjoint_left.mpr
    intro z hzConnector hzF
    obtain ⟨r, hr, hzr⟩ :=
      hconnectorSupport z hzConnector
    have hzFsupport :
        z ∈ (F₂.path j).walk.support := by
      have hz :
          z ∈ (F₂.path j).reverse.walk.support :=
        List.mem_of_mem_tail hzF
      simpa [SimplePath.reverse] using hz
    rcases hF₂support j z hzFsupport with
      rfl | hzBlock
    · exact R.c_not_old ⟨r, hzr.symm⟩
    · rcases R.classify_range_endLobeBlockHom
          P.right hzBlock with
        hzCut | ⟨b, hbInner, hzb⟩
      · exact (F₂.path j).reverse.start_not_mem_tail
          (hzCut ▸ hzF)
      · have hrb : r = b :=
          R.inclusion.injective
            (hzr.symm.trans hzb)
        exact P.connector_avoids_right b
          (hrb ▸ hr) hbInner
  let right : AdmissiblePathFamily B
      (R.inclusion P.left.cut) c 3 := {
    start := F₂.start + connector.length
    step := F₂.step
    admissible_step := F₂.admissible_step
    start_ge_two := by
      exact F₂.start_ge_two.trans
        (Nat.le_add_right F₂.start connector.length)
    path := fun j =>
      connector.appendDisjoint
        (F₂.path j).reverse
        (hconnectorF₂disjoint j)
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
      (connector.walk.append
        (F₂.path j).reverse.walk).support.tail
          at hzRight
    rw [SimpleGraph.Walk.tail_support_append]
      at hzRight
    rcases List.mem_append.mp hzRight with
      hzConnector | hzF₂
    · obtain ⟨r, hr, hzr⟩ :=
        hconnectorSupport z
          (List.mem_of_mem_tail hzConnector)
      have hzF₁support :=
        List.mem_of_mem_tail hzF₁
      rcases hF₁support i z hzF₁support with
        rfl | hzBlock
      · exact R.c_not_old ⟨r, hzr.symm⟩
      · rcases R.classify_range_endLobeBlockHom
            P.left hzBlock with
          hzCut | ⟨a, haInner, hza⟩
        · exact connector.start_not_mem_tail
            (hzCut ▸ hzConnector)
        · have hra : r = a :=
            R.inclusion.injective
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
      · exact (F₁.path i).start_not_mem_tail
          (hc₁ ▸ hzF₁)
      · rcases hF₂support j z hzF₂support with
          hc₂ | hzBlock₂
        · exact (F₁.path i).start_not_mem_tail
            (hc₂ ▸ hzF₁)
        · obtain ⟨-, hzCut₂⟩ :=
            hblockIntersection hzBlock₁ hzBlock₂
          exact (F₂.path j).reverse.start_not_mem_tail
            (hzCut₂ ▸ hzF₂)
  apply R.no_divisible_cycle
  exact disjoint_three_by_three_forces_cycle_divisible_by_five
    B F₁ right hF₁rightDisjoint

/-- A divisible cycle of `J` would map injectively into `B`. -/
theorem no_divisible_cycle_deleted
    (R : RootedBlockSetup J B c) :
    ¬ HasCycleDivisibleBy J 5 := by
  rintro ⟨C, hC⟩
  apply R.no_divisible_cycle
  refine ⟨C.mapInjectiveHom
      R.inclusion.toHom R.inclusion.injective, ?_⟩
  simpa using hC

/--
The complete Section 3 construction of the standing setup.  In particular,
the definition of `D`, its adjacency to `c`, its cardinality bound, and
3-connectivity of `J` are derived rather than assumed.
-/
noncomputable def toStandingSetup
    (R : RootedBlockSetup J B c) :
    StandingSetup J B c R.deficient := by
  classical
  have hJtwo := R.root_deletion_two_connected
  have hJno := R.no_divisible_cycle_deleted
  have hJthree :=
    root_deletion_is_three_connected
      J hJtwo R.deleted_degree_lower hJno
  exact {
    inclusion := R.inclusion
    c_not_old := R.c_not_old
    vertex_decomposition := R.vertex_decomposition
    degree_c_lower := fun _ => R.root_degree_lower
    deficient_adjacent_to_c := by
      intro d hd
      exact R.degree_four_adjacent_to_root d
        ((R.mem_deficient d).1 hd)
    degree_deficient := by
      intro d hd
      exact (R.mem_deficient d).1 hd
    degree_regular := by
      intro w hw
      have hlower := R.deleted_degree_lower w
      have hne : finiteDegree J w ≠ 4 := by
        intro heq
        exact hw ((R.mem_deficient w).2 heq)
      omega
    deficient_card := by
      exact R.deficient_card_le_root_degree.trans
        R.root_degree_upper
    three_connected := hJthree
    no_divisible_cycle := R.no_divisible_cycle
  }

/--
All of Sections 3--7 assembled for an extracted rooted end block.
-/
theorem contradiction
    (R : RootedBlockSetup J B c) :
    False :=
  R.toStandingSetup.girth_six_case_contradiction

end RootedBlockSetup

namespace EndLobe

/--
An ordinary end lobe, in a graph of minimum degree at least five with no
divisible cycle, supplies the pre-setup used by Section 3.
-/
noncomputable def toRootedBlockSetup
    {X : Type*} [Fintype X] [DecidableEq X]
    {G : SimpleGraph X}
    (L : EndLobe G)
    (hdegree : MinDegreeAtLeast G 5)
    (hno : ¬ HasCycleDivisibleBy G 5) :
    RootedBlockSetup
      (G.induce (↑L.inner : Set X))
      L.blockGraph
      (⟨L.cut, Finset.mem_insert_self _ _⟩ :
        L.blockCarrier) := by
  classical
  let innerSet : Set X := (↑L.inner : Set X)
  let blockSet : Set X :=
    (↑(insert L.cut L.inner) : Set X)
  have hsubset : innerSet ⊆ blockSet := by
    intro x hx
    exact Finset.mem_insert.mpr (Or.inr hx)
  let ι :
      G.induce innerSet ↪g
        G.induce blockSet :=
    G.induceHomOfLE hsubset
  let cB : blockSet :=
    ⟨L.cut, Finset.mem_insert_self _ _⟩
  refine {
    inclusion := ι
    c_not_old := ?_
    vertex_decomposition := ?_
    block_two_connected := ?_
    root_degree_lower := ?_
    old_degree_lower := ?_
    deleted_degree_lower := ?_
    degree_four_adjacent_to_root := ?_
    deleted_connected := ?_
    no_divisible_cycle := ?_
  }
  · rintro ⟨w, hw⟩
    have hwval : w.1 = L.cut := by
      exact congrArg Subtype.val hw
    exact L.cut_not_inner
      (hwval ▸ w.2)
  · intro z
    rcases Finset.mem_insert.mp z.2 with
      hzCut | hzInner
    · left
      apply Subtype.ext
      exact hzCut
    · right
      refine ⟨⟨z.1, hzInner⟩, ?_⟩
      apply Subtype.ext
      rfl
  · simpa [EndLobe.blockGraph, blockSet,
      EndLobe.blockCarrier] using
      L.block_two_connected
  · apply ClassicalGraphTheory.degree_at_least_connectivity
      (G.induce blockSet) 2
      (by
        simpa [EndLobe.blockGraph, blockSet,
          EndLobe.blockCarrier] using
          L.block_two_connected)
  · intro w
    have hinside :
        ∀ y, G.Adj w.1 y → y ∈ blockSet := by
      intro y hwy
      rcases L.closed w.2 hwy with
        hyInner | rfl
      · exact Finset.mem_insert.mpr
          (Or.inr hyInner)
      · exact Finset.mem_insert_self _ _
    have hle :=
      finiteDegree_le_induce G blockSet
        (⟨w.1, hsubset w.2⟩ : blockSet)
        hinside
    exact (hdegree w.1).trans hle
  · intro w
    have houtside :
        ∀ y, G.Adj w.1 y →
          y ∉ innerSet → y = L.cut := by
      intro y hwy hyInner
      rcases L.closed w.2 hwy with
        hy | hy
      · exact False.elim (hyInner hy)
      · exact hy
    have hle :=
      finiteDegree_le_induce_add_one
        G innerSet w L.cut houtside
    have hlower := hdegree w.1
    change 4 ≤
      finiteDegree (G.induce innerSet) w
    omega
  · intro w hwDegree
    change finiteDegree
      (G.induce innerSet) w = 4 at hwDegree
    change
      (G.induce blockSet).Adj cB (ι w)
    change G.Adj L.cut w.1
    by_contra hnotAdj
    have hinside :
        ∀ y, G.Adj w.1 y →
          y ∈ innerSet := by
      intro y hwy
      rcases L.closed w.2 hwy with
        hyInner | hyCut
      · exact hyInner
      · subst y
        exact False.elim
          (hnotAdj hwy.symm)
    have hle :=
      finiteDegree_le_induce G innerSet
        w hinside
    have hlower := hdegree w.1
    omega
  · simpa [innerSet] using L.inner_connected
  · rintro ⟨C, hC⟩
    apply hno
    let f : L.blockGraph →g G := {
      toFun := fun z => z.1
      map_rel' := by
        intro x y hxy
        exact hxy
    }
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext hxy
    refine ⟨C.mapInjectiveHom
        f hf, ?_⟩
    simpa using hC

end EndLobe

/-- The internally proved two-connected minimum-degree-five case. -/
theorem divisible_cycle_of_two_connected_min_degree_five
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X)
    (hconnected : IsTwoConnected G)
    (hdegree : MinDegreeAtLeast G 5) :
    HasCycleDivisibleBy G 5 :=
  divisible_cycle_of_two_connected_min_degree_five_internal
    G hconnected hdegree

/--
The paper's final theorem.

`Nonempty X` is explicit because the pointwise predicate
`MinDegreeAtLeast G 5` is vacuously true on an empty carrier.  This is the
formal counterpart of the conventional graph-theoretic assumption that a
graph with a stated minimum degree has a vertex.
-/
theorem dean_conjecture_k5
    {X : Type*} [Fintype X]
    [Nonempty X]
    (G : SimpleGraph X)
    (hdegree : MinDegreeAtLeast G 5) :
    HasCycleDivisibleBy G 5 := by
  classical
  by_contra hno
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let C : G.ConnectedComponent :=
    G.connectedComponentMk x
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  let H := C.toSimpleGraph
  have hHdegree : MinDegreeAtLeast H 5 := by
    intro w
    have hinside :
        ∀ y, G.Adj w.1 y → y ∈ C.supp := by
      intro y hwy
      exact C.mem_supp_of_adj_mem_supp
        w.2 hwy
    have hle :=
      finiteDegree_le_induce G C.supp
        w hinside
    exact (hdegree w.1).trans hle
  have hHno : ¬ HasCycleDivisibleBy H 5 := by
    rintro ⟨K, hK⟩
    apply hno
    refine ⟨K.mapInjectiveHom
        C.toSimpleGraph_hom
        (by
          intro a b hab
          exact Subtype.ext hab), ?_⟩
    simpa using hK
  by_cases hHtwo : IsTwoConnected H
  · exact hHno
      (divisible_cycle_of_two_connected_min_degree_five
        H hHtwo hHdegree)
  · have hHthree : MinDegreeAtLeast H 3 := by
      intro w
      exact (hHdegree w).trans' (by omega)
    obtain ⟨P⟩ :=
      ClassicalGraphTheory.two_end_lobes
        H C.connected_toSimpleGraph
        hHtwo hHthree
    let R :=
      P.left.toRootedBlockSetup hHdegree hHno
    exact R.contradiction

end DeanK5
