import DeanK5.RootLifting
import DeanK5.ThreeSeparator
import DeanK5.Concatenation

/-!
# Standing assumptions for paper Sections 3--7

The paper repeatedly appeals to properties established in Section 3.
They are packaged here so later Lean theorems cannot use an unnamed standing
assumption.  A later reduction theorem must construct this structure from
the original counterexample.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {W : Type u} {V : Type v}

/--
The standing data derived from the rooted end-block reduction and used
throughout paper Sections 3--7.  It records the embedding into the ambient
block, the deficient vertices, the degree split, 3-connectivity, and the
counterexample hypothesis.
-/
structure StandingSetup
    [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    (J : SimpleGraph W) (B : SimpleGraph V)
    (c : V) (D : Finset W) where
  /-- The embedding of the root-deleted graph `J` into the ambient block `B`. -/
  inclusion : J ↪g B
  c_not_old : c ∉ Set.range inclusion
  vertex_decomposition :
    ∀ v : V, v = c ∨ v ∈ Set.range inclusion
  /--
  The ambient root has two neighbors whenever a deficient vertex is present.
  The implication permits the deficiency-free specialization to use an
  isolated bookkeeping root.
  -/
  degree_c_lower : D.Nonempty → 2 ≤ finiteDegree B c
  deficient_adjacent_to_c :
    ∀ d ∈ D, B.Adj c (inclusion d)
  degree_deficient :
    ∀ d ∈ D, finiteDegree J d = 4
  degree_regular :
    ∀ w ∉ D, 5 ≤ finiteDegree J w
  deficient_card : D.card ≤ 4
  three_connected : IsKConnected J 3
  no_divisible_cycle : ¬ HasCycleDivisibleBy B 5

namespace StandingSetup

variable [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}

theorem degree_at_least_four
    (setup : StandingSetup J B c D) (w : W) :
    4 ≤ finiteDegree J w := by
  by_cases hw : w ∈ D
  · rw [setup.degree_deficient w hw]
  · exact (setup.degree_regular w hw).trans' (by omega)

/-- Inclusion of a two-root component base into the ambient block. -/
def twoRootBaseHom
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y : W) :
    twoRootComponentBase J Q x y →g B where
  toFun w := setup.inclusion w.1
  map_rel' := by
    intro a b hab
    exact setup.inclusion.toHom.map_rel' hab.1

theorem twoRootBaseHom_injective
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y : W) :
    Function.Injective (setup.twoRootBaseHom Q x y) := by
  intro a b hab
  apply Subtype.ext
  exact setup.inclusion.injective hab

theorem c_not_range_twoRootBaseHom
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y : W) :
    c ∉ Set.range (setup.twoRootBaseHom Q x y) := by
  rintro ⟨w, hw⟩
  exact setup.c_not_old ⟨w.1, by
    simpa [twoRootBaseHom] using hw⟩

/-- Two disjoint component-side inclusions meet only at the two roots. -/
theorem ranges_meet_only_at_roots
    (setup : StandingSetup J B c D)
    (Q₀ Q₁ : Finset W) (x y : W)
    (hdisj : Disjoint Q₀ Q₁)
    {v : V}
    (hv₀ : v ∈ Set.range (setup.twoRootBaseHom Q₀ x y))
    (hv₁ : v ∈ Set.range (setup.twoRootBaseHom Q₁ x y)) :
    v = setup.inclusion x ∨ v = setup.inclusion y := by
  obtain ⟨a₀, rfl⟩ := hv₀
  obtain ⟨a₁, ha₁⟩ := hv₁
  have hval : a₀.1 = a₁.1 :=
    setup.inclusion.injective ha₁.symm
  let w := a₀.1
  have hw₀ : w = x ∨ w = y ∨ w ∈ Q₀ := by
    have h : w = x ∨ w = y ∨ w ∈ Q₀ := by
      simpa [w, twoRootVertices] using a₀.2
    exact h
  have hw₁ : w = x ∨ w = y ∨ w ∈ Q₁ := by
    have hmem : a₀.1 ∈ twoRootVertices Q₁ x y := by
      rw [hval]
      exact a₁.2
    simpa [w, twoRootVertices] using hmem
  by_cases hwx : w = x
  · exact Or.inl (by simp [w, hwx, twoRootBaseHom])
  by_cases hwy : w = y
  · exact Or.inr (by simp [w, hwy, twoRootBaseHom])
  have hwQ₀ : w ∈ Q₀ := by tauto
  have hwQ₁ : w ∈ Q₁ := by tauto
  exact False.elim (Finset.disjoint_left.mp hdisj hwQ₀ hwQ₁)

/-- Deficient inner vertices on one separator side. -/
def deficientInRegion
    (D Q : Finset W) (x y : W) :
    Finset (↑(twoRootVertices Q x y) : Set W) :=
  Finset.univ.filter fun w => w.1 ∈ D ∧ w.1 ∈ Q

omit [Fintype W] in
@[simp] theorem mem_deficientInRegion
    (D Q : Finset W) (x y : W)
    (w : (↑(twoRootVertices Q x y) : Set W)) :
    w ∈ deficientInRegion D Q x y ↔
      w.1 ∈ D ∧ w.1 ∈ Q := by
  simp [deficientInRegion]

omit [Fintype W] in
theorem card_deficientInRegion
    (D Q : Finset W) (x y : W) :
    (deficientInRegion D Q x y).card = (D ∩ Q).card := by
  let valEmbedding :
      (↑(twoRootVertices Q x y) : Set W) ↪ W :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have himage :
      (deficientInRegion D Q x y).map valEmbedding = D ∩ Q := by
    ext w
    constructor
    · intro hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hw
      exact Finset.mem_inter.mpr
        ((mem_deficientInRegion D Q x y a).1 ha)
    · intro hw
      obtain ⟨hwD, hwQ⟩ := Finset.mem_inter.mp hw
      let a : (↑(twoRootVertices Q x y) : Set W) :=
        ⟨w, by simp [twoRootVertices, hwQ]⟩
      exact Finset.mem_map.mpr
        ⟨a, (mem_deficientInRegion D Q x y a).2
          ⟨hwD, hwQ⟩, rfl⟩
  rw [← himage, Finset.card_map]

/--
The root-lifted three-path family on one component side of a three-separator.
This is the common construction used in Lemmas 4.2 and 4.3.
-/
theorem separator_side_admissible_paths
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ : ComponentRegion J {x, y, z} Q) :
    AmbientRootLiftResult B c
      (setup.inclusion x) (setup.inclusion y) 3
      (Set.range (setup.twoRootBaseHom Q x y))
      ((deficientInRegion D Q x y).card < 2) := by
  let A := twoRootComponentBase J Q x y
  let DA := deficientInRegion D Q x y
  let rx := twoRootX Q x y
  let ry := twoRootY Q x y
  have hScard : ({x, y, z} : Finset W).card = 3 := by
    simp [hxy, hxz, hyz]
  have hQcard : 2 ≤ Q.card :=
    hQ.two_le_card_of_three_separator hScard
      (fun q _ => setup.degree_at_least_four q)
  have hxQ : x ∉ Q := by
    intro hx
    exact hQ.not_mem_separator hx (by simp)
  have hyQ : y ∉ Q := by
    intro hy
    exact hQ.not_mem_separator hy (by simp)
  have horderA : 4 ≤ Fintype.card
      (↑(twoRootVertices Q x y) : Set W) := by
    have hdisj : Disjoint Q ({x, y} : Finset W) := by
      apply Finset.disjoint_left.mpr
      intro w hwQ hwroot
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwroot
      rcases hwroot with rfl | rfl
      · exact hxQ hwQ
      · exact hyQ hwQ
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Set.ncard_coe_finset, twoRootVertices,
      Finset.card_union_of_disjoint hdisj]
    simp [hxy]
    omega
  have hconnA :
      IsTwoConnected (A ⊔ edge rx ry) := by
    change IsTwoConnected
      (twoRootComponentBase J Q x y ⊔
        edge (twoRootX Q x y) (twoRootY Q x y))
    rw [twoRootComponentBase_sup_edge]
    exact one_component_two_separator_roots J Q x y z
      hxy hxz hyz hQ setup.three_connected
  have hnotadj : ¬ A.Adj rx ry := by
    intro h
    exact h.2 (by
      simpa [rx, ry, twoRootX, twoRootY, SimpleGraph.edge_adj]
        using hxy)
  have hxDA : rx ∉ DA := by
    intro h
    exact hxQ ((mem_deficientInRegion D Q x y rx).1 h).2
  have hyDA : ry ∉ DA := by
    intro h
    exact hyQ ((mem_deficientInRegion D Q x y ry).1 h).2
  have hinner :
      ∀ w : (↑(twoRootVertices Q x y) : Set W),
        w ≠ rx → w ≠ ry → w.1 ∈ Q := by
    intro w hwrx hwry
    have hwClass : w.1 = x ∨ w.1 = y ∨ w.1 ∈ Q := by
      simpa [twoRootVertices] using w.2
    rcases hwClass with hwx | hwy | hwQ
    · exact False.elim (hwrx (by
        apply Subtype.ext
        exact hwx))
    · exact False.elim (hwry (by
        apply Subtype.ext
        exact hwy))
    · exact hwQ
  have hdegA :
      ∀ w, w ≠ rx → w ≠ ry → w ∉ DA →
        3 + 1 ≤ finiteDegree A w := by
    intro w hwrx hwry hwDA
    have hwQ := hinner w hwrx hwry
    have hwD : w.1 ∉ D := by
      intro hwD
      exact hwDA ((mem_deficientInRegion D Q x y w).2
        ⟨hwD, hwQ⟩)
    have hJdeg := setup.degree_regular w.1 hwD
    have hloss :=
      finiteDegree_le_twoRootComponentBase_add_one
        J Q x y z w.1 hQ hwQ
    have hwEq :
        (⟨w.1, by simp [twoRootVertices, hwQ]⟩ :
          (↑(twoRootVertices Q x y) : Set W)) = w :=
      Subtype.ext rfl
    rw [hwEq] at hloss
    change 4 ≤ finiteDegree (twoRootComponentBase J Q x y) w
    omega
  have hdegDA :
      ∀ w ∈ DA, 3 ≤ finiteDegree A w := by
    intro w hwDA
    have hw := (mem_deficientInRegion D Q x y w).1 hwDA
    have hJdeg := setup.degree_deficient w.1 hw.1
    have hloss :=
      finiteDegree_le_twoRootComponentBase_add_one
        J Q x y z w.1 hQ hw.2
    have hwEq :
        (⟨w.1, by simp [twoRootVertices, hw.2]⟩ :
          (↑(twoRootVertices Q x y) : Set W)) = w :=
      Subtype.ext rfl
    rw [hwEq] at hloss
    change 3 ≤ finiteDegree (twoRootComponentBase J Q x y) w
    omega
  have lifted : RootLiftResult A DA rx ry 3 :=
    root_lifting 3 A DA DA rx ry
      (by omega)
      (by
        intro h
        exact hxy (congrArg Subtype.val h))
      hnotadj hconnA Finset.Subset.rfl hxDA hyDA
      hdegA hdegDA (fun _ => horderA)
  have mapped :=
    lifted.mapToAmbient
      (setup.twoRootBaseHom Q x y) c
      (fun d hd => by
        have hd' := (mem_deficientInRegion D Q x y d).1 hd
        exact setup.deficient_adjacent_to_c d.1 hd'.1)
      (setup.twoRootBaseHom_injective Q x y)
      (setup.c_not_range_twoRootBaseHom Q x y)
  simpa [AmbientRootLiftResult, StandingSetup.twoRootBaseHom,
    A, DA, rx, ry, twoRootX, twoRootY] using mapped

/--
Inclusion of the retained-third-root component graph into the ambient block.
The explicit fresh vertex is sent to the separator vertex `z`.
-/
noncomputable def threeRootBaseHom
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y z : W) :
    threeRootComponentBase J Q x y z →g B where
  toFun
    | none => setup.inclusion z
    | some w => setup.inclusion w.1
  map_rel' := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact False.elim hab
        | some w =>
            apply setup.inclusion.toHom.map_rel'
            exact (mem_thirdRootNeighbors J Q x y z w).1 hab
    | some u =>
        cases b with
        | none =>
            apply setup.inclusion.toHom.map_rel'
            exact ((mem_thirdRootNeighbors J Q x y z u).1 hab).symm
        | some w =>
            apply setup.inclusion.toHom.map_rel'
            exact hab.1

theorem threeRootBaseHom_injective
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y z : W)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ : ComponentRegion J {x, y, z} Q) :
    Function.Injective (setup.threeRootBaseHom Q x y z) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some w =>
          have hzw : z = w.1 := setup.inclusion.injective hab
          have hwclass : w.1 = x ∨ w.1 = y ∨ w.1 ∈ Q := by
            simpa [twoRootVertices] using w.2
          rcases hwclass with hwx | hwy | hwQ
          · exact False.elim (hxz (hwx.symm.trans hzw.symm))
          · exact False.elim (hyz (hwy.symm.trans hzw.symm))
          · exact False.elim
              (hQ.not_mem_separator hwQ (by simp [hzw]))
  | some u =>
      cases b with
      | none =>
          have huz : u.1 = z := setup.inclusion.injective hab
          have huclass : u.1 = x ∨ u.1 = y ∨ u.1 ∈ Q := by
            simpa [twoRootVertices] using u.2
          rcases huclass with hux | huy | huQ
          · exact False.elim (hxz (hux.symm.trans huz))
          · exact False.elim (hyz (huy.symm.trans huz))
          · exact False.elim
              (hQ.not_mem_separator huQ (by simp [huz]))
      | some w =>
          apply congrArg some
          apply Subtype.ext
          exact setup.inclusion.injective hab

theorem c_not_range_threeRootBaseHom
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y z : W) :
    c ∉ Set.range (setup.threeRootBaseHom Q x y z) := by
  rintro ⟨a, ha⟩
  cases a with
  | none =>
      exact setup.c_not_old ⟨z, by
        simpa [threeRootBaseHom] using ha⟩
  | some w =>
      exact setup.c_not_old ⟨w.1, by
        simpa [threeRootBaseHom] using ha⟩

/--
The ordinary side and the side retaining `z` meet only at their common
roots `x,y`.
-/
theorem twoRoot_threeRoot_ranges_meet_only_at_roots
    (setup : StandingSetup J B c D)
    (Q₀ Q₁ : Finset W) (x y z : W)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ₀ : ComponentRegion J {x, y, z} Q₀)
    (hdisj : Disjoint Q₀ Q₁)
    {v : V}
    (hv₀ : v ∈ Set.range (setup.twoRootBaseHom Q₀ x y))
    (hv₁ : v ∈ Set.range (setup.threeRootBaseHom Q₁ x y z)) :
    v = setup.inclusion x ∨ v = setup.inclusion y := by
  obtain ⟨a₁, ha₁⟩ := hv₁
  cases a₁ with
  | none =>
      obtain ⟨a₀, ha₀⟩ := hv₀
      have ha₀z : a₀.1 = z := by
        apply setup.inclusion.injective
        calc
          setup.inclusion a₀.1 = v := ha₀
          _ = setup.inclusion z := by
            simpa [threeRootBaseHom] using ha₁.symm
      have ha₀class : a₀.1 = x ∨ a₀.1 = y ∨ a₀.1 ∈ Q₀ := by
        simpa [twoRootVertices] using a₀.2
      rcases ha₀class with ha₀x | ha₀y | ha₀Q
      · exact False.elim (hxz (ha₀x.symm.trans ha₀z))
      · exact False.elim (hyz (ha₀y.symm.trans ha₀z))
      · exact False.elim
          (hQ₀.not_mem_separator ha₀Q (by simp [ha₀z]))
  | some a₁ =>
      have hv₁' :
          v ∈ Set.range (setup.twoRootBaseHom Q₁ x y) := by
        refine ⟨a₁, ?_⟩
        simpa [threeRootBaseHom, twoRootBaseHom] using ha₁
      exact setup.ranges_meet_only_at_roots
        Q₀ Q₁ x y hdisj hv₀ hv₁'

/--
The second path family in Lemma 4.3.  Here `z` is retained and supplied
directly to the one-exception theorem; consequently none of these paths uses
the distinguished ambient root `c`.
-/
theorem separator_side_with_third_root_admissible_paths
    (setup : StandingSetup J B c D)
    (Q : Finset W) (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ : ComponentRegion J {x, y, z} Q)
    (hzneighbors : 2 ≤ (thirdRootNeighbors J Q x y z).card) :
    AmbientRootLiftResult B c
      (setup.inclusion x) (setup.inclusion y) 3
      (Set.range (setup.threeRootBaseHom Q x y z)) True := by
  let A := threeRootComponentBase J Q x y z
  let rx := threeRootX Q x y
  let ry := threeRootY Q x y
  have hconn : IsTwoConnected (A ⊔ edge rx ry) := by
    exact one_component_three_separator_roots
      J Q x y z hxy hxz hyz hQ setup.three_connected hzneighbors
  have horder : 4 ≤ Fintype.card
      (Option (↑(twoRootVertices Q x y) : Set W)) := by
    have hbaseOrder : 3 ≤ Fintype.card
        (↑(twoRootVertices Q x y) : Set W) :=
      (one_component_two_separator_roots
        J Q x y z hxy hxz hyz hQ setup.three_connected).1
    simp only [Fintype.card_option]
    omega
  have hroots : rx ≠ ry := by
    intro h
    exact hxy (by
      simpa [rx, ry, threeRootX, threeRootY, twoRootX, twoRootY]
        using h)
  have hdeg :
      ∀ v, v ≠ rx → v ≠ ry → v ≠ none →
        3 + 1 ≤ finiteDegree A v := by
    intro v hvrx hvry hvnone
    cases v with
    | none => exact False.elim (hvnone rfl)
    | some w =>
        have hwx : w ≠ twoRootX Q x y := by
          intro hw
          exact hvrx (by simp [rx, threeRootX, hw])
        have hwy : w ≠ twoRootY Q x y := by
          intro hw
          exact hvry (by simp [ry, threeRootY, hw])
        have hwclass : w.1 = x ∨ w.1 = y ∨ w.1 ∈ Q := by
          simpa [twoRootVertices] using w.2
        have hwQ : w.1 ∈ Q := by
          rcases hwclass with hwx' | hwy' | hwQ
          · exact False.elim (hwx (by
              apply Subtype.ext
              simpa [twoRootX] using hwx'))
          · exact False.elim (hwy (by
              apply Subtype.ext
              simpa [twoRootY] using hwy'))
          · exact hwQ
        exact (setup.degree_at_least_four w.1).trans
          (finiteDegree_le_threeRootComponentBase_inner
            J Q x y z w.1 hQ hwQ)
  obtain ⟨F⟩ :=
    COY.one_exception_rooted_paths 3 A rx ry none
      (by omega) horder hroots hconn hdeg
  let φ := setup.threeRootBaseHom Q x y z
  have hφ : Function.Injective φ :=
    setup.threeRootBaseHom_injective Q x y z hxz hyz hQ
  let F' := F.mapInjectiveHom φ hφ
  refine ⟨F', ?_, ?_⟩
  · intro i v hv
    right
    have hv' := hv
    change v ∈ ((F.path i).walk.map φ).support at hv'
    rw [SimpleGraph.Walk.support_map] at hv'
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv'
    exact ⟨w, rfl⟩
  · intro _ i hcSupport
    have hcSupport' := hcSupport
    change c ∈ ((F.path i).walk.map φ).support at hcSupport'
    rw [SimpleGraph.Walk.support_map] at hcSupport'
    obtain ⟨w, -, hφw⟩ := List.mem_map.mp hcSupport'
    exact setup.c_not_range_threeRootBaseHom Q x y z
      ⟨w, hφw⟩

/--
The path-concatenation contradiction in Lemma 4.3 once the retained
separator vertex has two neighbours on the second component side.
-/
theorem three_separator_contradiction_of_two_neighbors
    (setup : StandingSetup J B c D)
    (Q₀ Q₁ : Finset W) (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ₀ : ComponentRegion J {x, y, z} Q₀)
    (hQ₁ : ComponentRegion J {x, y, z} Q₁)
    (hdisjQ : Disjoint Q₀ Q₁)
    (hzneighbors : 2 ≤ (thirdRootNeighbors J Q₁ x y z).card) :
    False := by
  obtain ⟨F₀, hsupp₀, -⟩ :=
    setup.separator_side_admissible_paths Q₀ x y z
      hxy hxz hyz hQ₀
  obtain ⟨F₁, hsupp₁, havoid₁⟩ :=
    setup.separator_side_with_third_root_admissible_paths
      Q₁ x y z hxy hxz hyz hQ₁ hzneighbors
  let F₁r := F₁.reverse
  have hpathsDisjoint :
      ∀ i j,
        (F₀.path i).walk.support.tail.Disjoint
          (F₁r.path j).walk.support.tail := by
    intro i j
    rw [List.disjoint_left]
    intro v hv₀ hv₁
    have hv₀full : v ∈ (F₀.path i).walk.support :=
      List.mem_of_mem_tail hv₀
    have hv₁full : v ∈ (F₁.path j).walk.support := by
      have hvrev :
          v ∈ (F₁.path j).reverse.walk.support :=
        List.mem_of_mem_tail (by
          simpa [F₁r, AdmissiblePathFamily.reverse] using hv₁)
      simpa [SimplePath.reverse, SimpleGraph.Walk.support_reverse] using hvrev
    have hv₀allowed := hsupp₀ i v hv₀full
    have hv₁allowed := hsupp₁ j v hv₁full
    have hv₁range :
        v ∈ Set.range (setup.threeRootBaseHom Q₁ x y z) := by
      rcases hv₁allowed with hvc | hvrange
      · exact False.elim (havoid₁ trivial j (hvc ▸ hv₁full))
      · exact hvrange
    rcases hv₀allowed with hvc | hv₀range
    · exact False.elim
        (setup.c_not_range_threeRootBaseHom Q₁ x y z
          (hvc ▸ hv₁range))
    · have hroot :=
        setup.twoRoot_threeRoot_ranges_meet_only_at_roots
          Q₀ Q₁ x y z hxz hyz hQ₀ hdisjQ hv₀range hv₁range
      rcases hroot with hvx | hvy
      · exact (F₀.path i).start_not_mem_tail (hvx ▸ hv₀)
      · have hstart :=
          (F₁.path j).reverse.start_not_mem_tail
        apply hstart
        simpa [F₁r, AdmissiblePathFamily.reverse, hvy] using hv₁
  have hcycle :=
    disjoint_three_by_three_forces_cycle_divisible_by_five
      B F₀ F₁r hpathsDisjoint
  exact setup.no_divisible_cycle hcycle

/--
Main contradiction in paper Lemma 4.2: if one component behind a
three-separator contains at most one deficient vertex, a second component
supplies the other three-path family and the two sides form a divisible
cycle.
-/
theorem component_contains_two_deficient_of_other_component
    (setup : StandingSetup J B c D)
    (Q₀ Q₁ : Finset W) (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hQ₀ : ComponentRegion J {x, y, z} Q₀)
    (hQ₁ : ComponentRegion J {x, y, z} Q₁)
    (hdisjQ : Disjoint Q₀ Q₁) :
    2 ≤ (deficientInRegion D Q₀ x y).card := by
  by_contra hsmall'
  have hsmall :
      (deficientInRegion D Q₀ x y).card < 2 := by
    omega
  obtain ⟨F₀, hsupp₀, havoid₀⟩ :=
    setup.separator_side_admissible_paths Q₀ x y z
      hxy hxz hyz hQ₀
  obtain ⟨F₁, hsupp₁, -⟩ :=
    setup.separator_side_admissible_paths Q₁ x y z
      hxy hxz hyz hQ₁
  let F₁r := F₁.reverse
  have hpathsDisjoint :
      ∀ i j,
        (F₀.path i).walk.support.tail.Disjoint
          (F₁r.path j).walk.support.tail := by
    intro i j
    rw [List.disjoint_left]
    intro v hv₀ hv₁
    have hv₀full : v ∈ (F₀.path i).walk.support :=
      List.mem_of_mem_tail hv₀
    have hv₁full : v ∈ (F₁.path j).walk.support := by
      have hvrev :
          v ∈ (F₁.path j).reverse.walk.support :=
        List.mem_of_mem_tail (by
          simpa [F₁r, AdmissiblePathFamily.reverse] using hv₁)
      simpa [SimplePath.reverse, SimpleGraph.Walk.support_reverse] using hvrev
    have hv₀allowed := hsupp₀ i v hv₀full
    have hv₁allowed := hsupp₁ j v hv₁full
    have hv₀range :
        v ∈ Set.range (setup.twoRootBaseHom Q₀ x y) := by
      rcases hv₀allowed with hvc | hvrange
      · exact False.elim (havoid₀ hsmall i (hvc ▸ hv₀full))
      · exact hvrange
    rcases hv₁allowed with hvc | hv₁range
    · exact False.elim (havoid₀ hsmall i (hvc ▸ hv₀full))
    · have hroot :=
        setup.ranges_meet_only_at_roots
          Q₀ Q₁ x y hdisjQ hv₀range hv₁range
      rcases hroot with hvx | hvy
      · exact (F₀.path i).start_not_mem_tail (hvx ▸ hv₀)
      · have hstart :=
          (F₁.path j).reverse.start_not_mem_tail
        apply hstart
        simpa [F₁r, AdmissiblePathFamily.reverse, hvy] using hv₁
  have hcycle :
      HasCycleDivisibleBy B 5 :=
    disjoint_three_by_three_forces_cycle_divisible_by_five
      B F₀ F₁r hpathsDisjoint
  exact setup.no_divisible_cycle hcycle

/-- First conclusion of paper Lemma 4.2 for actual deleted components. -/
theorem every_component_of_three_cut_contains_two_deficient
    (setup : StandingSetup J B c D)
    (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcut : IsVertexCut J {x, y, z})
    (C : (deleteVertices J {x, y, z}).ConnectedComponent) :
    2 ≤
      (deficientInRegion D
        (componentVertices J {x, y, z} C) x y).card := by
  obtain ⟨C', hC'⟩ := hcut.exists_other_component C
  let Q := componentVertices J {x, y, z} C
  let Q' := componentVertices J {x, y, z} C'
  have hQ : ComponentRegion J {x, y, z} Q :=
    componentRegion_componentVertices J {x, y, z} C
  have hQ' : ComponentRegion J {x, y, z} Q' :=
    componentRegion_componentVertices J {x, y, z} C'
  have hdisj : Disjoint Q Q' :=
    disjoint_componentVertices J {x, y, z} hC'.symm
  exact setup.component_contains_two_deficient_of_other_component
    Q Q' x y z hxy hxz hyz hQ hQ' hdisj

/-- The counting conclusion of Lemma 4.2: a three-cut has at most two components. -/
theorem three_cut_has_at_most_two_components
    (setup : StandingSetup J B c D)
    (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcut : IsVertexCut J {x, y, z})
    (C₀ C₁ C₂ :
      (deleteVertices J {x, y, z}).ConnectedComponent) :
    C₀ = C₁ ∨ C₀ = C₂ ∨ C₁ = C₂ := by
  by_contra hallne
  push Not at hallne
  let Q₀ := componentVertices J {x, y, z} C₀
  let Q₁ := componentVertices J {x, y, z} C₁
  let Q₂ := componentVertices J {x, y, z} C₂
  let A₀ := D ∩ Q₀
  let A₁ := D ∩ Q₁
  let A₂ := D ∩ Q₂
  have hA₀ : 2 ≤ A₀.card := by
    have h :=
      setup.every_component_of_three_cut_contains_two_deficient
        x y z hxy hxz hyz hcut C₀
    rw [card_deficientInRegion] at h
    exact h
  have hA₁ : 2 ≤ A₁.card := by
    have h :=
      setup.every_component_of_three_cut_contains_two_deficient
        x y z hxy hxz hyz hcut C₁
    rw [card_deficientInRegion] at h
    exact h
  have hA₂ : 2 ≤ A₂.card := by
    have h :=
      setup.every_component_of_three_cut_contains_two_deficient
        x y z hxy hxz hyz hcut C₂
    rw [card_deficientInRegion] at h
    exact h
  have hQ₀₁ : Disjoint Q₀ Q₁ :=
    disjoint_componentVertices J {x, y, z} hallne.1
  have hQ₀₂ : Disjoint Q₀ Q₂ :=
    disjoint_componentVertices J {x, y, z} hallne.2.1
  have hQ₁₂ : Disjoint Q₁ Q₂ :=
    disjoint_componentVertices J {x, y, z} hallne.2.2
  have hA₀₁ : Disjoint A₀ A₁ := by
    apply Finset.disjoint_left.mpr
    intro w hw₀ hw₁
    exact Finset.disjoint_left.mp hQ₀₁
      (Finset.mem_inter.mp hw₀).2
      (Finset.mem_inter.mp hw₁).2
  have hA₀₂ : Disjoint A₀ A₂ := by
    apply Finset.disjoint_left.mpr
    intro w hw₀ hw₂
    exact Finset.disjoint_left.mp hQ₀₂
      (Finset.mem_inter.mp hw₀).2
      (Finset.mem_inter.mp hw₂).2
  have hA₁₂ : Disjoint A₁ A₂ := by
    apply Finset.disjoint_left.mpr
    intro w hw₁ hw₂
    exact Finset.disjoint_left.mp hQ₁₂
      (Finset.mem_inter.mp hw₁).2
      (Finset.mem_inter.mp hw₂).2
  have hUnionDisj : Disjoint (A₀ ∪ A₁) A₂ := by
    apply Finset.disjoint_left.mpr
    intro w hw01 hw₂
    rcases Finset.mem_union.mp hw01 with hw₀ | hw₁
    · exact Finset.disjoint_left.mp hA₀₂ hw₀ hw₂
    · exact Finset.disjoint_left.mp hA₁₂ hw₁ hw₂
  let U := (A₀ ∪ A₁) ∪ A₂
  have hUcard : U.card = A₀.card + A₁.card + A₂.card := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hUnionDisj,
      Finset.card_union_of_disjoint hA₀₁]
  have hUsub : U ⊆ D := by
    intro w hw
    simp only [U, A₀, A₁, A₂, Finset.mem_union, Finset.mem_inter] at hw
    tauto
  have hUle : U.card ≤ D.card := Finset.card_le_card hUsub
  rw [hUcard] at hUle
  have hDcard : D.card ≤ 4 := setup.deficient_card
  omega

/--
Lemma 4.2, with all of its bookkeeping made explicit.

Deleting a three-vertex cut leaves exactly two components.  Each component
contains exactly two deficient vertices; these are all four deficient
vertices, and no deficient vertex lies in the separator.
-/
theorem three_separator_structure
    (setup : StandingSetup J B c D)
    (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcut : IsVertexCut J {x, y, z}) :
    ∃ C₀ C₁ : (deleteVertices J {x, y, z}).ConnectedComponent,
      C₀ ≠ C₁ ∧
      (∀ C : (deleteVertices J {x, y, z}).ConnectedComponent,
        C = C₀ ∨ C = C₁) ∧
      (D ∩ componentVertices J {x, y, z} C₀).card = 2 ∧
      (D ∩ componentVertices J {x, y, z} C₁).card = 2 ∧
      D.card = 4 ∧
      D =
        (D ∩ componentVertices J {x, y, z} C₀) ∪
        (D ∩ componentVertices J {x, y, z} C₁) ∧
      Disjoint D {x, y, z} := by
  obtain ⟨C₀, C₁, hCne⟩ := hcut
  let Q₀ := componentVertices J {x, y, z} C₀
  let Q₁ := componentVertices J {x, y, z} C₁
  let A₀ := D ∩ Q₀
  let A₁ := D ∩ Q₁
  have hcomponents :
      ∀ C : (deleteVertices J {x, y, z}).ConnectedComponent,
        C = C₀ ∨ C = C₁ := by
    intro C
    rcases setup.three_cut_has_at_most_two_components
        x y z hxy hxz hyz ⟨C₀, C₁, hCne⟩ C C₀ C₁ with
      hCC₀ | hCC₁ | hbad
    · exact Or.inl hCC₀
    · exact Or.inr hCC₁
    · exact False.elim (hCne hbad)
  have hA₀lower : 2 ≤ A₀.card := by
    have h :=
      setup.every_component_of_three_cut_contains_two_deficient
        x y z hxy hxz hyz ⟨C₀, C₁, hCne⟩ C₀
    rw [card_deficientInRegion] at h
    exact h
  have hA₁lower : 2 ≤ A₁.card := by
    have h :=
      setup.every_component_of_three_cut_contains_two_deficient
        x y z hxy hxz hyz ⟨C₀, C₁, hCne⟩ C₁
    rw [card_deficientInRegion] at h
    exact h
  have hQdisj : Disjoint Q₀ Q₁ :=
    disjoint_componentVertices J {x, y, z} hCne
  have hAdisj : Disjoint A₀ A₁ := by
    apply Finset.disjoint_left.mpr
    intro w hw₀ hw₁
    exact Finset.disjoint_left.mp hQdisj
      (Finset.mem_inter.mp hw₀).2
      (Finset.mem_inter.mp hw₁).2
  let U := A₀ ∪ A₁
  have hUcard : U.card = A₀.card + A₁.card := by
    exact Finset.card_union_of_disjoint hAdisj
  have hUsub : U ⊆ D := by
    intro w hw
    simp only [U, A₀, A₁, Finset.mem_union, Finset.mem_inter] at hw
    tauto
  have hUle : U.card ≤ D.card := Finset.card_le_card hUsub
  have hDle : D.card ≤ 4 := setup.deficient_card
  have hA₀card : A₀.card = 2 := by omega
  have hA₁card : A₁.card = 2 := by omega
  have hDcard : D.card = 4 := by omega
  have hDleU : D.card ≤ U.card := by omega
  have hUeqD : U = D :=
    Finset.eq_of_subset_of_card_le hUsub hDleU
  have hDseparator : Disjoint D {x, y, z} := by
    apply Finset.disjoint_left.mpr
    intro w hwD hwS
    have hwU : w ∈ U := by
      rw [hUeqD]
      exact hwD
    rcases Finset.mem_union.mp hwU with hwA₀ | hwA₁
    · exact (componentRegion_componentVertices
        J {x, y, z} C₀).not_mem_separator
          (Finset.mem_inter.mp hwA₀).2 hwS
    · exact (componentRegion_componentVertices
        J {x, y, z} C₁).not_mem_separator
          (Finset.mem_inter.mp hwA₁).2 hwS
  refine ⟨C₀, C₁, hCne, hcomponents, ?_, ?_, hDcard, ?_,
    hDseparator⟩
  · exact hA₀card
  · exact hA₁card
  · exact hUeqD.symm

/--
All neighbours of a separator vertex lie either at the other two separator
vertices or in one of the two deletion-components.  This is the precise
degree count used to select the retained root in Lemma 4.3.
-/
theorem finiteDegree_le_two_thirdRootNeighbor_sets
    (x y z : W)
    (C₀ C₁ : (deleteVertices J {x, y, z}).ConnectedComponent)
    (hcomponents :
      ∀ C : (deleteVertices J {x, y, z}).ConnectedComponent,
        C = C₀ ∨ C = C₁)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    finiteDegree J z ≤
      (thirdRootNeighbors J
        (componentVertices J {x, y, z} C₀) x y z).card +
      (thirdRootNeighbors J
        (componentVertices J {x, y, z} C₁) x y z).card := by
  classical
  let Q₀ := componentVertices J {x, y, z} C₀
  let Q₁ := componentVertices J {x, y, z} C₁
  let Z₀ := thirdRootNeighbors J Q₀ x y z
  let Z₁ := thirdRootNeighbors J Q₁ x y z
  let R₀ : Set W := Subtype.val '' (↑Z₀ : Set
    (↑(twoRootVertices Q₀ x y) : Set W))
  let R₁ : Set W := Subtype.val '' (↑Z₁ : Set
    (↑(twoRootVertices Q₁ x y) : Set W))
  have hcover : J.neighborSet z ⊆ R₀ ∪ R₁ := by
    intro w hzw
    by_cases hwS : w ∈ ({x, y, z} : Finset W)
    · have hwneZ : w ≠ z := by
        intro hwz
        subst w
        exact J.loopless.irrefl z hzw
      have hwroot : w = x ∨ w = y := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwS
        tauto
      left
      let a : (↑(twoRootVertices Q₀ x y) : Set W) :=
        ⟨w, by
          rcases hwroot with rfl | rfl <;>
            simp [twoRootVertices]⟩
      refine ⟨a, ?_, rfl⟩
      exact (mem_thirdRootNeighbors J Q₀ x y z a).2 hzw
    · let wdel : {v : W // v ∉ ({x, y, z} : Finset W)} :=
        ⟨w, hwS⟩
      let Cw :=
        (deleteVertices J {x, y, z}).connectedComponentMk wdel
      have hwCw : wdel ∈ Cw.supp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      rcases hcomponents Cw with hC₀ | hC₁
      · left
        have hwQ₀ : w ∈ Q₀ := by
          apply (mem_componentVertices_iff J {x, y, z} C₀ w).2
          refine ⟨hwS, ?_⟩
          simpa [Cw, hC₀] using hwCw
        let a : (↑(twoRootVertices Q₀ x y) : Set W) :=
          ⟨w, by simp [twoRootVertices, hwQ₀]⟩
        refine ⟨a, ?_, rfl⟩
        exact (mem_thirdRootNeighbors J Q₀ x y z a).2 hzw
      · right
        have hwQ₁ : w ∈ Q₁ := by
          apply (mem_componentVertices_iff J {x, y, z} C₁ w).2
          refine ⟨hwS, ?_⟩
          simpa [Cw, hC₁] using hwCw
        let a : (↑(twoRootVertices Q₁ x y) : Set W) :=
          ⟨w, by simp [twoRootVertices, hwQ₁]⟩
        refine ⟨a, ?_, rfl⟩
        exact (mem_thirdRootNeighbors J Q₁ x y z a).2 hzw
  calc
    finiteDegree J z =
        (J.neighborSet z).ncard := rfl
    _ ≤ (R₀ ∪ R₁).ncard :=
      Set.ncard_le_ncard hcover
    _ ≤ R₀.ncard + R₁.ncard :=
      Set.ncard_union_le R₀ R₁
    _ = Z₀.card + Z₁.card := by
      rw [show R₀.ncard = Z₀.card by
        simp [R₀, Set.ncard_image_of_injective _ Subtype.val_injective],
        show R₁.ncard = Z₁.card by
        simp [R₁, Set.ncard_image_of_injective _ Subtype.val_injective]]

/-- A three-vertex cut contradicts the two root-lifted path families. -/
theorem no_three_vertex_cut
    (setup : StandingSetup J B c D)
    (x y z : W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ IsVertexCut J {x, y, z} := by
  intro hcut
  obtain ⟨C₀, C₁, hCne, hcomponents, -, -, -, -, hDseparator⟩ :=
    setup.three_separator_structure x y z hxy hxz hyz hcut
  let Q₀ := componentVertices J {x, y, z} C₀
  let Q₁ := componentVertices J {x, y, z} C₁
  have hzD : z ∉ D := by
    intro hzD
    exact Finset.disjoint_left.mp hDseparator hzD (by simp)
  have hzdegree : 5 ≤ finiteDegree J z :=
    setup.degree_regular z hzD
  have hneighborBound :=
    finiteDegree_le_two_thirdRootNeighbor_sets
      x y z C₀ C₁ hcomponents hxy hxz hyz
  change finiteDegree J z ≤
      (thirdRootNeighbors J Q₀ x y z).card +
      (thirdRootNeighbors J Q₁ x y z).card at hneighborBound
  have hQ₀ : ComponentRegion J {x, y, z} Q₀ :=
    componentRegion_componentVertices J {x, y, z} C₀
  have hQ₁ : ComponentRegion J {x, y, z} Q₁ :=
    componentRegion_componentVertices J {x, y, z} C₁
  have hQdisj : Disjoint Q₀ Q₁ :=
    disjoint_componentVertices J {x, y, z} hCne
  by_cases hZ₀ :
      2 ≤ (thirdRootNeighbors J Q₀ x y z).card
  · exact setup.three_separator_contradiction_of_two_neighbors
      Q₁ Q₀ x y z hxy hxz hyz hQ₁ hQ₀ hQdisj.symm hZ₀
  · have hZ₁ :
        2 ≤ (thirdRootNeighbors J Q₁ x y z).card := by
      omega
    exact setup.three_separator_contradiction_of_two_neighbors
      Q₀ Q₁ x y z hxy hxz hyz hQ₀ hQ₁ hQdisj hZ₁

/-- Paper Lemma 4.3: the standing graph is 4-connected. -/
theorem four_connected
    (setup : StandingSetup J B c D) :
    IsKConnected J 4 := by
  classical
  have horder : 5 ≤ Fintype.card W := by
    have hpos : 0 < Fintype.card W := by
      have := setup.three_connected.1
      omega
    let w : W := Classical.choice (Fintype.card_pos_iff.mp hpos)
    have hwdegree : 4 ≤ finiteDegree J w :=
      setup.degree_at_least_four w
    have hwNotNeighbor : w ∉ J.neighborSet w :=
      J.loopless.irrefl w
    have hcardInsert :
        (insert w (J.neighborSet w)).ncard =
          finiteDegree J w + 1 := by
      rw [Set.ncard_insert_of_notMem hwNotNeighbor]
      rfl
    have hsub : insert w (J.neighborSet w) ⊆ (Set.univ : Set W) :=
      Set.subset_univ _
    have hle :=
      Set.ncard_le_ncard hsub
    rw [hcardInsert] at hle
    simp only [Set.ncard_univ] at hle
    rw [Nat.card_eq_fintype_card] at hle
    omega
  constructor
  · simpa using horder
  · intro S hScard
    by_cases hSsmall : S.card < 3
    · exact setup.three_connected.2 S hSsmall
    · have hSthree : S.card = 3 := by omega
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ :=
        Finset.card_eq_three.mp hSthree
      have hncut :=
        setup.no_three_vertex_cut x y z hxy hxz hyz
      have hexists :
          ∃ w : W, w ∉ ({x, y, z} : Finset W) := by
        by_contra h
        push Not at h
        have huniv : ({x, y, z} : Finset W) = Finset.univ :=
          Finset.eq_univ_of_forall h
        have hunivcard :
            Fintype.card W = 3 := by
          rw [← Finset.card_univ, ← huniv]
          simp [hxy, hxz, hyz]
        omega
      obtain ⟨w, hwS⟩ := hexists
      rw [connected_iff_exists_forall_reachable]
      refine ⟨⟨w, hwS⟩, ?_⟩
      intro v
      apply SimpleGraph.ConnectedComponent.exact
      by_contra hne
      exact hncut ⟨
        (deleteVertices J {x, y, z}).connectedComponentMk ⟨w, hwS⟩,
        (deleteVertices J {x, y, z}).connectedComponentMk v,
        hne⟩

end StandingSetup

end DeanK5
