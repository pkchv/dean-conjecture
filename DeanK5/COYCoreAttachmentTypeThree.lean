import DeanK5.COYCoreAttachmentNatural

/-!
# Exterior attachments to a natural type-3 COY core

This file proves the type-3 case of the unmodified-core form of COY
Claim 3.3.  For a lexicographically optimal rooted type-3 core, an exterior
vertex other than the second root has at most `rank + 1` neighbors in the
core.  Equality forces one of those neighbors to lie in the source set `T`.

Type minimality excludes two local patterns: a triangle through the root,
and a mixed attachment to one `S`-vertex and two `T`-vertices.  The remaining
large attachments enlarge either `S` or `T`, contradicting the corresponding
lexicographic maximality condition.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace OptimalRootedCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y : V}

/-- The neighbors of `v` in the carrier of a selected type-3 core. -/
private noncomputable def typeThreeCoreNeighbors
    (R : OptimalRootedCore G x y) (v : V) : Finset V := by
  classical
  exact R.rooted.core.carrier.filter (G.Adj v)

/-- The neighbors of `v` in the terminal side `S`. -/
private noncomputable def typeThreeSNeighbors
    (C : TypeThreeCore G x ℓ) (v : V) : Finset V := by
  classical
  exact C.S.filter (G.Adj v)

/-- The neighbors of `v` in the root-adjacent side `T`. -/
private noncomputable def typeThreeTNeighbors
    (C : TypeThreeCore G x ℓ) (v : V) : Finset V := by
  classical
  exact C.T.filter (G.Adj v)

@[simp] private theorem mem_typeThreeCoreNeighbors
    (R : OptimalRootedCore G x y) (v w : V) :
    w ∈ R.typeThreeCoreNeighbors v ↔
      w ∈ R.rooted.core.carrier ∧ G.Adj v w := by
  classical
  simp [typeThreeCoreNeighbors]

omit [Fintype V] in
@[simp] private theorem mem_typeThreeSNeighbors
    (C : TypeThreeCore G x ℓ) (v w : V) :
    w ∈ typeThreeSNeighbors C v ↔
      w ∈ C.S ∧ G.Adj v w := by
  classical
  simp [typeThreeSNeighbors]

omit [Fintype V] in
@[simp] private theorem mem_typeThreeTNeighbors
    (C : TypeThreeCore G x ℓ) (v w : V) :
    w ∈ typeThreeTNeighbors C v ↔
      w ∈ C.T ∧ G.Adj v w := by
  classical
  simp [typeThreeTNeighbors]

/-- Finset and set formulations of the type-3 core-neighbor count agree. -/
private theorem typeThreeCoreNeighbors_card_eq_ncard
    (R : OptimalRootedCore G x y) (v : V) :
    (R.typeThreeCoreNeighbors v).card =
      (G.neighborSet v ∩
        (↑R.rooted.core.carrier : Set V)).ncard := by
  classical
  have hset :
      G.neighborSet v ∩
          (↑R.rooted.core.carrier : Set V) =
        (↑(R.typeThreeCoreNeighbors v) : Set V) := by
    ext w
    simp [typeThreeCoreNeighbors, SimpleGraph.mem_neighborSet, and_comm]
  rw [hset, Set.ncard_coe_finset]

/--
A triangle through the root, an exterior vertex, and a `T`-vertex is a
rooted type-1 core.
-/
private def rootedTypeOneOfTypeThreeTriangle
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v t : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (ht : t ∈ C.T)
    (hxv : G.Adj x v)
    (hvt : G.Adj v t) :
    RootedCore G x y 1 := by
  have hxt : G.Adj x t := C.root_adj_T t ht
  have hvx : v ≠ x := by
    intro hvx
    apply hvCarrier
    rw [hvx]
    exact R.rooted.core.root_mem_carrier
  have htx : t ≠ x := by
    intro htx
    exact C.root_not_mem_T (htx ▸ ht)
  have hyx : y ≠ x := by
    intro hyx
    subst y
    exact R.rooted.other_root_not_mem
      R.rooted.core.root_mem_carrier
  have hyt : y ≠ t := by
    intro hyt
    apply R.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hyt, ht]
  let C' : TypeOneCore G x 1 := {
    T := {v, t}
    rank_pos := le_rfl
    card_T := by simp [hvt.ne]
    root_not_mem := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvx.symm, htx.symm⟩
    root_adj := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hxv
      · exact hxt
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show v ≠ t → G.Adj v t from fun _ => hvt)
  }
  exact {
    core := .typeOne C'
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C',
        hyx, hvy.symm, hyt]
  }

/--
Type minimality excludes an exterior `T`-neighbor when the exterior vertex
is adjacent to the selected root.
-/
private theorem not_adj_T_of_adj_root
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (hxv : G.Adj x v) :
    ∀ t ∈ C.T, ¬G.Adj v t := by
  intro t ht hvt
  let R' :=
    R.rootedTypeOneOfTypeThreeTriangle C hcore
      hvCarrier hvy ht hxv hvt
  have hminimal := R.type_minimal R'
  rw [hcore] at hminimal
  change 3 ≤ 1 at hminimal
  omega

/--
For a natural type-three core, an exterior vertex with a `T`-neighbor is
not adjacent to the root.
-/
theorem not_adj_root_of_typeThree_of_T_neighbor
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v t : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (ht : t ∈ C.T)
    (hvt : G.Adj v t) :
    ¬G.Adj x v := by
  intro hxv
  exact
    (R.not_adj_T_of_adj_root
      C hcore hvCarrier hvy hxv t ht) hvt

/--
When the exterior vertex is not adjacent to the root, its core neighbors
split exactly between the two source sides.
-/
private theorem typeThreeCoreNeighbors_eq_union
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v : V}
    (hxv : ¬G.Adj x v) :
    R.typeThreeCoreNeighbors v =
      typeThreeSNeighbors C v ∪ typeThreeTNeighbors C v := by
  classical
  ext w
  constructor
  · intro hw
    have hwData := (R.mem_typeThreeCoreNeighbors v w).1 hw
    have hwx : w ≠ x := by
      intro hwx
      subst w
      exact hxv hwData.2.symm
    have hwClass :
        w ∈ C.S ∨ w ∈ C.T := by
      rw [hcore] at hwData
      simpa [Core.carrier, Core.S, Core.T, hwx] using hwData.1
    rcases hwClass with hwS | hwT
    · exact Finset.mem_union_left _
        ((mem_typeThreeSNeighbors C v w).2 ⟨hwS, hwData.2⟩)
    · exact Finset.mem_union_right _
        ((mem_typeThreeTNeighbors C v w).2 ⟨hwT, hwData.2⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hwS | hwT
    · have hwData := (mem_typeThreeSNeighbors C v w).1 hwS
      exact (R.mem_typeThreeCoreNeighbors v w).2
        ⟨by
            rw [hcore]
            exact (Core.typeThree C).S_subset_carrier
              (by simpa [Core.S] using hwData.1),
          hwData.2⟩
    · have hwData := (mem_typeThreeTNeighbors C v w).1 hwT
      exact (R.mem_typeThreeCoreNeighbors v w).2
        ⟨by
            rw [hcore]
            exact (Core.typeThree C).T_subset_carrier
              (by simpa [Core.T] using hwData.1),
          hwData.2⟩

omit [Fintype V] in
/-- The two side-neighbor sets are disjoint. -/
private theorem disjoint_typeThreeSideNeighbors
    (C : TypeThreeCore G x ℓ) (v : V) :
    Disjoint (typeThreeSNeighbors C v) (typeThreeTNeighbors C v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwS hwT
  exact Finset.disjoint_left.mp C.disjoint
    ((mem_typeThreeSNeighbors C v w).1 hwS).1
    ((mem_typeThreeTNeighbors C v w).1 hwT).1

/--
Two `T`-neighbors and one `S`-neighbor would form a rooted type-2 core,
contradicting type minimality.
-/
private theorem typeThreeTNeighbors_card_le_one_or_no_S_neighbor
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y) :
    (typeThreeTNeighbors C v).card ≤ 1 ∨
      typeThreeSNeighbors C v = ∅ := by
  classical
  by_contra h
  push Not at h
  obtain ⟨t₁, ht₁, t₂, ht₂, htne⟩ :=
    Finset.one_lt_card.mp (by omega :
      1 < (typeThreeTNeighbors C v).card)
  obtain ⟨s, hs⟩ := h.2
  have ht₁Data := (mem_typeThreeTNeighbors C v t₁).1 ht₁
  have ht₂Data := (mem_typeThreeTNeighbors C v t₂).1 ht₂
  have hsData := (mem_typeThreeSNeighbors C v s).1 hs
  have hvx : v ≠ x := by
    intro hvx
    apply hvCarrier
    rw [hvx]
    exact R.rooted.core.root_mem_carrier
  have hvs : v ≠ s := by
    intro hvs
    apply hvCarrier
    rw [hvs, hcore]
    exact (Core.typeThree C).S_subset_carrier
      (by simpa [Core.S] using hsData.1)
  have hvt₁ : v ≠ t₁ := ht₁Data.2.ne
  have hvt₂ : v ≠ t₂ := ht₂Data.2.ne
  have hst₁ : s ≠ t₁ := by
    intro hst
    exact Finset.disjoint_left.mp C.disjoint
      hsData.1 (hst ▸ ht₁Data.1)
  have hst₂ : s ≠ t₂ := by
    intro hst
    exact Finset.disjoint_left.mp C.disjoint
      hsData.1 (hst ▸ ht₂Data.1)
  let C' : TypeTwoCore G x 2 := {
    S := {t₁, t₂}
    T := {v, s}
    rank_ge_two := le_rfl
    card_S := by simp [htne]
    card_T := by simp [hvs]
    disjoint := by
      simp [hvt₁, hvt₂, hst₁, hst₂]
    root_not_mem_S := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨
        fun hxt₁ => C.root_not_mem_T (hxt₁ ▸ ht₁Data.1),
        fun hxt₂ => C.root_not_mem_T (hxt₂ ▸ ht₂Data.1)⟩
    root_not_mem_T := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvx.symm,
        fun hxs => C.root_not_mem_S (hxs ▸ hsData.1)⟩
    independent_S := by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;>
        rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact C.independent_T
          (by simpa using ht₁Data.1)
          (by simpa using ht₂Data.1) htne
      · intro hadj
        exact C.independent_T
          (by simpa using ht₁Data.1)
          (by simpa using ht₂Data.1) htne hadj.symm
      · exact False.elim (hab rfl)
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show v ≠ s → G.Adj v s from fun _ => hsData.2)
    root_adj_S := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact C.root_adj_T _ ht₁Data.1
      · exact C.root_adj_T _ ht₂Data.1
    cross_adj := by
      intro t ht w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht hw
      rcases ht with rfl | rfl <;>
        rcases hw with rfl | rfl
      · exact ht₁Data.2.symm
      · exact C.cross_adj _ ht₁Data.1 _ hsData.1
      · exact ht₂Data.2.symm
      · exact C.cross_adj _ ht₂Data.1 _ hsData.1
  }
  have hyx : y ≠ x := by
    intro hyx
    subst y
    exact R.rooted.other_root_not_mem
      R.rooted.core.root_mem_carrier
  have hyt₁ : y ≠ t₁ := by
    intro hyt
    apply R.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hyt, ht₁Data.1]
  have hyt₂ : y ≠ t₂ := by
    intro hyt
    apply R.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hyt, ht₂Data.1]
  have hys : y ≠ s := by
    intro hys
    apply R.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hys, hsData.1]
  let R' : RootedCore G x y 2 := {
    core := .typeTwo C'
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C',
        hyx, hvy.symm, hyt₁, hyt₂, hys]
  }
  have hminimal := R.type_minimal R'
  rw [hcore] at hminimal
  change 3 ≤ 2 at hminimal
  omega

/--
The number of `T`-neighbors is at most `rank+1`.  A larger set, in the only
case not already excluded by the type-2 obstruction, enlarges the `S`-side.
-/
private theorem typeThreeTNeighbors_card_le
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (hside :
      (typeThreeTNeighbors C v).card ≤ 1 ∨
        typeThreeSNeighbors C v = ∅) :
    (typeThreeTNeighbors C v).card ≤ R.rank + 1 := by
  classical
  rcases hside with hsmall | hnoS
  · omega
  · by_contra hbound
    have hlarge :
        R.rank + 2 ≤ (typeThreeTNeighbors C v).card := by
      omega
    let U : Finset V := typeThreeTNeighbors C v
    have hUT : U ⊆ C.T :=
      Finset.filter_subset (G.Adj v) C.T
    have hUCard :
        max ((R.rank + 1) + 1) 2 ≤ U.card := by
      have : R.rank + 2 ≤ U.card := hlarge
      omega
    have hvx : v ≠ x := by
      intro hvx
      apply hvCarrier
      rw [hvx]
      exact R.rooted.core.root_mem_carrier
    have hvS : v ∉ C.S := by
      intro hvS
      apply hvCarrier
      rw [hcore]
      exact (Core.typeThree C).S_subset_carrier
        (by simpa [Core.S] using hvS)
    have hvU : v ∉ U := by
      intro hv
      exact (mem_typeThreeTNeighbors C v v).1 hv |>.2.ne rfl
    have hvNonadjS :
        ∀ s ∈ C.S, ¬G.Adj v s := by
      intro s hs hvs
      have hsNeighbor : s ∈ typeThreeSNeighbors C v :=
        (mem_typeThreeSNeighbors C v s).2 ⟨hs, hvs⟩
      rw [hnoS] at hsNeighbor
      simp at hsNeighbor
    have hvAdjU :
        ∀ t ∈ U, G.Adj v t := by
      intro t ht
      exact (mem_typeThreeTNeighbors C v t).1 ht |>.2
    let C' : TypeThreeCore G x (R.rank + 1) :=
      C.insertInitial v U hUT hUCard
        hvx hvS hvU hvNonadjS hvAdjU
    have hyx : y ≠ x := by
      intro hyx
      subst y
      exact R.rooted.other_root_not_mem
        R.rooted.core.root_mem_carrier
    have hyS : y ∉ C.S := by
      intro hyS
      apply R.rooted.other_root_not_mem
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, hyS]
    have hyU : y ∉ U := by
      intro hyU
      apply R.rooted.other_root_not_mem
      rw [hcore]
      have hyT := hUT hyU
      simp [Core.carrier, Core.S, Core.T, hyT]
    let R' : RootedCore G x y (R.rank + 1) := {
      core := .typeThree C'
      other_root_not_mem := by
        simp [Core.carrier, Core.S, Core.T, C',
          TypeThreeCore.insertInitial,
          hyx, hvy.symm, hyS, hyU]
    }
    have htype :
        R'.core.typeNumber =
          R.rooted.core.typeNumber := by
      rw [hcore]
      rfl
    have hmax := R.S_maximal R' htype
    have hcardNew :
        R'.core.S.card = R.rank + 1 := by
      simp [R', C', Core.S, TypeThreeCore.insertInitial,
        hvS, C.card_S]
    have hcardOld :
        R.rooted.core.S.card = R.rank := by
      rw [hcore]
      exact C.card_S
    rw [hcardNew, hcardOld] at hmax
    omega

/-- The natural-core attachment bound in source type 3. -/
private theorem typeThreeCoreNeighbors_card_le
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y) :
    (R.typeThreeCoreNeighbors v).card ≤ R.rank + 1 := by
  classical
  by_cases hxv : G.Adj x v
  · have hvT :
        ∀ t ∈ C.T, ¬G.Adj v t :=
      R.not_adj_T_of_adj_root C hcore hvCarrier hvy hxv
    have hsubset :
        R.typeThreeCoreNeighbors v ⊆ insert x C.S := by
      intro w hw
      have hwData := (R.mem_typeThreeCoreNeighbors v w).1 hw
      have hwClass :
          w = x ∨ w ∈ C.S ∨ w ∈ C.T := by
        rw [hcore] at hwData
        simpa [Core.carrier, Core.S, Core.T] using hwData.1
      rcases hwClass with rfl | hwS | hwT
      · simp
      · simp [hwS]
      · exact False.elim (hvT w hwT hwData.2)
    calc
      (R.typeThreeCoreNeighbors v).card
          ≤ (insert x C.S).card :=
        Finset.card_le_card hsubset
      _ = R.rank + 1 := by
        simp [C.root_not_mem_S, C.card_S]
  · have hsplit :=
      R.typeThreeTNeighbors_card_le_one_or_no_S_neighbor
        C hcore hvCarrier hvy
    have hTBound :=
      R.typeThreeTNeighbors_card_le
        C hcore hvCarrier hvy hsplit
    rw [R.typeThreeCoreNeighbors_eq_union C hcore hxv,
      Finset.card_union_of_disjoint
        (disjoint_typeThreeSideNeighbors C v)]
    rcases hsplit with hsmall | hnoS
    · calc
        (typeThreeSNeighbors C v).card +
            (typeThreeTNeighbors C v).card
            ≤ C.S.card + 1 := by
              exact Nat.add_le_add
                (Finset.card_le_card
                  (Finset.filter_subset (G.Adj v) C.S))
                hsmall
        _ = R.rank + 1 := by rw [C.card_S]
    · rw [hnoS, Finset.card_empty, zero_add]
      exact hTBound

/--
Type-3 case of Claim 3.3 in source set-cardinality form: an exterior vertex
other than the second root has at most `rank + 1` neighbors in the natural
core.
-/
theorem coreNeighbor_ncard_le_of_typeThree
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y) :
    (G.neighborSet v ∩
      (↑R.rooted.core.carrier : Set V)).ncard ≤ R.rank + 1 := by
  rw [← R.typeThreeCoreNeighbors_card_eq_ncard v]
  exact R.typeThreeCoreNeighbors_card_le C hcore hvCarrier hvy

/--
In the equality case of the type-3 attachment bound, the exterior vertex
has a neighbor in the source set `T`.
-/
theorem exists_T_neighbor_of_coreNeighbor_ncard_eq_typeThree
    (R : OptimalRootedCore G x y)
    (C : TypeThreeCore G x R.rank)
    (hcore : R.rooted.core = .typeThree C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (heq :
      (G.neighborSet v ∩
        (↑R.rooted.core.carrier : Set V)).ncard =
        R.rank + 1) :
    ∃ t ∈ R.rooted.core.T, G.Adj v t := by
  classical
  by_contra hT
  have hTEmpty : typeThreeTNeighbors C v = ∅ := by
    by_contra hne
    obtain ⟨t, ht⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hne
    have htData := (mem_typeThreeTNeighbors C v t).1 ht
    exact hT ⟨t,
      by simpa [hcore, Core.T] using htData.1,
      htData.2⟩
  by_cases hxv : G.Adj x v
  · have hsubset :
        R.typeThreeCoreNeighbors v ⊆ insert x C.S := by
      intro w hw
      have hwData := (R.mem_typeThreeCoreNeighbors v w).1 hw
      have hwClass :
          w = x ∨ w ∈ C.S ∨ w ∈ C.T := by
        rw [hcore] at hwData
        simpa [Core.carrier, Core.S, Core.T] using hwData.1
      rcases hwClass with rfl | hwS | hwT
      · simp
      · simp [hwS]
      · have hwTN : w ∈ typeThreeTNeighbors C v :=
          (mem_typeThreeTNeighbors C v w).2 ⟨hwT, hwData.2⟩
        rw [hTEmpty] at hwTN
        simp at hwTN
    have hneighborCard :
        (R.typeThreeCoreNeighbors v).card = R.rank + 1 := by
      rw [R.typeThreeCoreNeighbors_card_eq_ncard v, heq]
    have hneighbors :
        R.typeThreeCoreNeighbors v = insert x C.S := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [hneighborCard]
      simp [C.root_not_mem_S, C.card_S]
    have hvAdjS :
        ∀ s ∈ C.S, G.Adj v s := by
      intro s hs
      have hsN : s ∈ R.typeThreeCoreNeighbors v := by
        rw [hneighbors]
        simp [hs]
      exact (R.mem_typeThreeCoreNeighbors v s).1 hsN |>.2
    have hvNonadjT :
        ∀ t ∈ C.T, ¬G.Adj v t := by
      intro t ht hvt
      have htN : t ∈ typeThreeTNeighbors C v :=
        (mem_typeThreeTNeighbors C v t).2 ⟨ht, hvt⟩
      rw [hTEmpty] at htN
      simp at htN
    have hvx : v ≠ x := by
      intro hvx
      apply hvCarrier
      rw [hvx]
      exact R.rooted.core.root_mem_carrier
    have hvS : v ∉ C.S := by
      intro hvS
      apply hvCarrier
      rw [hcore]
      exact (Core.typeThree C).S_subset_carrier
        (by simpa [Core.S] using hvS)
    have hvT : v ∉ C.T := by
      intro hvT
      apply hvCarrier
      rw [hcore]
      exact (Core.typeThree C).T_subset_carrier
        (by simpa [Core.T] using hvT)
    let C' : TypeThreeCore G x R.rank :=
      C.insertTerminal v hvx hvS hvT hxv hvNonadjT hvAdjS
    have hyx : y ≠ x := by
      intro hyx
      subst y
      exact R.rooted.other_root_not_mem
        R.rooted.core.root_mem_carrier
    have hyS : y ∉ C.S := by
      intro hyS
      apply R.rooted.other_root_not_mem
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, hyS]
    have hyT : y ∉ C.T := by
      intro hyT
      apply R.rooted.other_root_not_mem
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, hyT]
    let R' : RootedCore G x y R.rank := {
      core := .typeThree C'
      other_root_not_mem := by
        simp [Core.carrier, Core.S, Core.T, C',
          TypeThreeCore.insertTerminal,
          hyx, hvy.symm, hyS, hyT]
    }
    have htype :
        R'.core.typeNumber =
          R.rooted.core.typeNumber := by
      rw [hcore]
      rfl
    have hS :
        R'.core.S.card =
          R.rooted.core.S.card := by
      rw [hcore]
      rfl
    have hmax := R.T_maximal R' htype hS
    have hcardNew :
        R'.core.T.card = C.T.card + 1 := by
      simp [R', C', Core.T, TypeThreeCore.insertTerminal, hvT]
    have hcardOld :
        R.rooted.core.T.card = C.T.card := by
      rw [hcore]
      rfl
    rw [hcardNew, hcardOld] at hmax
    omega
  · have hcard :
        (R.typeThreeCoreNeighbors v).card ≤ R.rank := by
      rw [R.typeThreeCoreNeighbors_eq_union C hcore hxv,
        hTEmpty, Finset.union_empty]
      calc
        (typeThreeSNeighbors C v).card ≤ C.S.card :=
          Finset.card_le_card
            (Finset.filter_subset (G.Adj v) C.S)
        _ = R.rank := C.card_S
    rw [R.typeThreeCoreNeighbors_card_eq_ncard v, heq] at hcard
    omega

end OptimalRootedCore

end COY

end DeanK5
