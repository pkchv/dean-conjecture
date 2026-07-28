import DeanK5.COYModifiedExterior

/-!
# Exterior attachments to a modified type-3 COY core

This file proves the specially modified type-3 branch of COY Claim 3.3.
The original optimal core supplies the type minimality and the maximal
choice of its `S`-side; the modified core itself is not assigned any
additional maximality property.

The source excludes both the other root `y` and the distinguished removed
vertex `t₀`.  The latter exclusion is essential: `t₀` is adjacent to the
root and to every vertex of the modified `S`-side, but need not have a
neighbor in the modified `T`-side.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeThreeModificationChoice

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}
  {T : TypeThreeModificationTrigger (z := z) O}

/-- The neighbors of `v` in the selected modified core. -/
private noncomputable def modifiedCoreNeighbors
    (K : TypeThreeModificationChoice T) (v : V) : Finset V := by
  classical
  exact K.rooted.core.carrier.filter (G.Adj v)

/-- The neighbors of `v` in the modified terminal side `S`. -/
private noncomputable def modifiedSNeighbors
    (K : TypeThreeModificationChoice T) (v : V) : Finset V := by
  classical
  exact K.core.S.filter (G.Adj v)

/-- The neighbors of `v` in the modified root-adjacent side `T`. -/
private noncomputable def modifiedTNeighbors
    (K : TypeThreeModificationChoice T) (v : V) : Finset V := by
  classical
  exact K.core.T.filter (G.Adj v)

@[simp] private theorem mem_modifiedCoreNeighbors
    (K : TypeThreeModificationChoice T) (v w : V) :
    w ∈ K.modifiedCoreNeighbors v ↔
      w ∈ K.rooted.core.carrier ∧ G.Adj v w := by
  classical
  simp [modifiedCoreNeighbors]

@[simp] private theorem mem_modifiedSNeighbors
    (K : TypeThreeModificationChoice T) (v w : V) :
    w ∈ K.modifiedSNeighbors v ↔
      w ∈ K.core.S ∧ G.Adj v w := by
  classical
  simp [modifiedSNeighbors]

@[simp] private theorem mem_modifiedTNeighbors
    (K : TypeThreeModificationChoice T) (v w : V) :
    w ∈ K.modifiedTNeighbors v ↔
      w ∈ K.core.T ∧ G.Adj v w := by
  classical
  simp [modifiedTNeighbors]

/-- Finset and set formulations of the modified-core neighbor count agree. -/
private theorem modifiedCoreNeighbors_card_eq_ncard
    (K : TypeThreeModificationChoice T) (v : V) :
    (K.modifiedCoreNeighbors v).card =
      (G.neighborSet v ∩
        (↑K.rooted.core.carrier : Set V)).ncard := by
  classical
  have hset :
      G.neighborSet v ∩
          (↑K.rooted.core.carrier : Set V) =
        (↑(K.modifiedCoreNeighbors v) : Set V) := by
    ext w
    simp [modifiedCoreNeighbors, SimpleGraph.mem_neighborSet, and_comm]
  rw [hset, Set.ncard_coe_finset]

/-- Every old `T`-vertex other than `t₀` remains in the modified `T`-side. -/
private theorem mem_core_T_of_mem_original_T_of_ne_t₀
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hvT : v ∈ T.core.T)
    (hvt₀ : v ≠ T.t₀) :
    v ∈ K.core.T := by
  cases K <;>
    simp [core, TypeThreeCore.eraseBalanced,
      TypeThreeCore.eraseTerminal, hvT, hvt₀]

/--
An exterior vertex other than `t₀` is not adjacent to the root.  This uses
the trigger identity `N(x)=T_original`, not any maximality of the modified
core.
-/
private theorem not_adj_root
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hvCarrier : v ∉ K.rooted.core.carrier)
    (hvt₀ : v ≠ T.t₀) :
    ¬G.Adj x v := by
  intro hxv
  have hvOriginalT : v ∈ T.core.T :=
    (T.root_neighbors v).1 hxv
  have hvWorkingT : v ∈ K.core.T :=
    K.mem_core_T_of_mem_original_T_of_ne_t₀
      hvOriginalT hvt₀
  apply hvCarrier
  exact K.rooted.core.T_subset_carrier
    (by simpa [rooted, Core.T] using hvWorkingT)

/--
In a modified type-three core, every exterior vertex other than the removed
vertex `t₀` is nonadjacent to the root.
-/
theorem not_adj_root_of_exterior
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hvCarrier : v ∉ K.rooted.core.carrier)
    (hvt₀ : v ≠ T.t₀) :
    ¬G.Adj x v :=
  K.not_adj_root hvCarrier hvt₀

/--
Once root adjacency is excluded, the modified-core neighbors split exactly
between its two source sides.
-/
private theorem modifiedCoreNeighbors_eq_union
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hxv : ¬G.Adj x v) :
    K.modifiedCoreNeighbors v =
      K.modifiedSNeighbors v ∪ K.modifiedTNeighbors v := by
  classical
  ext w
  constructor
  · intro hw
    have hwData := (K.mem_modifiedCoreNeighbors v w).1 hw
    have hwx : w ≠ x := by
      intro h
      subst w
      exact hxv hwData.2.symm
    rcases K.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
        hwData.1 hwx with hwS | hwT
    · exact Finset.mem_union_left _
        ((K.mem_modifiedSNeighbors v w).2
          ⟨by simpa [rooted, Core.S] using hwS, hwData.2⟩)
    · exact Finset.mem_union_right _
        ((K.mem_modifiedTNeighbors v w).2
          ⟨by simpa [rooted, Core.T] using hwT, hwData.2⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hwS | hwT
    · have hwData := (K.mem_modifiedSNeighbors v w).1 hwS
      exact (K.mem_modifiedCoreNeighbors v w).2
        ⟨K.rooted.core.S_subset_carrier
            (by simpa [rooted, Core.S] using hwData.1),
          hwData.2⟩
    · have hwData := (K.mem_modifiedTNeighbors v w).1 hwT
      exact (K.mem_modifiedCoreNeighbors v w).2
        ⟨K.rooted.core.T_subset_carrier
            (by simpa [rooted, Core.T] using hwData.1),
          hwData.2⟩

/-- The two side-neighbor sets are disjoint. -/
private theorem disjoint_modifiedSideNeighbors
    (K : TypeThreeModificationChoice T) (v : V) :
    Disjoint (K.modifiedSNeighbors v) (K.modifiedTNeighbors v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwS hwT
  exact Finset.disjoint_left.mp K.core.disjoint
    ((K.mem_modifiedSNeighbors v w).1 hwS).1
    ((K.mem_modifiedTNeighbors v w).1 hwT).1

/--
Two modified `T`-neighbors and one modified `S`-neighbor would form a
rooted type-2 core, contradicting the original core's type minimality.
-/
private theorem modifiedTNeighbors_card_le_one_or_no_S_neighbor
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hvCarrier : v ∉ K.rooted.core.carrier)
    (hvy : v ≠ y) :
    (K.modifiedTNeighbors v).card ≤ 1 ∨
      K.modifiedSNeighbors v = ∅ := by
  classical
  by_contra h
  push Not at h
  obtain ⟨t₁, ht₁, t₂, ht₂, htne⟩ :=
    Finset.one_lt_card.mp (by omega :
      1 < (K.modifiedTNeighbors v).card)
  obtain ⟨s, hs⟩ := h.2
  have ht₁Data := (K.mem_modifiedTNeighbors v t₁).1 ht₁
  have ht₂Data := (K.mem_modifiedTNeighbors v t₂).1 ht₂
  have hsData := (K.mem_modifiedSNeighbors v s).1 hs
  have hvx : v ≠ x := by
    intro hvx
    apply hvCarrier
    rw [hvx]
    exact K.rooted.core.root_mem_carrier
  have hvs : v ≠ s := by
    intro hvs
    apply hvCarrier
    rw [hvs]
    exact K.rooted.core.S_subset_carrier
      (by simpa [rooted, Core.S] using hsData.1)
  have hvt₁ : v ≠ t₁ := ht₁Data.2.ne
  have hvt₂ : v ≠ t₂ := ht₂Data.2.ne
  have hst₁ : s ≠ t₁ := by
    intro hst
    exact Finset.disjoint_left.mp K.core.disjoint
      hsData.1 (hst ▸ ht₁Data.1)
  have hst₂ : s ≠ t₂ := by
    intro hst
    exact Finset.disjoint_left.mp K.core.disjoint
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
        fun hxt₁ =>
          K.core.root_not_mem_T (hxt₁ ▸ ht₁Data.1),
        fun hxt₂ =>
          K.core.root_not_mem_T (hxt₂ ▸ ht₂Data.1)⟩
    root_not_mem_T := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvx.symm,
        fun hxs =>
          K.core.root_not_mem_S (hxs ▸ hsData.1)⟩
    independent_S := by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;>
        rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact K.core.independent_T
          (by simpa using ht₁Data.1)
          (by simpa using ht₂Data.1) htne
      · intro hadj
        exact K.core.independent_T
          (by simpa using ht₁Data.1)
          (by simpa using ht₂Data.1) htne hadj.symm
      · exact False.elim (hab rfl)
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show v ≠ s → G.Adj v s from
          fun _ => hsData.2)
    root_adj_S := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact K.core.root_adj_T _ ht₁Data.1
      · exact K.core.root_adj_T _ ht₂Data.1
    cross_adj := by
      intro t ht w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht hw
      rcases ht with rfl | rfl <;>
        rcases hw with rfl | rfl
      · exact ht₁Data.2.symm
      · exact K.core.cross_adj _ ht₁Data.1 _ hsData.1
      · exact ht₂Data.2.symm
      · exact K.core.cross_adj _ ht₂Data.1 _ hsData.1
  }
  have hyx : y ≠ x := by
    intro hyx
    subst y
    exact O.rooted.other_root_not_mem
      O.rooted.core.root_mem_carrier
  let R' : RootedCore G x y 2 := {
    core := .typeTwo C'
    other_root_not_mem := by
      have hyt₁ : y ≠ t₁ := by
        intro hyt
        apply O.rooted.other_root_not_mem
        have htOriginal :
            t₁ ∈ O.rooted.core.carrier :=
          K.carrier_subset_original
            (K.rooted.core.T_subset_carrier
              (by simpa [rooted, Core.T] using ht₁Data.1))
        simpa [hyt] using htOriginal
      have hyt₂ : y ≠ t₂ := by
        intro hyt
        apply O.rooted.other_root_not_mem
        have htOriginal :
            t₂ ∈ O.rooted.core.carrier :=
          K.carrier_subset_original
            (K.rooted.core.T_subset_carrier
              (by simpa [rooted, Core.T] using ht₂Data.1))
        simpa [hyt] using htOriginal
      have hys : y ≠ s := by
        intro hys
        apply O.rooted.other_root_not_mem
        have hsOriginal :
            s ∈ O.rooted.core.carrier :=
          K.carrier_subset_original
            (K.rooted.core.S_subset_carrier
              (by simpa [rooted, Core.S] using hsData.1))
        simpa [hys] using hsOriginal
      simp [Core.carrier, Core.S, Core.T, C',
        hyx, hvy.symm, hyt₁, hyt₂, hys]
  }
  have hminimal := O.type_minimal R'
  rw [T.core_eq] at hminimal
  change 3 ≤ 2 at hminimal
  omega

/--
The number of neighbors in the modified `T`-side is at most `rank+1`.
For (M1) this is its exact side size.  For (M2), a larger neighbor set
would enlarge the original core's `S`-side via `insertInitial`.
-/
private theorem modifiedTNeighbors_card_le
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hvCarrier : v ∉ K.rooted.core.carrier)
    (hvy : v ≠ y)
    (hvt₀ : v ≠ T.t₀)
    (hside :
      (K.modifiedTNeighbors v).card ≤ 1 ∨
        K.modifiedSNeighbors v = ∅) :
    (K.modifiedTNeighbors v).card ≤ K.rank + 1 := by
  classical
  cases K with
  | balanced s₀ hs₀ hbalance =>
      calc
        (modifiedTNeighbors
            (.balanced s₀ hs₀ hbalance) v).card
            ≤ ((.balanced s₀ hs₀ hbalance :
              TypeThreeModificationChoice T).core.T).card :=
          Finset.card_le_card
            (Finset.filter_subset (G.Adj v) _)
        _ = ((.balanced s₀ hs₀ hbalance :
              TypeThreeModificationChoice T).rank + 1) := by
          change (T.core.T.erase T.t₀).card =
            (O.rank - 1) + 1
          rw [Finset.card_erase_of_mem T.t₀_mem,
            hbalance, T.core.card_S]
          have hrank :=
            T.two_le_rank_of_balanced hbalance
          omega
  | terminal hlarge =>
      let K' : TypeThreeModificationChoice T := .terminal hlarge
      by_contra hbound
      have hbound' :
          ¬(K'.modifiedTNeighbors v).card ≤ O.rank + 1 := by
        simpa [K', rank] using hbound
      have hneighborLarge :
          O.rank + 2 ≤ (K'.modifiedTNeighbors v).card := by
        omega
      have hsideEmpty : K'.modifiedSNeighbors v = ∅ := by
        rcases hside with hsmall | hempty
        · have : (K'.modifiedTNeighbors v).card ≤ 1 := by
            simpa [K'] using hsmall
          omega
        · simpa [K'] using hempty
      let U : Finset V := K'.modifiedTNeighbors v
      have hUOriginal : U ⊆ T.core.T := by
        intro w hw
        have hwWorking :=
          (K'.mem_modifiedTNeighbors v w).1 hw |>.1
        simpa [K', core, TypeThreeCore.eraseTerminal] using
          Finset.mem_of_mem_erase hwWorking
      have hUCard :
          max ((O.rank + 1) + 1) 2 ≤ U.card := by
        have : O.rank + 2 ≤ U.card := hneighborLarge
        omega
      have hvx : v ≠ x := by
        intro hvx
        apply hvCarrier
        rw [hvx]
        exact K'.rooted.core.root_mem_carrier
      have hvOriginalS : v ∉ T.core.S := by
        intro hvS
        apply hvCarrier
        exact K'.rooted.core.S_subset_carrier
          (by
            simpa [K', rooted, core, Core.S,
              TypeThreeCore.eraseTerminal] using hvS)
      have hvU : v ∉ U := by
        intro hv
        exact (K'.mem_modifiedTNeighbors v v).1 hv |>.2.ne rfl
      have hvNonadjOriginalS :
          ∀ s ∈ T.core.S, ¬G.Adj v s := by
        intro s hsS hvs
        have hsWorking :
            s ∈ K'.core.S := by
          simpa [K', core, TypeThreeCore.eraseTerminal] using hsS
        have hsNeighbor : s ∈ K'.modifiedSNeighbors v :=
          (K'.mem_modifiedSNeighbors v s).2
            ⟨hsWorking, hvs⟩
        rw [hsideEmpty] at hsNeighbor
        simp at hsNeighbor
      have hvAdjU :
          ∀ t ∈ U, G.Adj v t := by
        intro t ht
        exact (K'.mem_modifiedTNeighbors v t).1 ht |>.2
      let C' : TypeThreeCore G x (O.rank + 1) :=
        T.core.insertInitial v U hUOriginal hUCard
          hvx hvOriginalS hvU hvNonadjOriginalS hvAdjU
      have hyx : y ≠ x := by
        intro hyx
        subst y
        exact O.rooted.other_root_not_mem
          O.rooted.core.root_mem_carrier
      have hyOriginalS : y ∉ T.core.S := by
        intro hyS
        apply O.rooted.other_root_not_mem
        rw [T.core_eq]
        simp [Core.carrier, Core.S, Core.T, hyS]
      have hyU : y ∉ U := by
        intro hyU
        apply O.rooted.other_root_not_mem
        rw [T.core_eq]
        have hyOriginalT := hUOriginal hyU
        simp [Core.carrier, Core.S, Core.T, hyOriginalT]
      let R' : RootedCore G x y (O.rank + 1) := {
        core := .typeThree C'
        other_root_not_mem := by
          simp [Core.carrier, Core.S, Core.T, C',
            TypeThreeCore.insertInitial,
            hyx, hvy.symm, hyOriginalS, hyU]
      }
      have htype :
          R'.core.typeNumber =
            O.rooted.core.typeNumber := by
        rw [T.core_eq]
        rfl
      have hmax := O.S_maximal R' htype
      have hcardNew :
          R'.core.S.card = O.rank + 1 := by
        simp [R', C', Core.S, TypeThreeCore.insertInitial,
          hvOriginalS, T.core.card_S]
      have hcardOld :
          O.rooted.core.S.card = O.rank := by
        rw [T.core_eq]
        exact T.core.card_S
      rw [hcardNew, hcardOld] at hmax
      omega

/--
Modified type-3 branch of COY Claim 3.3: a vertex outside the working core,
other than the two source-excluded vertices `y` and `t₀`, has at most
`rank+1` neighbors in the working core.
-/
theorem coreNeighbor_ncard_le_of_modified
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hvCarrier : v ∉ K.rooted.core.carrier)
    (hvy : v ≠ y)
    (hvt₀ : v ≠ T.t₀) :
    (G.neighborSet v ∩
      (↑K.rooted.core.carrier : Set V)).ncard ≤ K.rank + 1 := by
  classical
  have hxv : ¬G.Adj x v :=
    K.not_adj_root hvCarrier hvt₀
  have hsplit :=
    K.modifiedTNeighbors_card_le_one_or_no_S_neighbor
      hvCarrier hvy
  have hTBound :=
    K.modifiedTNeighbors_card_le
      hvCarrier hvy hvt₀ hsplit
  rw [← K.modifiedCoreNeighbors_card_eq_ncard v,
    K.modifiedCoreNeighbors_eq_union hxv,
    Finset.card_union_of_disjoint
      (K.disjoint_modifiedSideNeighbors v)]
  rcases hsplit with hsmall | hnoS
  · calc
      (K.modifiedSNeighbors v).card +
          (K.modifiedTNeighbors v).card
          ≤ K.core.S.card + 1 := by
            exact Nat.add_le_add
              (Finset.card_le_card
                (Finset.filter_subset (G.Adj v) K.core.S))
              hsmall
      _ = K.rank + 1 := by rw [K.core.card_S]
  · rw [hnoS, Finset.card_empty, zero_add]
    exact hTBound

/--
Equality in the modified attachment bound forces a neighbor in the modified
`T`-side.
-/
theorem exists_T_neighbor_of_coreNeighbor_ncard_eq_modified
    (K : TypeThreeModificationChoice T)
    {v : V}
    (hvCarrier : v ∉ K.rooted.core.carrier)
    (_hvy : v ≠ y)
    (hvt₀ : v ≠ T.t₀)
    (heq :
      (G.neighborSet v ∩
        (↑K.rooted.core.carrier : Set V)).ncard =
        K.rank + 1) :
    ∃ t ∈ K.rooted.core.T, G.Adj v t := by
  classical
  by_contra hT
  have hxv : ¬G.Adj x v :=
    K.not_adj_root hvCarrier hvt₀
  have hTEmpty : K.modifiedTNeighbors v = ∅ := by
    by_contra hne
    obtain ⟨t, ht⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hne
    have htData := (K.mem_modifiedTNeighbors v t).1 ht
    exact hT ⟨t,
      by simpa [rooted, Core.T] using htData.1,
      htData.2⟩
  have hcard :
      (K.modifiedCoreNeighbors v).card ≤ K.rank := by
    rw [K.modifiedCoreNeighbors_eq_union hxv,
      hTEmpty, Finset.union_empty]
    calc
      (K.modifiedSNeighbors v).card ≤ K.core.S.card :=
        Finset.card_le_card
          (Finset.filter_subset (G.Adj v) K.core.S)
      _ = K.rank := K.core.card_S
  rw [K.modifiedCoreNeighbors_card_eq_ncard v, heq] at hcard
  omega

end TypeThreeModificationChoice

end COY

end DeanK5
