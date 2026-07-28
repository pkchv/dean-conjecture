import DeanK5.COYWorkingCoreSelection

/-!
# The singleton exterior in the COY core argument

This file formalizes COY Claim 3.5 for the natural working core.  If the
component of the core deletion containing the other root is the singleton
`{y}`, then all neighbors of `y` lie in the core.  Conditions (XY1) and
(XY2) then identify the complete neighborhood of both roots with the
appropriate side of the core.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace SelectedWorkingCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}

/--
The singleton-exterior case cannot use the special type-3 modification.
This is the formal version of the source deduction from Claim 3.4.
-/
theorem eq_natural_of_otherRegion_eq_singleton
    (W : SelectedWorkingCore (z := z) O)
    (hxz : ¬G.Adj x z)
    (hregion : W.rooted.otherRegion = {y}) :
    ∃ hnot :
        ¬Nonempty (TypeThreeModificationTrigger (z := z) O),
      W = .natural hnot := by
  cases W with
  | natural hnot =>
      exact ⟨hnot, rfl⟩
  | modified T K =>
      have htwo :=
        K.two_le_otherRegion_sdiff_protected hxz
      change K.rooted.otherRegion = {y} at hregion
      rw [hregion] at htwo
      have hempty :
          ({y} : Finset V) \ {y, z} = ∅ := by
        apply Finset.sdiff_eq_empty_iff_subset.2
        simp
      rw [hempty, Finset.card_empty] at htwo
      omega

end SelectedWorkingCore

namespace PreferredOrientationData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
If the exterior component containing the other root is a singleton, every
neighbor of that root belongs to the core carrier.
-/
private theorem other_neighborSet_subset_carrier_of_region_eq_singleton
    (D : PreferredOrientationData G x y z)
    (hregion : D.chosen.rooted.otherRegion = {y}) :
    G.neighborSet y ⊆
      (↑D.chosen.rooted.core.carrier : Set V) := by
  intro v hv
  have hyv : G.Adj y v := by
    simpa [SimpleGraph.mem_neighborSet] using hv
  by_contra hvCarrier
  have hvRegion :=
    D.chosen.rooted.otherRegion_componentRegion.closed
      D.chosen.rooted.other_root_mem_otherRegion
      hyv hvCarrier
  rw [hregion] at hvRegion
  have hvy : v = y := by
    simpa using hvRegion
  subst v
  exact G.loopless.irrefl y hyv

/--
Protected nonadjacency removes the old root from the preceding containment,
so every neighbor of the other root lies in one of the two source parts.
-/
private theorem other_neighborSet_subset_core_parts
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hregion : D.chosen.rooted.otherRegion = {y}) :
    G.neighborSet y ⊆
      (↑(D.chosen.rooted.core.S ∪
        D.chosen.rooted.core.T) : Set V) := by
  intro v hv
  have hyv : G.Adj y v := by
    simpa [SimpleGraph.mem_neighborSet] using hv
  have hvCarrier :=
    D.other_neighborSet_subset_carrier_of_region_eq_singleton
      hregion hv
  have hvx : v ≠ x := by
    intro hvx
    subst v
    exact M.roots_not_adj hyv.symm
  have hvParts :=
    D.chosen.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
      hvCarrier hvx
  change v ∈
    D.chosen.rooted.core.S ∪ D.chosen.rooted.core.T
  exact Finset.mem_union.mpr hvParts

/-- Two adjacent neighbors of `y` form a type-1 core at the reversed root. -/
private def rootedTypeOneAtOther
    (G : SimpleGraph V) {x y u v : V}
    (hxy : x ≠ y) (hnotAdj : ¬G.Adj x y)
    (hyu : G.Adj y u) (hyv : G.Adj y v)
    (huv : G.Adj u v) :
    RootedCore G y x 1 := by
  have hxu : x ≠ u := by
    intro hxu
    subst u
    exact hnotAdj hyu.symm
  have hxv : x ≠ v := by
    intro hxv
    subst v
    exact hnotAdj hyv.symm
  let C : TypeOneCore G y 1 := {
    T := {u, v}
    rank_pos := le_rfl
    card_T := by simp [huv.ne]
    root_not_mem := by simp [hyu.ne, hyv.ne]
    root_adj := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hyu
      · exact hyv
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show u ≠ v → G.Adj u v from fun _ => huv)
  }
  exact {
    core := .typeOne C
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C,
        hxy, hxu, hxv]
  }

/--
Under (XY1), a chosen core of type at least two rules out an adjacent pair
of neighbors at the reversed root.
-/
private theorem not_adj_of_other_neighbors_of_two_le_type
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (htype : 2 ≤ D.chosen.rooted.core.typeNumber)
    {u v : V} (hyu : G.Adj y u) (hyv : G.Adj y v) :
    ¬G.Adj u v := by
  intro huv
  let R : RootedCore G y x 1 :=
    rootedTypeOneAtOther G M.roots_ne M.roots_not_adj
      hyu hyv huv
  have hminimal := D.type_le_core_at_other_root R
  change D.chosen.rooted.core.typeNumber ≤ 1 at hminimal
  omega

/--
Condition (XY2) closes the cardinality sandwich
`N(y) ⊆ A ⊆ N(x)`.
-/
private theorem neighborSets_eq_of_other_attains_type
    (D : PreferredOrientationData G x y z)
    (hattains : D.OtherRootAttainsChosenType)
    (A : Finset V)
    (hyA : G.neighborSet y ⊆ (↑A : Set V))
    (hAx : (↑A : Set V) ⊆ G.neighborSet x) :
    G.neighborSet x = G.neighborSet y ∧
      G.neighborSet y = (↑A : Set V) := by
  have hdegree :=
    D.chosen_degree_le_other_of_otherRootAttainsChosenType hattains
  change (G.neighborSet x).ncard ≤
    (G.neighborSet y).ncard at hdegree
  have hAdegreeX :
      (↑A : Set V).ncard ≤ (G.neighborSet x).ncard :=
    Set.ncard_le_ncard hAx
  have hdegreeYA :
      (G.neighborSet y).ncard ≤ (↑A : Set V).ncard :=
    Set.ncard_le_ncard hyA
  have hAeqX :
      (↑A : Set V) = G.neighborSet x :=
    Set.eq_of_subset_of_ncard_le hAx
      (hdegree.trans hdegreeYA)
  have hyEqA :
      G.neighborSet y = (↑A : Set V) :=
    Set.eq_of_subset_of_ncard_le hyA
      (hAdegreeX.trans hdegree)
  exact ⟨hAeqX.symm.trans hyEqA.symm, hyEqA⟩

/-- Claim 3.5 in source type 1. -/
private theorem neighborSets_eq_T_of_singleton_typeOne
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (C : TypeOneCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeOne C)
    (hregion : D.chosen.rooted.otherRegion = {y}) :
    G.neighborSet x = G.neighborSet y ∧
      G.neighborSet y = (↑C.T : Set V) := by
  have hyParts :=
    D.other_neighborSet_subset_core_parts M hregion
  have hyT : G.neighborSet y ⊆ (↑C.T : Set V) := by
    intro v hv
    have hvParts := hyParts hv
    rw [hcore] at hvParts
    simpa [Core.S, Core.T] using hvParts
  have htwo : 1 < (G.neighborSet y).ncard := by
    change 1 < finiteDegree G y
    exact M.two_le_right_root_degree
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Set.one_lt_ncard (s := G.neighborSet y)).1 htwo
  have hyu : G.Adj y u := by
    simpa [SimpleGraph.mem_neighborSet] using hu
  have hyv : G.Adj y v := by
    simpa [SimpleGraph.mem_neighborSet] using hv
  have huT : u ∈ (↑C.T : Set V) := hyT hu
  have hvT : v ∈ (↑C.T : Set V) := hyT hv
  have huvAdj : G.Adj u v :=
    C.clique_T huT hvT huv
  let R : RootedCore G y x 1 :=
    rootedTypeOneAtOther G M.roots_ne M.roots_not_adj
      hyu hyv huvAdj
  have hattains : D.OtherRootAttainsChosenType := by
    refine ⟨1, R, ?_⟩
    rw [hcore]
    rfl
  have hTx : (↑C.T : Set V) ⊆ G.neighborSet x := by
    intro t ht
    simpa [SimpleGraph.mem_neighborSet] using
      C.root_adj t (by simpa using ht)
  exact D.neighborSets_eq_of_other_attains_type
    hattains C.T hyT hTx

/-- Claim 3.5 in source type 2. -/
private theorem neighborSets_eq_S_of_singleton_typeTwo
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (C : TypeTwoCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeTwo C)
    (hregion : D.chosen.rooted.otherRegion = {y}) :
    G.neighborSet x = G.neighborSet y ∧
      G.neighborSet y = (↑C.S : Set V) := by
  have hyParts :=
    D.other_neighborSet_subset_core_parts M hregion
  have htwo : 1 < (G.neighborSet y).ncard := by
    change 1 < finiteDegree G y
    exact M.two_le_right_root_degree
  have htype : 2 ≤ D.chosen.rooted.core.typeNumber := by
    rw [hcore]
    simp [Core.typeNumber]
  have hyNotT :
      ∀ t ∈ C.T, ¬G.Adj y t := by
    intro t ht hyt
    obtain ⟨v, hv, hvt⟩ :=
      (G.neighborSet y).exists_ne_of_one_lt_ncard htwo t
    have hyv : G.Adj y v := by
      simpa [SimpleGraph.mem_neighborSet] using hv
    have hvParts := hyParts hv
    rw [hcore] at hvParts
    have hvClass : v ∈ C.S ∨ v ∈ C.T := by
      simpa [Core.S, Core.T] using hvParts
    have htv : G.Adj t v := by
      rcases hvClass with hvS | hvT
      · exact (C.cross_adj v hvS t ht).symm
      · exact C.clique_T
          (by simpa using ht) (by simpa using hvT) hvt.symm
    exact (D.not_adj_of_other_neighbors_of_two_le_type
      M htype hyt hyv) htv
  have hyS : G.neighborSet y ⊆ (↑C.S : Set V) := by
    intro v hv
    have hvParts := hyParts hv
    rw [hcore] at hvParts
    have hvClass : v ∈ C.S ∨ v ∈ C.T := by
      simpa [Core.S, Core.T] using hvParts
    rcases hvClass with hvS | hvT
    · exact hvS
    · exact False.elim
        (hyNotT v hvT
          (by simpa [SimpleGraph.mem_neighborSet] using hv))
  have hyEqS :
      G.neighborSet y = (↑C.S : Set V) := by
    apply Set.eq_of_subset_of_ncard_le hyS
    rw [Set.ncard_coe_finset, C.card_S]
    change 2 ≤ finiteDegree G y
    exact M.two_le_right_root_degree
  have hyNotS : y ∉ C.S := by
    intro hy
    apply D.chosen.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hy]
  have hyNotT' : y ∉ C.T := by
    intro hy
    apply D.chosen.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hy]
  let C' : TypeTwoCore G y D.chosen.rank := {
    S := C.S
    T := C.T
    rank_ge_two := C.rank_ge_two
    card_S := C.card_S
    card_T := C.card_T
    disjoint := C.disjoint
    root_not_mem_S := hyNotS
    root_not_mem_T := hyNotT'
    independent_S := C.independent_S
    clique_T := C.clique_T
    root_adj_S := by
      intro s hs
      have hsNeighbor : s ∈ G.neighborSet y := by
        rw [hyEqS]
        exact hs
      simpa [SimpleGraph.mem_neighborSet] using hsNeighbor
    cross_adj := C.cross_adj
  }
  let R : RootedCore G y x D.chosen.rank := {
    core := .typeTwo C'
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C',
        M.roots_ne, C.root_not_mem_S, C.root_not_mem_T]
  }
  have hattains : D.OtherRootAttainsChosenType := by
    refine ⟨D.chosen.rank, R, ?_⟩
    rw [hcore]
    rfl
  have hSx : (↑C.S : Set V) ⊆ G.neighborSet x := by
    intro s hs
    simpa [SimpleGraph.mem_neighborSet] using
      C.root_adj_S s (by simpa using hs)
  exact D.neighborSets_eq_of_other_attains_type
    hattains C.S hyS hSx

/-- Claim 3.5 in source type 3. -/
private theorem neighborSets_eq_T_of_singleton_typeThree
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (C : TypeThreeCore G x D.chosen.rank)
    (hcore : D.chosen.rooted.core = .typeThree C)
    (hregion : D.chosen.rooted.otherRegion = {y}) :
    G.neighborSet x = G.neighborSet y ∧
      G.neighborSet y = (↑C.T : Set V) := by
  have hyParts :=
    D.other_neighborSet_subset_core_parts M hregion
  have htype : 2 ≤ D.chosen.rooted.core.typeNumber := by
    rw [hcore]
    simp [Core.typeNumber]
  have hySide :
      G.neighborSet y ⊆ (↑C.T : Set V) ∨
        G.neighborSet y ⊆ (↑C.S : Set V) := by
    by_cases hT : ∃ t ∈ C.T, G.Adj y t
    · obtain ⟨t, ht, hyt⟩ := hT
      left
      intro v hv
      have hyv : G.Adj y v := by
        simpa [SimpleGraph.mem_neighborSet] using hv
      have hvParts := hyParts hv
      rw [hcore] at hvParts
      have hvClass : v ∈ C.S ∨ v ∈ C.T := by
        simpa [Core.S, Core.T] using hvParts
      rcases hvClass with hvS | hvT
      · have htv : G.Adj t v :=
          C.cross_adj t ht v hvS
        exact False.elim
          ((D.not_adj_of_other_neighbors_of_two_le_type
            M htype hyt hyv) htv)
      · exact hvT
    · right
      intro v hv
      have hvParts := hyParts hv
      rw [hcore] at hvParts
      have hvClass : v ∈ C.S ∨ v ∈ C.T := by
        simpa [Core.S, Core.T] using hvParts
      rcases hvClass with hvS | hvT
      · exact hvS
      · exact False.elim
          (hT ⟨v, hvT,
            by simpa [SimpleGraph.mem_neighborSet] using hv⟩)
  have hreverseUpper :
      D.reverse.rooted.core.typeNumber ≤ 3 := by
    cases D.reverse.rooted.core <;> simp [Core.typeNumber]
  have hchosenType :
      D.chosen.rooted.core.typeNumber = 3 := by
    rw [hcore]
    rfl
  have hreverseType :
      D.reverse.rooted.core.typeNumber =
        D.chosen.rooted.core.typeNumber := by
    have hpreferred := D.preferred.type_le
    rw [hchosenType] at hpreferred
    exact (Nat.le_antisymm hreverseUpper hpreferred).trans
      hchosenType.symm
  have hattains : D.OtherRootAttainsChosenType :=
    ⟨D.reverse.rank, D.reverse.rooted, hreverseType⟩
  have hTx : (↑C.T : Set V) ⊆ G.neighborSet x := by
    intro t ht
    simpa [SimpleGraph.mem_neighborSet] using
      C.root_adj_T t (by simpa using ht)
  rcases hySide with hyT | hyS
  · exact D.neighborSets_eq_of_other_attains_type
      hattains C.T hyT hTx
  · have hdegree :=
      D.chosen_degree_le_other_of_otherRootAttainsChosenType
        hattains
    change (G.neighborSet x).ncard ≤
      (G.neighborSet y).ncard at hdegree
    have hcardTS : C.T.card ≤ C.S.card := by
      have hTdegree :
          (↑C.T : Set V).ncard ≤
            (G.neighborSet x).ncard :=
        Set.ncard_le_ncard hTx
      have hdegreeS :
          (G.neighborSet y).ncard ≤
            (↑C.S : Set V).ncard :=
        Set.ncard_le_ncard hyS
      simpa using hTdegree.trans (hdegree.trans hdegreeS)
    have hlarge := C.card_T_lower
    rw [C.card_S] at hcardTS
    omega

/--
COY Claim 3.5 for a natural type-1 or type-3 working core: if the exterior
region is `{y}`, then both root neighborhoods are exactly the source set
`T`.
-/
theorem neighborSets_eq_T_of_natural_singleton
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype :
      D.chosen.rooted.core.typeNumber = 1 ∨
        D.chosen.rooted.core.typeNumber = 3) :
    G.neighborSet x = G.neighborSet y ∧
      G.neighborSet y =
        (↑D.chosen.rooted.core.T : Set V) := by
  change D.chosen.rooted.otherRegion = {y} at hregion
  cases hcore : D.chosen.rooted.core with
  | typeOne C =>
      simpa [hcore, Core.T] using
        neighborSets_eq_T_of_singleton_typeOne
          M D C hcore hregion
  | typeTwo C =>
      simp [hcore, Core.typeNumber] at htype
  | typeThree C =>
      simpa [hcore, Core.T] using
        neighborSets_eq_T_of_singleton_typeThree
          M D C hcore hregion

/--
COY Claim 3.5 for a natural type-2 working core: if the exterior region is
`{y}`, then both root neighborhoods are exactly the source set `S`.
-/
theorem neighborSets_eq_S_of_natural_singleton
    (M : MinimalCounterexample q G x y z)
    (D : PreferredOrientationData G x y z)
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) D.chosen))
    (hregion :
      (SelectedWorkingCore.natural hnot).rooted.otherRegion = {y})
    (htype : D.chosen.rooted.core.typeNumber = 2) :
    G.neighborSet x = G.neighborSet y ∧
      G.neighborSet y =
        (↑D.chosen.rooted.core.S : Set V) := by
  change D.chosen.rooted.otherRegion = {y} at hregion
  cases hcore : D.chosen.rooted.core with
  | typeOne C =>
      simp [hcore, Core.typeNumber] at htype
  | typeTwo C =>
      simpa [hcore, Core.S] using
        neighborSets_eq_S_of_singleton_typeTwo
          M D C hcore hregion
  | typeThree C =>
      simp [hcore, Core.typeNumber] at htype

end PreferredOrientationData

end COY

end DeanK5
