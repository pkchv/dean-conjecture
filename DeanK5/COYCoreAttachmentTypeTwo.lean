import DeanK5.COYCoreAttachmentNatural

/-!
# Exterior attachments to a natural type-2 COY core

This file proves the type-2 case of the unmodified-core form of COY
Claim 3.3.  For a lexicographically optimal rooted type-2 core, an exterior
vertex other than the second root has at most `rank + 1` neighbors in the
core.  Equality forces one of those neighbors to lie in the source set `T`.

The proof first uses type minimality to exclude a triangle consisting of the
root, the exterior vertex, and a vertex of `S`.  If the exterior vertex is
not adjacent to the root, an attachment larger than the asserted bound must
contain all of `S ∪ T`; adjoining the exterior vertex to `T` then contradicts
the maximal choice of `T`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace OptimalRootedCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y : V}

/-- The neighbors of `v` in the carrier, used for the type-2 count. -/
private noncomputable def typeTwoCoreNeighbors
    (R : OptimalRootedCore G x y) (v : V) : Finset V := by
  classical
  exact R.rooted.core.carrier.filter (G.Adj v)

@[simp] private theorem mem_typeTwoCoreNeighbors
    (R : OptimalRootedCore G x y) (v w : V) :
    w ∈ R.typeTwoCoreNeighbors v ↔
      w ∈ R.rooted.core.carrier ∧ G.Adj v w := by
  classical
  simp [typeTwoCoreNeighbors]

/-- The finite and set cardinalities of the type-2 core neighbors agree. -/
private theorem typeTwoCoreNeighbors_card_eq_ncard
    (R : OptimalRootedCore G x y) (v : V) :
    (R.typeTwoCoreNeighbors v).card =
      (G.neighborSet v ∩
        (↑R.rooted.core.carrier : Set V)).ncard := by
  classical
  have hset :
      G.neighborSet v ∩
          (↑R.rooted.core.carrier : Set V) =
        (↑(R.typeTwoCoreNeighbors v) : Set V) := by
    ext w
    simp [typeTwoCoreNeighbors, SimpleGraph.mem_neighborSet, and_comm]
  rw [hset, Set.ncard_coe_finset]

/--
A triangle `x-v-s-x`, with `s` in the `S`-side of a type-2 core, is a
rooted type-1 core.  The two exterior hypotheses keep the other root out of
this smaller-type core.
-/
private def rootedTypeOneOfTypeTwoTriangle
    (R : OptimalRootedCore G x y)
    (C : TypeTwoCore G x R.rank)
    (hcore : R.rooted.core = .typeTwo C)
    {v s : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (hs : s ∈ C.S)
    (hxv : G.Adj x v)
    (hvs : G.Adj v s) :
    RootedCore G x y 1 := by
  have hxs : G.Adj x s := C.root_adj_S s hs
  have hvx : v ≠ x := by
    intro h
    apply hvCarrier
    rw [h]
    exact R.rooted.core.root_mem_carrier
  have hsx : s ≠ x := by
    intro h
    exact C.root_not_mem_S (h ▸ hs)
  have hvs_ne : v ≠ s := hvs.ne
  have hyx : y ≠ x := by
    intro h
    subst y
    exact R.rooted.other_root_not_mem
      R.rooted.core.root_mem_carrier
  have hys : y ≠ s := by
    intro h
    apply R.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, h, hs]
  let C' : TypeOneCore G x 1 := {
    T := {v, s}
    rank_pos := le_rfl
    card_T := by simp [hvs_ne]
    root_not_mem := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvx.symm, hsx.symm⟩
    root_adj := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hxv
      · exact hxs
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show v ≠ s → G.Adj v s from fun _ => hvs)
  }
  exact {
    core := .typeOne C'
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C',
        hyx, hvy.symm, hys]
  }

/--
Type minimality excludes a triangle through the selected root, an exterior
vertex, and any vertex of the `S`-side of a type-2 core.
-/
private theorem no_root_exterior_S_triangle
    (R : OptimalRootedCore G x y)
    (C : TypeTwoCore G x R.rank)
    (hcore : R.rooted.core = .typeTwo C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (hxv : G.Adj x v) :
    ∀ s ∈ C.S, ¬G.Adj v s := by
  intro s hs hvs
  let R' :=
    R.rootedTypeOneOfTypeTwoTriangle C hcore
      hvCarrier hvy hs hxv hvs
  have hminimal := R.type_minimal R'
  rw [hcore] at hminimal
  change 2 ≤ 1 at hminimal
  omega

/-- The natural-core attachment bound in source type 2. -/
private theorem typeTwoCoreNeighbors_card_le
    (R : OptimalRootedCore G x y)
    (C : TypeTwoCore G x R.rank)
    (hcore : R.rooted.core = .typeTwo C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y) :
    (R.typeTwoCoreNeighbors v).card ≤ R.rank + 1 := by
  classical
  by_contra hbound
  have hlarge :
      R.rank + 2 ≤ (R.typeTwoCoreNeighbors v).card := by
    omega
  by_cases hxv : G.Adj x v
  · have hvS :
        ∀ s ∈ C.S, ¬G.Adj v s :=
      R.no_root_exterior_S_triangle C hcore hvCarrier hvy hxv
    have hsubset :
        R.typeTwoCoreNeighbors v ⊆ insert x C.T := by
      intro w hw
      have hwData := (R.mem_typeTwoCoreNeighbors v w).1 hw
      have hwClass :
          w = x ∨ w ∈ C.S ∨ w ∈ C.T := by
        rw [hcore] at hwData
        simpa [Core.carrier, Core.S, Core.T] using hwData.1
      rcases hwClass with rfl | hwS | hwT
      · simp
      · exact False.elim (hvS w hwS hwData.2)
      · simp [hwT]
    have hcard :
        (R.typeTwoCoreNeighbors v).card ≤ R.rank + 1 := by
      calc
        (R.typeTwoCoreNeighbors v).card ≤ (insert x C.T).card :=
          Finset.card_le_card hsubset
        _ = R.rank + 1 := by
          simp [C.root_not_mem_T, C.card_T]
    omega
  · have hsubset :
        R.typeTwoCoreNeighbors v ⊆ C.S ∪ C.T := by
      intro w hw
      have hwData := (R.mem_typeTwoCoreNeighbors v w).1 hw
      have hwClass :
          w = x ∨ w ∈ C.S ∨ w ∈ C.T := by
        rw [hcore] at hwData
        simpa [Core.carrier, Core.S, Core.T] using hwData.1
      rcases hwClass with rfl | hwS | hwT
      · exact False.elim (hxv hwData.2.symm)
      · exact Finset.mem_union_left C.T hwS
      · exact Finset.mem_union_right C.S hwT
    have hSTcard :
        (C.S ∪ C.T).card = R.rank + 2 := by
      rw [Finset.card_union_of_disjoint C.disjoint,
        C.card_S, C.card_T]
      omega
    have hneighbors :
        R.typeTwoCoreNeighbors v = C.S ∪ C.T := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [hSTcard]
      exact hlarge
    have hvAdjS :
        ∀ s ∈ C.S, G.Adj s v := by
      intro s hs
      have hsN : s ∈ R.typeTwoCoreNeighbors v := by
        rw [hneighbors]
        exact Finset.mem_union_left C.T hs
      exact ((R.mem_typeTwoCoreNeighbors v s).1 hsN).2.symm
    have hvAdjT :
        ∀ t ∈ C.T, G.Adj v t := by
      intro t ht
      have htN : t ∈ R.typeTwoCoreNeighbors v := by
        rw [hneighbors]
        exact Finset.mem_union_right C.S ht
      exact ((R.mem_typeTwoCoreNeighbors v t).1 htN).2
    have hvx : v ≠ x := by
      intro h
      apply hvCarrier
      rw [h]
      exact R.rooted.core.root_mem_carrier
    have hvS : v ∉ C.S := by
      intro hv
      apply hvCarrier
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, hv]
    have hvT : v ∉ C.T := by
      intro hv
      apply hvCarrier
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, hv]
    let C' : TypeTwoCore G x (R.rank + 1) :=
      C.insertTerminal v hvx hvS hvT hvAdjS hvAdjT
    have hyx : y ≠ x := by
      intro h
      subst y
      exact R.rooted.other_root_not_mem
        R.rooted.core.root_mem_carrier
    have hyS : y ∉ C.S := by
      intro hy
      apply R.rooted.other_root_not_mem
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, hy]
    have hyT : y ∉ C.T := by
      intro hy
      apply R.rooted.other_root_not_mem
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, hy]
    let R' : RootedCore G x y (R.rank + 1) := {
      core := .typeTwo C'
      other_root_not_mem := by
        simp [Core.carrier, Core.S, Core.T, C',
          TypeTwoCore.insertTerminal,
          hyx, hvy.symm, hyS, hyT]
    }
    have htype :
        R'.core.typeNumber = R.rooted.core.typeNumber := by
      rw [hcore]
      rfl
    have hS :
        R'.core.S.card = R.rooted.core.S.card := by
      rw [hcore]
      rfl
    have hmax := R.T_maximal R' htype hS
    simp [R', C', hcore, Core.T,
      TypeTwoCore.insertTerminal, hvT, C.card_T] at hmax

/--
Type-2 case of Claim 3.3 in its source set-cardinality form: an exterior
vertex other than the second root has at most `rank + 1` neighbors in the
natural core.
-/
theorem coreNeighbor_ncard_le_of_typeTwo
    (R : OptimalRootedCore G x y)
    (C : TypeTwoCore G x R.rank)
    (hcore : R.rooted.core = .typeTwo C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y) :
    (G.neighborSet v ∩
      (↑R.rooted.core.carrier : Set V)).ncard ≤ R.rank + 1 := by
  rw [← R.typeTwoCoreNeighbors_card_eq_ncard v]
  exact R.typeTwoCoreNeighbors_card_le C hcore hvCarrier hvy

/--
In the equality case of the type-2 attachment bound, the exterior vertex
has a neighbor in the source set `T`.
-/
theorem exists_T_neighbor_of_coreNeighbor_ncard_eq_typeTwo
    (R : OptimalRootedCore G x y)
    (C : TypeTwoCore G x R.rank)
    (hcore : R.rooted.core = .typeTwo C)
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
  have hsubset :
      R.typeTwoCoreNeighbors v ⊆ insert x C.S := by
    intro w hw
    have hwData := (R.mem_typeTwoCoreNeighbors v w).1 hw
    have hwClass :
        w = x ∨ w ∈ C.S ∨ w ∈ C.T := by
      rw [hcore] at hwData
      simpa [Core.carrier, Core.S, Core.T] using hwData.1
    rcases hwClass with rfl | hwS | hwT
    · simp
    · simp [hwS]
    · exact False.elim (hT ⟨w,
        by simpa [hcore, Core.T] using hwT, hwData.2⟩)
  have hcard :
      (R.typeTwoCoreNeighbors v).card ≤ 3 := by
    calc
      (R.typeTwoCoreNeighbors v).card ≤ (insert x C.S).card :=
        Finset.card_le_card hsubset
      _ = 3 := by
        simp [C.root_not_mem_S, C.card_S]
  rw [R.typeTwoCoreNeighbors_card_eq_ncard v, heq] at hcard
  have hrank : 2 ≤ R.rank := C.rank_ge_two
  have hrankEq : R.rank = 2 := by omega
  have hneighborCard :
      (R.typeTwoCoreNeighbors v).card = 3 := by
    rw [R.typeTwoCoreNeighbors_card_eq_ncard v, heq, hrankEq]
  have hneighbors :
      R.typeTwoCoreNeighbors v = insert x C.S := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hneighborCard]
    simp [C.root_not_mem_S, C.card_S]
  have hxN : x ∈ R.typeTwoCoreNeighbors v := by
    rw [hneighbors]
    simp
  have hxv : G.Adj x v :=
    ((R.mem_typeTwoCoreNeighbors v x).1 hxN).2.symm
  have hSnonempty : C.S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have hcard := C.card_S
    rw [h, Finset.card_empty] at hcard
    omega
  obtain ⟨s, hs⟩ := hSnonempty
  have hsN : s ∈ R.typeTwoCoreNeighbors v := by
    rw [hneighbors]
    simp [hs]
  have hvs : G.Adj v s :=
    ((R.mem_typeTwoCoreNeighbors v s).1 hsN).2
  exact R.no_root_exterior_S_triangle C hcore
    hvCarrier hvy hxv s hs hvs

end OptimalRootedCore

end COY

end DeanK5
