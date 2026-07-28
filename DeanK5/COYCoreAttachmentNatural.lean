import DeanK5.COYCoreOrientation
import DeanK5.COYCoreExtensions

/-!
# Exterior attachments to a naturally oriented COY core

This file proves the unmodified-core form of COY Claim 3.3.  For a
lexicographically optimal rooted core, an exterior vertex other than the
second root has at most `rank + 1` neighbors in the core.  Equality forces
one of those neighbors to lie in the source set `T`.

The proof uses only the defining minimality and maximality properties of an
`OptimalRootedCore`.  In particular, it applies to an arbitrary finite simple
graph and does not use connectivity or any minimal-counterexample hypothesis.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace OptimalRootedCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y : V}

/-- The neighbors of `v` that lie in the carrier of the selected core. -/
private noncomputable def coreNeighbors
    (R : OptimalRootedCore G x y) (v : V) : Finset V := by
  classical
  exact R.rooted.core.carrier.filter (G.Adj v)

@[simp] private theorem mem_coreNeighbors
    (R : OptimalRootedCore G x y) (v w : V) :
    w ∈ R.coreNeighbors v ↔
      w ∈ R.rooted.core.carrier ∧ G.Adj v w := by
  classical
  simp [coreNeighbors]

/-- Finset and set formulations of the number of core neighbors agree. -/
private theorem coreNeighbors_card_eq_ncard
    (R : OptimalRootedCore G x y) (v : V) :
    (R.coreNeighbors v).card =
      (G.neighborSet v ∩
        (↑R.rooted.core.carrier : Set V)).ncard := by
  classical
  have hset :
      G.neighborSet v ∩
          (↑R.rooted.core.carrier : Set V) =
        (↑(R.coreNeighbors v) : Set V) := by
    ext w
    simp [coreNeighbors, SimpleGraph.mem_neighborSet, and_comm]
  rw [hset, Set.ncard_coe_finset]

/--
A triangle through the selected root gives a rooted type-1 core.  The
exterior hypotheses ensure that the second root remains outside it.
-/
private def rootedTypeOneOfRootTriangle
    (R : OptimalRootedCore G x y)
    {v t : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (htCarrier : t ∈ R.rooted.core.carrier)
    (hxv : G.Adj x v)
    (hxt : G.Adj x t)
    (hvt : G.Adj v t) :
    RootedCore G x y 1 := by
  have hvx : v ≠ x := by
    intro h
    apply hvCarrier
    rw [h]
    exact R.rooted.core.root_mem_carrier
  have htx : t ≠ x := hxt.symm.ne
  have hyx : y ≠ x := by
    intro h
    subst y
    exact R.rooted.other_root_not_mem
      R.rooted.core.root_mem_carrier
  have hyt : y ≠ t := by
    intro h
    apply R.rooted.other_root_not_mem
    simpa [h] using htCarrier
  let C : TypeOneCore G x 1 := {
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
    core := .typeOne C
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T, C,
        hyx,
        hvy.symm, hyt]
  }

/--
An exterior vertex cannot complete a triangle through the selected root
when the optimal core has type 2 or 3.
-/
private theorem no_root_triangle_of_type_gt_one
    (R : OptimalRootedCore G x y)
    {v t : V}
    (htype : 1 < R.rooted.core.typeNumber)
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y)
    (htCarrier : t ∈ R.rooted.core.carrier)
    (hxv : G.Adj x v)
    (hxt : G.Adj x t)
    (hvt : G.Adj v t) :
    False := by
  let R' :=
    R.rootedTypeOneOfRootTriangle hvCarrier hvy htCarrier hxv hxt hvt
  have hminimal := R.type_minimal R'
  change R.rooted.core.typeNumber ≤ 1 at hminimal
  omega

/-- The attachment bound when the selected optimal core has source type 1. -/
private theorem coreNeighbors_card_le_typeOne
    (R : OptimalRootedCore G x y)
    (C : TypeOneCore G x R.rank)
    (hcore : R.rooted.core = .typeOne C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y) :
    (R.coreNeighbors v).card ≤ R.rank + 1 := by
  by_contra hbound
  have hlarge : R.rank + 2 ≤ (R.coreNeighbors v).card := by
    omega
  have hcarrierCard :
      R.rooted.core.carrier.card = R.rank + 2 := by
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T,
      C.root_not_mem, C.card_T]
  have hneighborsEq :
      R.coreNeighbors v = R.rooted.core.carrier := by
    classical
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.filter_subset (G.Adj v) R.rooted.core.carrier
    · rw [hcarrierCard]
      exact hlarge
  have hxv : G.Adj x v := by
    have hxmem : x ∈ R.coreNeighbors v := by
      rw [hneighborsEq]
      exact R.rooted.core.root_mem_carrier
    exact (R.mem_coreNeighbors v x).1 hxmem |>.2.symm
  have hvT : ∀ t ∈ C.T, G.Adj v t := by
    intro t ht
    have htCarrier : t ∈ R.rooted.core.carrier := by
      rw [hcore]
      simp [Core.carrier, Core.S, Core.T, ht]
    have htmem : t ∈ R.coreNeighbors v := by
      rw [hneighborsEq]
      exact htCarrier
    exact (R.mem_coreNeighbors v t).1 htmem |>.2
  have hvx : v ≠ x := by
    intro h
    apply hvCarrier
    rw [h]
    exact R.rooted.core.root_mem_carrier
  have hvTmem : v ∉ C.T := by
    intro hv
    apply hvCarrier
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hv]
  let C' : TypeOneCore G x (R.rank + 1) :=
    C.insertTerminal v hvx hvTmem hxv hvT
  have hyx : y ≠ x := by
    intro h
    subst y
    exact R.rooted.other_root_not_mem
      R.rooted.core.root_mem_carrier
  let R' : RootedCore G x y (R.rank + 1) := {
    core := .typeOne C'
    other_root_not_mem := by
      have hyT : y ∉ C.T := by
        intro hy
        apply R.rooted.other_root_not_mem
        rw [hcore]
        simp [Core.carrier, Core.S, Core.T, hy]
      simp [Core.carrier, Core.S, Core.T, C',
        TypeOneCore.insertTerminal, hyx, hvy.symm, hyT]
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
  simp [R', C', hcore, Core.T, TypeOneCore.insertTerminal,
    hvTmem] at hmax

/--
Type-1 case of the natural-core attachment bound in its source set-cardinal
form.
-/
theorem coreNeighbor_ncard_le_of_typeOne
    (R : OptimalRootedCore G x y)
    (C : TypeOneCore G x R.rank)
    (hcore : R.rooted.core = .typeOne C)
    {v : V}
    (hvCarrier : v ∉ R.rooted.core.carrier)
    (hvy : v ≠ y) :
    (G.neighborSet v ∩
      (↑R.rooted.core.carrier : Set V)).ncard ≤ R.rank + 1 := by
  rw [← R.coreNeighbors_card_eq_ncard v]
  exact R.coreNeighbors_card_le_typeOne C hcore hvCarrier hvy

/--
In the equality case of the type-1 bound, the exterior vertex has a
neighbor in the source set `T`.
-/
theorem exists_T_neighbor_of_coreNeighbor_ncard_eq_typeOne
    (R : OptimalRootedCore G x y)
    (C : TypeOneCore G x R.rank)
    (hcore : R.rooted.core = .typeOne C)
    {v : V}
    (heq :
      (G.neighborSet v ∩
        (↑R.rooted.core.carrier : Set V)).ncard =
        R.rank + 1) :
    ∃ t ∈ R.rooted.core.T, G.Adj v t := by
  classical
  by_contra hT
  have hsubset : R.coreNeighbors v ⊆ {x} := by
    intro w hw
    have hwData := (R.mem_coreNeighbors v w).1 hw
    have hwClass : w = x ∨ w ∈ C.T := by
      rw [hcore] at hwData
      simpa [Core.carrier, Core.S, Core.T] using hwData.1
    rcases hwClass with rfl | hwT
    · simp
    · exact False.elim (hT ⟨w,
        by simpa [hcore, Core.T] using hwT, hwData.2⟩)
  have hcard : (R.coreNeighbors v).card ≤ 1 := by
    calc
      (R.coreNeighbors v).card ≤ ({x} : Finset V).card :=
        Finset.card_le_card hsubset
      _ = 1 := by simp
  rw [R.coreNeighbors_card_eq_ncard v, heq] at hcard
  have hrank := C.rank_pos
  omega

end OptimalRootedCore

end COY

end DeanK5
