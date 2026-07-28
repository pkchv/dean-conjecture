import DeanK5.COYCoreAdapters

/-!
# Uniform bounded catalogues to the `S`-side of a type-three core

A type-three core supplies admissible paths of lengths
`2, 4, ..., 2n` from its root to every selected vertex of `S`.
The construction may reserve one vertex of `T`, which is possible because
the source definition always gives at least two vertices in `T`.

This file packages the endpoint-independent lengths and the common support
bound needed by COY Fact 1.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeThreeCore

variable [DecidableEq V]
  {G : SimpleGraph V} {x : V} {ℓ n : ℕ}

/--
A uniform collection of bounded admissible catalogues from `x` to every
vertex of the `S`-side of a type-three core.
-/
structure UniformSCatalogue
    (C : TypeThreeCore G x ℓ) (n : ℕ) where
  /-- One reserved `T`-vertex omitted from every selected path. -/
  deleted : V
  /-- The reserved vertex belongs to `T`. -/
  deleted_mem : deleted ∈ C.T
  /-- The bounded path catalogue to a selected `S`-vertex. -/
  family :
    ∀ target : V, target ∈ C.S →
      AdmissiblePathFamily G x target n
  /-- Every selected catalogue starts at length two. -/
  family_start :
    ∀ target htarget, (family target htarget).start = 2
  /-- Every selected catalogue has common difference two. -/
  family_step :
    ∀ target htarget, (family target htarget).step = 2
  /-- Every selected path stays in the original core carrier. -/
  support :
    ∀ target htarget i v,
      v ∈ ((family target htarget).path i).walk.support →
        v ∈ insert x (C.S ∪ C.T)

private theorem bounded_sCatalogue_start
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ) :
    (C.admissiblePathsToSAfterDeleting
      target deleted htarget hdeleted
      n hnOne hnFour hnCore).start = 2 := by
  unfold admissiblePathsToSAfterDeleting
  unfold PointedTypeThreeSCore.factTwoTypeThreeBounded
  interval_cases n <;> rfl

private theorem bounded_sCatalogue_step
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ) :
    (C.admissiblePathsToSAfterDeleting
      target deleted htarget hdeleted
      n hnOne hnFour hnCore).step = 2 := by
  unfold admissiblePathsToSAfterDeleting
  unfold PointedTypeThreeSCore.factTwoTypeThreeBounded
  interval_cases n <;> rfl

/-- Build the uniform bounded `S`-catalogue of a type-three core. -/
noncomputable def uniformSCatalogue
    (C : TypeThreeCore G x ℓ)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ) :
    C.UniformSCatalogue n := by
  classical
  have hTCard : 1 ≤ C.T.card := by
    have htwo : 2 ≤ C.T.card :=
      (Nat.le_max_right (ℓ + 1) 2).trans C.card_T_lower
    omega
  have hTNonempty : C.T.Nonempty :=
    Finset.card_pos.mp hTCard
  let deleted : V := Classical.choose hTNonempty
  have hdeleted : deleted ∈ C.T :=
    Classical.choose_spec hTNonempty
  exact {
    deleted := deleted
    deleted_mem := hdeleted
    family := fun target htarget =>
      C.admissiblePathsToSAfterDeleting
        target deleted htarget hdeleted
        n hnOne hnFour hnCore
    family_start := by
      intro target htarget
      exact bounded_sCatalogue_start C target deleted
        htarget hdeleted hnOne hnFour hnCore
    family_step := by
      intro target htarget
      exact bounded_sCatalogue_step C target deleted
        htarget hdeleted hnOne hnFour hnCore
    support := by
      intro target htarget i v hv
      have hv' :=
        C.admissiblePathsToSAfterDeleting_support
          target deleted htarget hdeleted
          n hnOne hnFour hnCore i v hv
      rcases Finset.mem_insert.mp hv' with rfl | hv'
      · simp
      · rcases Finset.mem_union.mp hv' with hvS | hvT
        · simp [hvS]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_union_right C.S
              ((Finset.mem_erase.mp hvT).2))
  }

namespace UniformSCatalogue

variable {C : TypeThreeCore G x ℓ}

/--
Corresponding paths in catalogues with different `S`-endpoints have the
same length.
-/
theorem equal_length
    (U : C.UniformSCatalogue n)
    (target₁ target₂ : V)
    (htarget₁ : target₁ ∈ C.S)
    (htarget₂ : target₂ ∈ C.S)
    (i : Fin n) :
    ((U.family target₁ htarget₁).path i).length =
      ((U.family target₂ htarget₂).path i).length := by
  rw [
    (U.family target₁ htarget₁).length_path i,
    (U.family target₂ htarget₂).length_path i,
    U.family_start target₁ htarget₁,
    U.family_start target₂ htarget₂,
    U.family_step target₁ htarget₁,
    U.family_step target₂ htarget₂]

end UniformSCatalogue

end TypeThreeCore

end COY

end DeanK5
