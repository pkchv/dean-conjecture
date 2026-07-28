import DeanK5.COYCoreAdapters

/-!
# Uniform bounded catalogues to the `T`-side of a COY core

Every one of the three COY core types supplies the bounded
semi-admissible path catalogue from the core root to any selected vertex
of its `T`-side.  This file packages those three constructions behind the
common `Core` interface.

For fixed core and catalogue size, the first length and common difference
do not depend on the selected endpoint.  Every path is supported on the
core carrier.  These two facts are the form needed when several
core-to-`T` catalogues are combined with an exterior path construction.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace Core

variable [DecidableEq V]
  {G : SimpleGraph V} {x : V} {ℓ n : ℕ}

/-- The common first length of the bounded `T`-catalogues of a core. -/
def tCatalogueStart : Core G x ℓ → ℕ
  | .typeOne _ => 1
  | .typeTwo _ => 2
  | .typeThree _ => 1

/-- The common difference in the bounded `T`-catalogues of a core. -/
def tCatalogueStep : Core G x ℓ → ℕ
  | .typeOne _ => 1
  | .typeTwo _ => 1
  | .typeThree _ => 2

private theorem typeOne_tCatalogue_start
    (C : TypeOneCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsTo target htarget n
      hnOne hnFour hnCore).start = 1 := by
  unfold TypeOneCore.semiAdmissiblePathsTo
  unfold PointedTypeOneCore.factTwoTypeOneBounded
  interval_cases n <;> rfl

private theorem typeOne_tCatalogue_step
    (C : TypeOneCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsTo target htarget n
      hnOne hnFour hnCore).step = 1 := by
  unfold TypeOneCore.semiAdmissiblePathsTo
  unfold PointedTypeOneCore.factTwoTypeOneBounded
  interval_cases n <;> rfl

private theorem typeTwo_tCatalogue_start
    (C : TypeTwoCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).start = 2 := by
  unfold TypeTwoCore.semiAdmissiblePathsToT
  unfold PointedTypeTwoTCore.factTwoTypeTwoTBounded
  interval_cases n <;> rfl

private theorem typeTwo_tCatalogue_step
    (C : TypeTwoCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).step = 1 := by
  unfold TypeTwoCore.semiAdmissiblePathsToT
  unfold PointedTypeTwoTCore.factTwoTypeTwoTBounded
  interval_cases n <;> rfl

private theorem typeThree_tCatalogue_start
    (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).start = 1 := by
  unfold TypeThreeCore.semiAdmissiblePathsToT
  unfold PointedTypeThreeTCore.factTwoTypeThreeTBounded
  interval_cases n <;> rfl

private theorem typeThree_tCatalogue_step
    (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).step = 2 := by
  unfold TypeThreeCore.semiAdmissiblePathsToT
  unfold PointedTypeThreeTCore.factTwoTypeThreeTBounded
  interval_cases n <;> rfl

/--
The bounded semi-admissible catalogue from the root of an arbitrary COY
core to a selected vertex of its `T`-side.
-/
noncomputable def semiAdmissiblePathsToT
    (C : Core G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target n := by
  cases C with
  | typeOne C =>
      exact C.semiAdmissiblePathsTo target
        (by simpa [T] using htarget)
        n hnOne hnFour hnCore
  | typeTwo C =>
      exact C.semiAdmissiblePathsToT target
        (by simpa [T] using htarget)
        n hnOne hnFour hnCore
  | typeThree C =>
      exact C.semiAdmissiblePathsToT target
        (by simpa [T] using htarget)
        n hnOne hnFour hnCore

/-- The first length of the general core catalogue is endpoint-independent. -/
theorem semiAdmissiblePathsToT_start
    (C : Core G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).start = C.tCatalogueStart := by
  cases C with
  | typeOne C =>
      simpa [semiAdmissiblePathsToT, tCatalogueStart] using
        typeOne_tCatalogue_start C target
          (by simpa [T] using htarget)
          hnOne hnFour hnCore
  | typeTwo C =>
      simpa [semiAdmissiblePathsToT, tCatalogueStart] using
        typeTwo_tCatalogue_start C target
          (by simpa [T] using htarget)
          hnOne hnFour hnCore
  | typeThree C =>
      simpa [semiAdmissiblePathsToT, tCatalogueStart] using
        typeThree_tCatalogue_start C target
          (by simpa [T] using htarget)
          hnOne hnFour hnCore

/-- The common difference of the general core catalogue is endpoint-independent. -/
theorem semiAdmissiblePathsToT_step
    (C : Core G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    (C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).step = C.tCatalogueStep := by
  cases C with
  | typeOne C =>
      simpa [semiAdmissiblePathsToT, tCatalogueStep] using
        typeOne_tCatalogue_step C target
          (by simpa [T] using htarget)
          hnOne hnFour hnCore
  | typeTwo C =>
      simpa [semiAdmissiblePathsToT, tCatalogueStep] using
        typeTwo_tCatalogue_step C target
          (by simpa [T] using htarget)
          hnOne hnFour hnCore
  | typeThree C =>
      simpa [semiAdmissiblePathsToT, tCatalogueStep] using
        typeThree_tCatalogue_step C target
          (by simpa [T] using htarget)
          hnOne hnFour hnCore

/-- Every path in the general `T`-catalogue stays in the core carrier. -/
theorem semiAdmissiblePathsToT_support
    (C : Core G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1)
    (i : Fin n) (v : V)
    (hv : v ∈ ((C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore).path i).walk.support) :
    v ∈ C.carrier := by
  cases C with
  | typeOne C =>
      have hv' := C.semiAdmissiblePathsTo_support target
        (by simpa [T] using htarget)
        n hnOne hnFour hnCore i v
        (by simpa [semiAdmissiblePathsToT] using hv)
      simpa [carrier, S, T] using hv'
  | typeTwo C =>
      have hv' := C.semiAdmissiblePathsToT_support target
        (by simpa [T] using htarget)
        n hnOne hnFour hnCore i v
        (by simpa [semiAdmissiblePathsToT] using hv)
      simpa [carrier, S, T] using hv'
  | typeThree C =>
      have hv' := C.semiAdmissiblePathsToT_support target
        (by simpa [T] using htarget)
        n hnOne hnFour hnCore i v
        (by simpa [semiAdmissiblePathsToT] using hv)
      simpa [carrier, S, T] using hv'

/--
A uniform collection of bounded catalogues to every vertex of a core's
`T`-side.
-/
structure UniformTCatalogue
    (C : Core G x ℓ) (n : ℕ) where
  /-- The endpoint-independent first length. -/
  start : ℕ
  /-- The endpoint-independent common difference. -/
  step : ℕ
  /-- The bounded path catalogue to a selected `T`-vertex. -/
  family :
    ∀ target : V, target ∈ C.T →
      SemiAdmissiblePathFamily G x target n
  /-- Every selected catalogue has the packaged first length. -/
  family_start :
    ∀ target htarget, (family target htarget).start = start
  /-- Every selected catalogue has the packaged common difference. -/
  family_step :
    ∀ target htarget, (family target htarget).step = step
  /-- Every selected path stays in the core carrier. -/
  support :
    ∀ target htarget i v,
      v ∈ ((family target htarget).path i).walk.support →
        v ∈ C.carrier

/-- Build the uniform bounded `T`-catalogue of an arbitrary COY core. -/
noncomputable def uniformTCatalogue
    (C : Core G x ℓ)
    (n : ℕ) (hnOne : 1 ≤ n) (hnFour : n ≤ 4)
    (hnCore : n ≤ ℓ + 1) :
    C.UniformTCatalogue n where
  start := C.tCatalogueStart
  step := C.tCatalogueStep
  family target htarget :=
    C.semiAdmissiblePathsToT target htarget n
      hnOne hnFour hnCore
  family_start target htarget :=
    C.semiAdmissiblePathsToT_start target htarget
      hnOne hnFour hnCore
  family_step target htarget :=
    C.semiAdmissiblePathsToT_step target htarget
      hnOne hnFour hnCore
  support target htarget i v hv :=
    C.semiAdmissiblePathsToT_support target htarget
      hnOne hnFour hnCore i v hv

namespace UniformTCatalogue

variable {C : Core G x ℓ}

/--
Corresponding paths in catalogues with different `T`-endpoints have the
same length.
-/
theorem equal_length
    (U : C.UniformTCatalogue n)
    (target₁ target₂ : V)
    (htarget₁ : target₁ ∈ C.T)
    (htarget₂ : target₂ ∈ C.T)
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

end UniformTCatalogue

end Core

end COY

end DeanK5
