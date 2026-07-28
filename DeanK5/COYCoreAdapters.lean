import DeanK5.COYCoreStructure
import DeanK5.COYCores

/-!
# Pointing source-level COY cores

The source definitions store their parts as finite vertex sets, while the
explicit path catalogues use embeddings from `Fin n`.  This file supplies
the finite enumerations and proves that selected source vertices give the
pointed certificates required by the path constructors.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- Enumerate a finite set whose cardinality is known exactly. -/
noncomputable def finsetEmbeddingOfCardEq
    [DecidableEq V]
    (A : Finset V) {n : ℕ} (hcard : A.card = n) :
    Fin n ↪ V :=
  (Finset.equivFinOfCardEq hcard).symm.toEmbedding.trans
    (Function.Embedding.subtype (fun v => v ∈ A))

@[simp] theorem finsetEmbeddingOfCardEq_mem
    [DecidableEq V]
    (A : Finset V) {n : ℕ} (hcard : A.card = n)
    (i : Fin n) :
    finsetEmbeddingOfCardEq A hcard i ∈ A := by
  change ((Finset.equivFinOfCardEq hcard).symm i : A).1 ∈ A
  exact ((Finset.equivFinOfCardEq hcard).symm i).2

/-- Select and enumerate `n` distinct vertices from a finite set of size at least `n`. -/
noncomputable def finsetEmbeddingOfCardLE
    [DecidableEq V]
    (A : Finset V) {n : ℕ} (hcard : n ≤ A.card) :
    Fin n ↪ V := by
  have hcard' : n ≤ Fintype.card A := by
    simpa using hcard
  exact
    (Fin.castLEEmb hcard').trans
      (Fintype.equivFin A).symm.toEmbedding |>.trans
        (Function.Embedding.subtype (fun v => v ∈ A))

@[simp] theorem finsetEmbeddingOfCardLE_mem
    [DecidableEq V]
    (A : Finset V) {n : ℕ} (hcard : n ≤ A.card)
    (i : Fin n) :
    finsetEmbeddingOfCardLE A hcard i ∈ A := by
  change
    (((Fintype.equivFin A).symm
      (Fin.castLE (by simpa using hcard) i) : A).1 ∈ A)
  exact
    ((Fintype.equivFin A).symm
      (Fin.castLE (by simpa using hcard) i)).2

namespace TypeOneCore

variable [DecidableEq V] {G : SimpleGraph V} {x : V} {ℓ : ℕ}

/--
Point a source type-1 core at one of its clique vertices.
-/
noncomputable def pointAt
    (C : TypeOneCore G x ℓ) (target : V)
    (htarget : target ∈ C.T) :
    PointedTypeOneCore G x target ℓ := by
  let remaining := C.T.erase target
  have hremainingCard : remaining.card = ℓ := by
    dsimp [remaining]
    rw [Finset.card_erase_of_mem htarget, C.card_T]
    omega
  let other : Fin ℓ ↪ V :=
    finsetEmbeddingOfCardEq remaining hremainingCard
  have hotherRemaining (i : Fin ℓ) :
      other i ∈ remaining :=
    finsetEmbeddingOfCardEq_mem remaining hremainingCard i
  have hotherT (i : Fin ℓ) :
      other i ∈ C.T :=
    (Finset.mem_erase.1 (hotherRemaining i)).2
  have hotherNeTarget (i : Fin ℓ) :
      other i ≠ target :=
    (Finset.mem_erase.1 (hotherRemaining i)).1
  exact {
    other := other
    x_ne_target := by
      intro h
      subst target
      exact C.root_not_mem htarget
    x_ne_other := by
      intro i h
      apply C.root_not_mem
      simpa [h] using hotherT i
    target_ne_other := by
      intro i
      exact (hotherNeTarget i).symm
    adj_x_target := C.root_adj target htarget
    adj_x_other := by
      intro i
      exact C.root_adj (other i) (hotherT i)
    adj_other_target := by
      intro i
      exact C.clique_T (hotherT i) htarget
        (hotherNeTarget i)
    adj_other := by
      intro i j hij
      exact C.clique_T (hotherT i) (hotherT j)
        (other.injective.ne hij)
  }

/--
The bounded type-1 path catalogue obtained from a source core.
-/
noncomputable def semiAdmissiblePathsTo
    (C : TypeOneCore G x ℓ) (target : V)
    (htarget : target ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target q :=
  (C.pointAt target htarget).factTwoTypeOneBounded
    hqOne hqFour hqCore

/--
Every path in the source type-1 catalogue stays in the core carrier
`{x} ∪ T`.
-/
theorem semiAdmissiblePathsTo_support
    (C : TypeOneCore G x ℓ) (target : V)
    (htarget : target ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.semiAdmissiblePathsTo target htarget q
      hqOne hqFour hqCore).path i).walk.support) :
    z ∈ insert x C.T := by
  have hother (j : Fin ℓ) :
      (C.pointAt target htarget).other j ∈ C.T := by
    simp only [pointAt]
    exact Finset.mem_of_mem_erase
      (finsetEmbeddingOfCardEq_mem
        (C.T.erase target) _ j)
  rcases PointedTypeOneCore.factTwoTypeOneBounded_support
      (C.pointAt target htarget) hqOne hqFour hqCore i z hz with
    rfl | rfl | ⟨j, rfl⟩
  · simp
  · simp [htarget]
  · simp [hother j]

end TypeOneCore

namespace TypeTwoCore

variable [DecidableEq V] {G : SimpleGraph V} {x : V} {ℓ : ℕ}

/-- Point a source type-2 core at a vertex of its `S`-side. -/
noncomputable def pointAtS
    (C : TypeTwoCore G x ℓ) (target : V)
    (htarget : target ∈ C.S) :
    PointedTypeTwoSCore G x target ℓ := by
  let remainingS := C.S.erase target
  have hremainingSCard : remainingS.card = 1 := by
    dsimp [remainingS]
    rw [Finset.card_erase_of_mem htarget, C.card_S]
  let otherSEmbedding : Fin 1 ↪ V :=
    finsetEmbeddingOfCardEq remainingS hremainingSCard
  let otherS : V := otherSEmbedding 0
  have hotherSRemaining : otherS ∈ remainingS :=
    finsetEmbeddingOfCardEq_mem remainingS hremainingSCard 0
  have hotherS : otherS ∈ C.S :=
    (Finset.mem_erase.1 hotherSRemaining).2
  have hotherSNeTarget : otherS ≠ target :=
    (Finset.mem_erase.1 hotherSRemaining).1
  let t : Fin ℓ ↪ V :=
    finsetEmbeddingOfCardEq C.T C.card_T
  have ht (i : Fin ℓ) : t i ∈ C.T :=
    finsetEmbeddingOfCardEq_mem C.T C.card_T i
  have hdisjoint :
      ∀ {s t : V}, s ∈ C.S → t ∈ C.T → s ≠ t := by
    intro s t hs ht hst
    subst t
    exact Finset.disjoint_left.1 C.disjoint hs ht
  exact {
    otherS := otherS
    t := t
    x_ne_target := by
      intro h
      subst target
      exact C.root_not_mem_S htarget
    x_ne_otherS := by
      intro h
      apply C.root_not_mem_S
      simpa [h] using hotherS
    x_ne_t := by
      intro i h
      apply C.root_not_mem_T
      simpa [h] using ht i
    otherS_ne_target := hotherSNeTarget
    otherS_ne_t := by
      intro i
      exact hdisjoint hotherS (ht i)
    t_ne_target := by
      intro i
      exact (hdisjoint htarget (ht i)).symm
    adj_x_otherS := C.root_adj_S otherS hotherS
    adj_otherS_t := by
      intro i
      exact C.cross_adj otherS hotherS (t i) (ht i)
    adj_t_target := by
      intro i
      exact (C.cross_adj target htarget (t i) (ht i)).symm
    adj_t := by
      intro i j hij
      exact C.clique_T (ht i) (ht j) (t.injective.ne hij)
  }

/-- Point a source type-2 core at a vertex of its clique side `T`. -/
noncomputable def pointAtT
    (C : TypeTwoCore G x ℓ) (target : V)
    (htarget : target ∈ C.T) :
    PointedTypeTwoTCore G x target ℓ := by
  let remainingT := C.T.erase target
  have hremainingTCard : remainingT.card = ℓ - 1 := by
    dsimp [remainingT]
    rw [Finset.card_erase_of_mem htarget, C.card_T]
  let s : Fin 2 ↪ V :=
    finsetEmbeddingOfCardEq C.S C.card_S
  let otherT : Fin (ℓ - 1) ↪ V :=
    finsetEmbeddingOfCardEq remainingT hremainingTCard
  have hs (i : Fin 2) : s i ∈ C.S :=
    finsetEmbeddingOfCardEq_mem C.S C.card_S i
  have hotherTRemaining (i : Fin (ℓ - 1)) :
      otherT i ∈ remainingT :=
    finsetEmbeddingOfCardEq_mem remainingT hremainingTCard i
  have hotherT (i : Fin (ℓ - 1)) :
      otherT i ∈ C.T :=
    (Finset.mem_erase.1 (hotherTRemaining i)).2
  have hotherTNeTarget (i : Fin (ℓ - 1)) :
      otherT i ≠ target :=
    (Finset.mem_erase.1 (hotherTRemaining i)).1
  have hdisjoint :
      ∀ {s t : V}, s ∈ C.S → t ∈ C.T → s ≠ t := by
    intro s t hs ht hst
    subst t
    exact Finset.disjoint_left.1 C.disjoint hs ht
  exact {
    rank_ge_two := C.rank_ge_two
    s := s
    otherT := otherT
    x_ne_target := by
      intro h
      subst target
      exact C.root_not_mem_T htarget
    x_ne_s := by
      intro i h
      apply C.root_not_mem_S
      simpa [h] using hs i
    x_ne_otherT := by
      intro i h
      apply C.root_not_mem_T
      simpa [h] using hotherT i
    s_ne_target := by
      intro i
      exact hdisjoint (hs i) htarget
    otherT_ne_target := hotherTNeTarget
    s_ne_otherT := by
      intro i j
      exact hdisjoint (hs i) (hotherT j)
    adj_x_s := by
      intro i
      exact C.root_adj_S (s i) (hs i)
    adj_s_target := by
      intro i
      exact C.cross_adj (s i) (hs i) target htarget
    adj_s_otherT := by
      intro i j
      exact C.cross_adj (s i) (hs i)
        (otherT j) (hotherT j)
    adj_otherT_target := by
      intro i
      exact C.clique_T (hotherT i) htarget
        (hotherTNeTarget i)
    adj_otherT := by
      intro i j hij
      exact C.clique_T (hotherT i) (hotherT j)
        (otherT.injective.ne hij)
  }

/-- The bounded type-2 catalogue to a selected `S`-vertex. -/
noncomputable def admissiblePathsToS
    (C : TypeTwoCore G x ℓ) (target : V)
    (htarget : target ∈ C.S)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ) :
    AdmissiblePathFamily G x target q :=
  (C.pointAtS target htarget).factTwoTypeTwoBounded
    hqOne hqFour hqCore

/-- The bounded type-2 catalogue to a selected `T`-vertex. -/
noncomputable def semiAdmissiblePathsToT
    (C : TypeTwoCore G x ℓ) (target : V)
    (htarget : target ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target q :=
  (C.pointAtT target htarget).factTwoTypeTwoTBounded
    hqOne hqFour hqCore

/--
Every path in the source type-2 catalogue to `S` stays in the core
carrier `{x} ∪ S ∪ T`.
-/
theorem admissiblePathsToS_support
    (C : TypeTwoCore G x ℓ) (target : V)
    (htarget : target ∈ C.S)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.admissiblePathsToS target htarget q
      hqOne hqFour hqCore).path i).walk.support) :
    z ∈ insert x (C.S ∪ C.T) := by
  have hotherS :
      (C.pointAtS target htarget).otherS ∈ C.S := by
    simp only [pointAtS]
    exact Finset.mem_of_mem_erase
      (finsetEmbeddingOfCardEq_mem
        (C.S.erase target) _ 0)
  have ht (j : Fin ℓ) :
      (C.pointAtS target htarget).t j ∈ C.T := by
    simp only [pointAtS]
    exact finsetEmbeddingOfCardEq_mem C.T C.card_T j
  rcases PointedTypeTwoSCore.factTwoTypeTwoBounded_support
      (C.pointAtS target htarget) hqOne hqFour hqCore i z hz with
    rfl | rfl | rfl | ⟨j, rfl⟩
  · simp
  · simp [htarget]
  · simp [hotherS]
  · simp [ht j]

/--
Every path in the source type-2 catalogue to `T` stays in the core
carrier `{x} ∪ S ∪ T`.
-/
theorem semiAdmissiblePathsToT_support
    (C : TypeTwoCore G x ℓ) (target : V)
    (htarget : target ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.semiAdmissiblePathsToT target htarget q
      hqOne hqFour hqCore).path i).walk.support) :
    z ∈ insert x (C.S ∪ C.T) := by
  have hs (j : Fin 2) :
      (C.pointAtT target htarget).s j ∈ C.S := by
    simp only [pointAtT]
    exact finsetEmbeddingOfCardEq_mem C.S C.card_S j
  have hotherT (j : Fin (ℓ - 1)) :
      (C.pointAtT target htarget).otherT j ∈ C.T := by
    simp only [pointAtT]
    exact Finset.mem_of_mem_erase
      (finsetEmbeddingOfCardEq_mem
        (C.T.erase target) _ j)
  rcases PointedTypeTwoTCore.factTwoTypeTwoTBounded_support
      (C.pointAtT target htarget) hqOne hqFour hqCore i z hz with
    rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp
  · simp [htarget]
  · simp [hs j]
  · simp [hotherT j]

end TypeTwoCore

namespace TypeThreeCore

variable [DecidableEq V] {G : SimpleGraph V} {x : V} {ℓ : ℕ}

/--
Build a type-3 pointed `T`-certificate from any `ℓ` spare vertices of
`T` avoiding the target.
-/
noncomputable def pointAtTFromSpare
    (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (spare : Finset V) (hspare : spare ⊆ C.T)
    (htargetSpare : target ∉ spare)
    (hspareCard : ℓ ≤ spare.card) :
    PointedTypeThreeTCore G x target ℓ := by
  let s : Fin ℓ ↪ V :=
    finsetEmbeddingOfCardEq C.S C.card_S
  let otherT : Fin ℓ ↪ V :=
    finsetEmbeddingOfCardLE spare hspareCard
  have hs (i : Fin ℓ) : s i ∈ C.S :=
    finsetEmbeddingOfCardEq_mem C.S C.card_S i
  have hotherTSpare (i : Fin ℓ) :
      otherT i ∈ spare :=
    finsetEmbeddingOfCardLE_mem spare hspareCard i
  have hotherT (i : Fin ℓ) :
      otherT i ∈ C.T :=
    hspare (hotherTSpare i)
  have hotherTNeTarget (i : Fin ℓ) :
      otherT i ≠ target := by
    intro h
    apply htargetSpare
    simpa [h] using hotherTSpare i
  have hdisjoint :
      ∀ {s t : V}, s ∈ C.S → t ∈ C.T → s ≠ t := by
    intro s t hs ht hst
    subst t
    exact Finset.disjoint_left.1 C.disjoint hs ht
  exact {
    s := s
    otherT := otherT
    x_ne_target := by
      intro h
      subst target
      exact C.root_not_mem_T htarget
    x_ne_s := by
      intro i h
      apply C.root_not_mem_S
      simpa [h] using hs i
    x_ne_otherT := by
      intro i h
      apply C.root_not_mem_T
      simpa [h] using hotherT i
    s_ne_target := by
      intro i
      exact hdisjoint (hs i) htarget
    otherT_ne_target := hotherTNeTarget
    s_ne_otherT := by
      intro i j
      exact hdisjoint (hs i) (hotherT j)
    adj_x_target := C.root_adj_T target htarget
    adj_x_otherT := by
      intro i
      exact C.root_adj_T (otherT i) (hotherT i)
    adj_otherT_s := by
      intro i j
      exact C.cross_adj (otherT i) (hotherT i)
        (s j) (hs j)
    adj_s_target := by
      intro i
      exact (C.cross_adj target htarget (s i) (hs i)).symm
  }

/-- Point a source type-3 core at a selected vertex of `T`. -/
noncomputable def pointAtT
    (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T) :
    PointedTypeThreeTCore G x target ℓ := by
  let spare := C.T.erase target
  have hspareCard : ℓ ≤ spare.card := by
    dsimp [spare]
    rw [Finset.card_erase_of_mem htarget]
    have hlarge : ℓ + 1 ≤ C.T.card :=
      (Nat.le_max_left (ℓ + 1) 2).trans C.card_T_lower
    omega
  exact C.pointAtTFromSpare target htarget spare
    (Finset.erase_subset target C.T) (by simp [spare])
    hspareCard

/--
Point a source type-3 core at `target ∈ T` after deleting a distinct
vertex `deleted ∈ T`.  The source hypothesis `|T| ≥ ℓ+2` leaves at least
`ℓ` spare vertices.
-/
noncomputable def pointAtTAfterDeleting
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.T)
    (hdeleted : deleted ∈ C.T)
    (hne : target ≠ deleted)
    (hlarge : ℓ + 2 ≤ C.T.card) :
    PointedTypeThreeTCore G x target ℓ := by
  let spare := (C.T.erase target).erase deleted
  have hdeletedRemaining : deleted ∈ C.T.erase target := by
    simp [hdeleted, hne.symm]
  have hspareCard : ℓ ≤ spare.card := by
    dsimp [spare]
    rw [Finset.card_erase_of_mem hdeletedRemaining,
      Finset.card_erase_of_mem htarget]
    omega
  have hspareSubset : spare ⊆ C.T :=
    (Finset.erase_subset deleted (C.T.erase target)).trans
      (Finset.erase_subset target C.T)
  exact C.pointAtTFromSpare target htarget spare hspareSubset
    (by simp [spare]) hspareCard

/--
Point a source type-3 core at `target ∈ S` after deleting one specified
vertex of `T`.
-/
noncomputable def pointAtSAfterDeleting
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T) :
    PointedTypeThreeSCore G x target ℓ := by
  let remainingS := C.S.erase target
  let remainingT := C.T.erase deleted
  have hremainingSCard : remainingS.card = ℓ - 1 := by
    dsimp [remainingS]
    rw [Finset.card_erase_of_mem htarget, C.card_S]
  have hremainingTCard : ℓ ≤ remainingT.card := by
    dsimp [remainingT]
    rw [Finset.card_erase_of_mem hdeleted]
    have hlarge : ℓ + 1 ≤ C.T.card :=
      (Nat.le_max_left (ℓ + 1) 2).trans C.card_T_lower
    omega
  let otherS : Fin (ℓ - 1) ↪ V :=
    finsetEmbeddingOfCardEq remainingS hremainingSCard
  let t : Fin ℓ ↪ V :=
    finsetEmbeddingOfCardLE remainingT hremainingTCard
  have hotherSRemaining (i : Fin (ℓ - 1)) :
      otherS i ∈ remainingS :=
    finsetEmbeddingOfCardEq_mem remainingS hremainingSCard i
  have hotherS (i : Fin (ℓ - 1)) :
      otherS i ∈ C.S :=
    (Finset.mem_erase.1 (hotherSRemaining i)).2
  have hotherSNeTarget (i : Fin (ℓ - 1)) :
      otherS i ≠ target :=
    (Finset.mem_erase.1 (hotherSRemaining i)).1
  have htRemaining (i : Fin ℓ) :
      t i ∈ remainingT :=
    finsetEmbeddingOfCardLE_mem remainingT hremainingTCard i
  have ht (i : Fin ℓ) :
      t i ∈ C.T :=
    (Finset.mem_erase.1 (htRemaining i)).2
  have hdisjoint :
      ∀ {s t : V}, s ∈ C.S → t ∈ C.T → s ≠ t := by
    intro s t hs ht hst
    subst t
    exact Finset.disjoint_left.1 C.disjoint hs ht
  exact {
    otherS := otherS
    t := t
    x_ne_target := by
      intro h
      subst target
      exact C.root_not_mem_S htarget
    x_ne_otherS := by
      intro i h
      apply C.root_not_mem_S
      simpa [h] using hotherS i
    x_ne_t := by
      intro i h
      apply C.root_not_mem_T
      simpa [h] using ht i
    target_ne_otherS := by
      intro i
      exact (hotherSNeTarget i).symm
    target_ne_t := by
      intro i
      exact hdisjoint htarget (ht i)
    otherS_ne_t := by
      intro i j
      exact hdisjoint (hotherS i) (ht j)
    adj_x_t := by
      intro i
      exact C.root_adj_T (t i) (ht i)
    adj_t_target := by
      intro i
      exact C.cross_adj (t i) (ht i) target htarget
    adj_t_otherS := by
      intro i j
      exact C.cross_adj (t i) (ht i)
        (otherS j) (hotherS j)
  }

/--
The bounded type-3 catalogue to a selected `S`-vertex, surviving deletion
of any specified `T`-vertex.
-/
noncomputable def admissiblePathsToSAfterDeleting
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ) :
    AdmissiblePathFamily G x target q :=
  (C.pointAtSAfterDeleting target deleted htarget hdeleted
    ).factTwoTypeThreeBounded hqOne hqFour hqCore

/-- The bounded type-3 catalogue to a selected `T`-vertex. -/
noncomputable def semiAdmissiblePathsToT
    (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target q :=
  (C.pointAtT target htarget).factTwoTypeThreeTBounded
    hqOne hqFour hqCore

/--
The bounded type-3 catalogue to `target ∈ T` after deletion of a
distinct `T`-vertex.
-/
noncomputable def semiAdmissiblePathsToTAfterDeleting
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.T)
    (hdeleted : deleted ∈ C.T)
    (hne : target ≠ deleted)
    (hlarge : ℓ + 2 ≤ C.T.card)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target q :=
  (C.pointAtTAfterDeleting target deleted htarget hdeleted hne hlarge
    ).factTwoTypeThreeTBounded hqOne hqFour hqCore

/--
Every path in the source type-3 catalogue to `S` after deleting `deleted`
stays in the exact surviving carrier `{x} ∪ S ∪ (T \ {deleted})`.
-/
theorem admissiblePathsToSAfterDeleting_support
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.admissiblePathsToSAfterDeleting
      target deleted htarget hdeleted q hqOne hqFour
      hqCore).path i).walk.support) :
    z ∈ insert x (C.S ∪ C.T.erase deleted) := by
  have hotherS (j : Fin (ℓ - 1)) :
      (C.pointAtSAfterDeleting target deleted htarget
        hdeleted).otherS j ∈ C.S := by
    simp only [pointAtSAfterDeleting]
    exact Finset.mem_of_mem_erase
      (finsetEmbeddingOfCardEq_mem
        (C.S.erase target) _ j)
  have ht (j : Fin ℓ) :
      (C.pointAtSAfterDeleting target deleted htarget
        hdeleted).t j ∈ C.T.erase deleted := by
    simp only [pointAtSAfterDeleting]
    exact finsetEmbeddingOfCardLE_mem
      (C.T.erase deleted) _ j
  rcases PointedTypeThreeSCore.factTwoTypeThreeBounded_support
      (C.pointAtSAfterDeleting target deleted htarget hdeleted)
      hqOne hqFour hqCore i z hz with
    rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp
  · simp [htarget]
  · simp [hotherS j]
  · simp [ht j]

/--
The source type-3 catalogue to `S` really lives in `H - deleted`: no
selected path uses the deleted vertex.
-/
theorem admissiblePathsToSAfterDeleting_avoids_deleted
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ)
    (i : Fin q) :
    deleted ∉ ((C.admissiblePathsToSAfterDeleting
      target deleted htarget hdeleted q hqOne hqFour
      hqCore).path i).walk.support := by
  intro hz
  have hmem := C.admissiblePathsToSAfterDeleting_support
    target deleted htarget hdeleted q hqOne hqFour
    hqCore i deleted hz
  have hnotS : deleted ∉ C.S := by
    intro hS
    exact Finset.disjoint_left.1 C.disjoint hS hdeleted
  have hdeletedNeRoot : deleted ≠ x := by
    intro h
    subst deleted
    exact C.root_not_mem_T hdeleted
  simp [hdeletedNeRoot, hnotS] at hmem

/--
Every path in the source type-3 catalogue to `T` stays in the core
carrier `{x} ∪ S ∪ T`.
-/
theorem semiAdmissiblePathsToT_support
    (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.semiAdmissiblePathsToT target htarget q
      hqOne hqFour hqCore).path i).walk.support) :
    z ∈ insert x (C.S ∪ C.T) := by
  have hs (j : Fin ℓ) :
      (C.pointAtT target htarget).s j ∈ C.S := by
    simp only [pointAtT, pointAtTFromSpare]
    exact finsetEmbeddingOfCardEq_mem C.S C.card_S j
  have hotherT (j : Fin ℓ) :
      (C.pointAtT target htarget).otherT j ∈ C.T := by
    simp only [pointAtT, pointAtTFromSpare]
    exact Finset.mem_of_mem_erase
      (finsetEmbeddingOfCardLE_mem
        (C.T.erase target) _ j)
  rcases PointedTypeThreeTCore.factTwoTypeThreeTBounded_support
      (C.pointAtT target htarget)
      hqOne hqFour hqCore i z hz with
    rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp
  · simp [htarget]
  · simp [hs j]
  · simp [hotherT j]

/--
Every path in the source type-3 catalogue to `T` after deleting
`deleted` stays in the exact surviving carrier
`{x} ∪ S ∪ (T \ {deleted})`.
-/
theorem semiAdmissiblePathsToTAfterDeleting_support
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.T)
    (hdeleted : deleted ∈ C.T)
    (hne : target ≠ deleted)
    (hlarge : ℓ + 2 ≤ C.T.card)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.semiAdmissiblePathsToTAfterDeleting
      target deleted htarget hdeleted hne hlarge q
      hqOne hqFour hqCore).path i).walk.support) :
    z ∈ insert x (C.S ∪ C.T.erase deleted) := by
  have hs (j : Fin ℓ) :
      (C.pointAtTAfterDeleting target deleted htarget
        hdeleted hne hlarge).s j ∈ C.S := by
    simp only [pointAtTAfterDeleting, pointAtTFromSpare]
    exact finsetEmbeddingOfCardEq_mem C.S C.card_S j
  have hotherT (j : Fin ℓ) :
      (C.pointAtTAfterDeleting target deleted htarget
        hdeleted hne hlarge).otherT j ∈
          C.T.erase deleted := by
    simp only [pointAtTAfterDeleting, pointAtTFromSpare]
    have hdeletedRemaining :
        deleted ∈ C.T.erase target := by
      simp [hdeleted, hne.symm]
    have hcard :
        ℓ ≤ ((C.T.erase target).erase deleted).card := by
      rw [Finset.card_erase_of_mem hdeletedRemaining,
        Finset.card_erase_of_mem htarget]
      omega
    have hj := finsetEmbeddingOfCardLE_mem
      ((C.T.erase target).erase deleted) hcard j
    rw [Finset.mem_erase]
    exact ⟨(Finset.mem_erase.1 hj).1,
      (Finset.mem_erase.1
        (Finset.mem_erase.1 hj).2).2⟩
  rcases PointedTypeThreeTCore.factTwoTypeThreeTBounded_support
      (C.pointAtTAfterDeleting target deleted htarget
        hdeleted hne hlarge)
      hqOne hqFour hqCore i z hz with
    rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp
  · simp [htarget, hne]
  · simp [hs j]
  · simp [hotherT j]

/--
The source type-3 catalogue to `T` really lives in `H - deleted`: no
selected path uses the deleted vertex.
-/
theorem semiAdmissiblePathsToTAfterDeleting_avoids_deleted
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.T)
    (hdeleted : deleted ∈ C.T)
    (hne : target ≠ deleted)
    (hlarge : ℓ + 2 ≤ C.T.card)
    (q : ℕ) (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) :
    deleted ∉ ((C.semiAdmissiblePathsToTAfterDeleting
      target deleted htarget hdeleted hne hlarge q
      hqOne hqFour hqCore).path i).walk.support := by
  intro hz
  have hmem := C.semiAdmissiblePathsToTAfterDeleting_support
    target deleted htarget hdeleted hne hlarge q
    hqOne hqFour hqCore i deleted hz
  have hnotS : deleted ∉ C.S := by
    intro hS
    exact Finset.disjoint_left.1 C.disjoint hS hdeleted
  have hdeletedNeRoot : deleted ≠ x := by
    intro h
    subst deleted
    exact C.root_not_mem_T hdeleted
  simp [hdeletedNeRoot, hnotS] at hmem

end TypeThreeCore

end COY

end DeanK5
