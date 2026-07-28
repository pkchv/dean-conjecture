import DeanK5.COYMinimalCore

/-!
# Lexicographically optimal COY cores

The proof of COY Theorem 3 first minimizes the source type of a rooted core.
Within that type it maximizes `|S|`, and subject to that maximizes `|T|`.
For types 1 and 2 the size of `S` is fixed, so this single lexicographic
package expresses all three source cases uniformly.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- A rooted core satisfying the source choices (H1) and (H2). -/
structure OptimalRootedCore
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) where
  /-- The rank of the selected core. -/
  rank : ℕ
  /-- The selected rooted core. -/
  rooted : RootedCore G x y rank
  /-- No rooted core for `(x,y)` has smaller source type. -/
  type_minimal :
    ∀ {m : ℕ} (R : RootedCore G x y m),
      rooted.core.typeNumber ≤ R.core.typeNumber
  /-- Within the selected type, `|S|` is maximal. -/
  S_maximal :
    ∀ {m : ℕ} (R : RootedCore G x y m),
      R.core.typeNumber = rooted.core.typeNumber →
        R.core.S.card ≤ rooted.core.S.card
  /-- Subject to the selected type and `|S|`, `|T|` is maximal. -/
  T_maximal :
    ∀ {m : ℕ} (R : RootedCore G x y m),
      R.core.typeNumber = rooted.core.typeNumber →
      R.core.S.card = rooted.core.S.card →
        R.core.T.card ≤ rooted.core.T.card

/--
Every nonempty collection of rooted cores has a lexicographically optimal
member.  The optimization is over three bounded natural-valued statistics,
so no finite enumeration of proof-carrying core structures is needed.
-/
theorem exists_optimalRootedCore
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y : V}
    (hexists : ∃ ℓ : ℕ, Nonempty (RootedCore G x y ℓ)) :
    Nonempty (OptimalRootedCore G x y) := by
  classical
  obtain ⟨ℓ₀, ⟨R₀⟩⟩ := hexists
  let Ptype : ℕ → Prop := fun n =>
    ∃ (ℓ : ℕ) (R : RootedCore G x y ℓ),
      R.core.typeNumber = n
  have hPtype : ∃ n, Ptype n :=
    ⟨R₀.core.typeNumber, ℓ₀, R₀, rfl⟩
  let n := Nat.find hPtype
  have hnSpec : Ptype n :=
    Nat.find_spec hPtype
  obtain ⟨ℓ₁, R₁, hR₁Type⟩ := hnSpec
  let PS : ℕ → Prop := fun s =>
    ∃ (ℓ : ℕ) (R : RootedCore G x y ℓ),
      R.core.typeNumber = n ∧ R.core.S.card = s
  have hR₁SBound :
      R₁.core.S.card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hPSWitness : PS R₁.core.S.card :=
    ⟨ℓ₁, R₁, hR₁Type, rfl⟩
  let s := Nat.findGreatest PS (Fintype.card V)
  have hsSpec : PS s :=
    Nat.findGreatest_spec hR₁SBound hPSWitness
  obtain ⟨ℓ₂, R₂, hR₂Type, hR₂S⟩ := hsSpec
  let PT : ℕ → Prop := fun t =>
    ∃ (ℓ : ℕ) (R : RootedCore G x y ℓ),
      R.core.typeNumber = n ∧
      R.core.S.card = s ∧
      R.core.T.card = t
  have hR₂TBound :
      R₂.core.T.card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hPTWitness : PT R₂.core.T.card :=
    ⟨ℓ₂, R₂, hR₂Type, hR₂S, rfl⟩
  let t := Nat.findGreatest PT (Fintype.card V)
  have htSpec : PT t :=
    Nat.findGreatest_spec hR₂TBound hPTWitness
  obtain ⟨ℓ, R, hRType, hRS, hRT⟩ := htSpec
  refine ⟨{
    rank := ℓ
    rooted := R
    type_minimal := ?_
    S_maximal := ?_
    T_maximal := ?_
  }⟩
  · intro m R'
    rw [hRType]
    exact Nat.find_min' hPtype
      ⟨m, R', rfl⟩
  · intro m R' hsameType
    rw [hRS]
    apply Nat.le_findGreatest
    · rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    · refine ⟨m, R', ?_, rfl⟩
      exact hsameType.trans hRType
  · intro m R' hsameType hsameS
    rw [hRT]
    apply Nat.le_findGreatest
    · rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    · refine ⟨m, R', hsameType.trans hRType, ?_, rfl⟩
      exact hsameS.trans hRS

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- A lexicographically optimal core exists at the left root. -/
theorem exists_optimalRootedCore
    (M : MinimalCounterexample q G x y z) :
    Nonempty (OptimalRootedCore G x y) :=
  COY.exists_optimalRootedCore M.exists_left_rootedCore

/-- A fixed optimal left-root core for the subsequent source case split. -/
noncomputable def optimalRootedCore
    (M : MinimalCounterexample q G x y z) :
    OptimalRootedCore G x y :=
  Classical.choice M.exists_optimalRootedCore

/-- Fact 3 for the fixed optimal core. -/
theorem optimalRootedCore_factThree
    (M : MinimalCounterexample q G x y z) :
    M.optimalRootedCore.rank < q ∧
      (M.optimalRootedCore.rooted.core.HasTAttachment
          M.optimalRootedCore.rooted.otherRegion →
        M.optimalRootedCore.rank + 1 < q) :=
  M.rootedCore_factThree M.optimalRootedCore.rooted

end MinimalCounterexample

end COY

end DeanK5
