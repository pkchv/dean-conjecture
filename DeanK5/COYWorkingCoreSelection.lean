import DeanK5.COYModifiedExterior
import DeanK5.COYCoreOrientation

/-!
# Selecting the COY working core

The optimal core is retained unless condition (T) holds.  When it does,
the selected working core is the corresponding (M1) or (M2) modification.
The resulting sum type keeps that source case split explicit.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- The optimal core itself, or the mandatory special type-3 modification. -/
inductive SelectedWorkingCore
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y z : V}
    (O : OptimalRootedCore G x y) where
  /-- Condition (T) fails, so the optimal core is used unchanged. -/
  | natural
      (no_trigger :
        ¬Nonempty (TypeThreeModificationTrigger (z := z) O))
  /-- Condition (T) holds and the appropriate source modification is used. -/
  | modified
      (trigger : TypeThreeModificationTrigger (z := z) O)
      (choice : TypeThreeModificationChoice trigger)

namespace SelectedWorkingCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}

/-- Every optimal core determines a source working core. -/
theorem exists_selection :
    Nonempty (SelectedWorkingCore (z := z) O) := by
  classical
  by_cases htrigger :
      Nonempty (TypeThreeModificationTrigger (z := z) O)
  · obtain ⟨T⟩ := htrigger
    obtain ⟨K⟩ :=
      TypeThreeModificationChoice.exists_choice (T := T)
    exact ⟨.modified T K⟩
  · exact ⟨.natural htrigger⟩

/-- The rank of the selected working core. -/
def rank (W : SelectedWorkingCore (z := z) O) : ℕ :=
  match W with
  | .natural _ => O.rank
  | .modified _ K => K.rank

/-- The selected working core with the original ordered roots. -/
def rooted (W : SelectedWorkingCore (z := z) O) :
    RootedCore G x y W.rank :=
  match W with
  | .natural _ => O.rooted
  | .modified _ K => K.rooted

/-- In the natural branch the selected rooted core is the optimal core. -/
theorem rooted_eq_optimal_of_natural
    (hnot :
      ¬Nonempty (TypeThreeModificationTrigger (z := z) O)) :
    (SelectedWorkingCore.natural hnot).rooted = O.rooted :=
  rfl

/-- In the modified branch the selected core has source type 3. -/
theorem rooted_core_eq_typeThree_of_modified
    (T : TypeThreeModificationTrigger (z := z) O)
    (K : TypeThreeModificationChoice T) :
    (SelectedWorkingCore.modified T K).rooted.core =
      .typeThree K.core :=
  rfl

/--
Selecting one of the two source type-3 modifications can change the rank
and the two parts, but it never changes the numerical core type.
-/
theorem typeNumber_eq_optimal
    (W : SelectedWorkingCore (z := z) O) :
    W.rooted.core.typeNumber =
      O.rooted.core.typeNumber := by
  cases W with
  | natural hnot =>
      rfl
  | modified T K =>
      rw [T.core_eq]
      rfl

/-- Claim 3.4 is available in every modified branch. -/
theorem two_le_otherRegion_sdiff_protected_of_modified
    (T : TypeThreeModificationTrigger (z := z) O)
    (K : TypeThreeModificationChoice T)
    (hxz : ¬G.Adj x z) :
    2 ≤
      ((SelectedWorkingCore.modified T K).rooted.otherRegion \
        {y, z}).card :=
  K.two_le_otherRegion_sdiff_protected hxz

end SelectedWorkingCore

/-- An oriented optimal-core pair together with its selected working core. -/
structure PreferredWorkingCoreData
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y z : V) where
  /-- The source orientation satisfying (XY1)--(XY3). -/
  orientation : PreferredOrientationData G x y z
  /-- The natural or specially modified working core. -/
  working :
    SelectedWorkingCore (z := z) orientation.chosen

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
A minimal counterexample admits the full post-Claim-3.2 source setup in one
of the two root orientations.
-/
theorem preferredWorkingCoreData_or_swap
    (M : MinimalCounterexample q G x y z) :
    Nonempty (PreferredWorkingCoreData G x y z) ∨
      Nonempty (PreferredWorkingCoreData G y x z) := by
  rcases M.preferredOrientationData_or_swap with
    hforward | hreverse
  · obtain ⟨D⟩ := hforward
    obtain ⟨W⟩ :=
      SelectedWorkingCore.exists_selection
        (z := z) (O := D.chosen)
    exact Or.inl ⟨D, W⟩
  · obtain ⟨D⟩ := hreverse
    obtain ⟨W⟩ :=
      SelectedWorkingCore.exists_selection
        (z := z) (O := D.chosen)
    exact Or.inr ⟨D, W⟩

end MinimalCounterexample

end COY

end DeanK5
