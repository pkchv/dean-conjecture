import DeanK5.COYCoreSelection
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The COY root orientation

After choosing an optimal core at each root, the proof of COY Theorem 3
orients the ordered root pair by the source conditions (XY1)--(XY3):

1. minimize the core type over both roots;
2. subject to a type tie, minimize the degree of the chosen root;
3. subject to both ties, minimize its distance to the exceptional vertex.

The orientation data below carries both optimal cores explicitly.  This
avoids relying on the behavior of `Classical.choice` after swapping the
roots twice.  No distinctness assumption involving the exceptional vertex
is made; in particular, it may coincide with either root.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/--
The first ordered root orientation is preferred to the reverse orientation
according to the source choices (XY1)--(XY3).
-/
def PreferredOrientation
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y z : V}
    (chosen : OptimalRootedCore G x y)
    (reverse : OptimalRootedCore G y x) : Prop :=
  chosen.rooted.core.typeNumber ≤ reverse.rooted.core.typeNumber ∧
    (chosen.rooted.core.typeNumber = reverse.rooted.core.typeNumber →
      finiteDegree G x ≤ finiteDegree G y) ∧
    (chosen.rooted.core.typeNumber = reverse.rooted.core.typeNumber →
      finiteDegree G x = finiteDegree G y →
        G.dist x z ≤ G.dist y z)

namespace PreferredOrientation

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {chosen : OptimalRootedCore G x y}
  {reverse : OptimalRootedCore G y x}

/-- Condition (XY1): the chosen type is no larger than the reverse type. -/
theorem type_le
    (h : PreferredOrientation (z := z) chosen reverse) :
    chosen.rooted.core.typeNumber ≤ reverse.rooted.core.typeNumber :=
  h.1

/-- Condition (XY2), once the two optimal types coincide. -/
theorem degree_le_of_type_eq
    (h : PreferredOrientation (z := z) chosen reverse)
    (htype :
      chosen.rooted.core.typeNumber = reverse.rooted.core.typeNumber) :
    finiteDegree G x ≤ finiteDegree G y :=
  h.2.1 htype

/-- Condition (XY3), once both the optimal types and root degrees coincide. -/
theorem dist_le_of_type_eq_of_degree_eq
    (h : PreferredOrientation (z := z) chosen reverse)
    (htype :
      chosen.rooted.core.typeNumber = reverse.rooted.core.typeNumber)
    (hdegree : finiteDegree G x = finiteDegree G y) :
    G.dist x z ≤ G.dist y z :=
  h.2.2 htype hdegree

end PreferredOrientation

/--
For any two optimal rooted cores, one of the two ordered orientations
satisfies (XY1)--(XY3).  Equality in all three statistics is resolved in
favor of both orientations.
-/
theorem preferredOrientation_or_reverse
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y z : V}
    (left : OptimalRootedCore G x y)
    (right : OptimalRootedCore G y x) :
    PreferredOrientation (z := z) left right ∨
      PreferredOrientation (z := z) right left := by
  unfold PreferredOrientation
  omega

/--
An explicitly oriented pair of optimal cores.  Keeping the reverse core in
the package lets later arguments compare against both roots without making
another proof-dependent choice.
-/
structure PreferredOrientationData
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y z : V) where
  /-- The optimal core at the chosen root. -/
  chosen : OptimalRootedCore G x y
  /-- The optimal core at the other root. -/
  reverse : OptimalRootedCore G y x
  /-- The three source orientation conditions. -/
  preferred : PreferredOrientation (z := z) chosen reverse

namespace PreferredOrientationData

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}

/-- The selected core is type-minimal among cores at the chosen root. -/
theorem type_le_core_at_chosen_root
    (D : PreferredOrientationData G x y z)
    {m : ℕ} (R : RootedCore G x y m) :
    D.chosen.rooted.core.typeNumber ≤ R.core.typeNumber :=
  D.chosen.type_minimal R

/-- The selected core is type-minimal among cores at the other root as well. -/
theorem type_le_core_at_other_root
    (D : PreferredOrientationData G x y z)
    {m : ℕ} (R : RootedCore G y x m) :
    D.chosen.rooted.core.typeNumber ≤ R.core.typeNumber :=
  D.preferred.type_le.trans (D.reverse.type_minimal R)

/--
The full (XY1) conclusion: the selected type is no larger than the type of
any rooted core based at either root.
-/
theorem type_le_every_rootedCore
    (D : PreferredOrientationData G x y z) :
    (∀ {m : ℕ} (R : RootedCore G x y m),
      D.chosen.rooted.core.typeNumber ≤ R.core.typeNumber) ∧
    (∀ {m : ℕ} (R : RootedCore G y x m),
      D.chosen.rooted.core.typeNumber ≤ R.core.typeNumber) :=
  ⟨D.type_le_core_at_chosen_root, D.type_le_core_at_other_root⟩

/-- The reverse orientation has a rooted core of the selected minimum type. -/
def OtherRootAttainsChosenType
    (D : PreferredOrientationData G x y z) : Prop :=
  ∃ (m : ℕ) (R : RootedCore G y x m),
    R.core.typeNumber = D.chosen.rooted.core.typeNumber

/--
If the other root can attain the selected type, then its own optimal core
has exactly that type.
-/
theorem reverse_type_eq_of_otherRootAttainsChosenType
    (D : PreferredOrientationData G x y z)
    (hattains : D.OtherRootAttainsChosenType) :
    D.reverse.rooted.core.typeNumber =
      D.chosen.rooted.core.typeNumber := by
  obtain ⟨m, R, hR⟩ := hattains
  apply Nat.le_antisymm
  · simpa [hR] using D.reverse.type_minimal R
  · exact D.preferred.type_le

/--
Condition (XY2): if the reverse orientation can attain the same globally
minimum type, the chosen root has no larger degree.
-/
theorem chosen_degree_le_other_of_otherRootAttainsChosenType
    (D : PreferredOrientationData G x y z)
    (hattains : D.OtherRootAttainsChosenType) :
    finiteDegree G x ≤ finiteDegree G y :=
  D.preferred.degree_le_of_type_eq
    (D.reverse_type_eq_of_otherRootAttainsChosenType hattains).symm

/--
Condition (XY3): if the reverse orientation can attain the same minimum
type and the two root degrees tie, the chosen root is no farther from the
exceptional vertex.
-/
theorem chosen_dist_le_other_of_otherRootAttainsChosenType_of_degree_eq
    (D : PreferredOrientationData G x y z)
    (hattains : D.OtherRootAttainsChosenType)
    (hdegree : finiteDegree G x = finiteDegree G y) :
    G.dist x z ≤ G.dist y z :=
  D.preferred.dist_le_of_type_eq_of_degree_eq
    (D.reverse_type_eq_of_otherRootAttainsChosenType hattains).symm
    hdegree

end PreferredOrientationData

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
Choose an orientation satisfying (XY1)--(XY3).  In the reverse branch the
two already selected cores are exchanged explicitly, so this theorem does
not require the optimal core chosen after swapping twice to be definitionally
equal to the original choice.
-/
theorem preferredOrientationData_or_swap
    (M : MinimalCounterexample q G x y z) :
    Nonempty (PreferredOrientationData G x y z) ∨
      Nonempty (PreferredOrientationData G y x z) := by
  let left := M.optimalRootedCore
  let right := M.swapRoots.optimalRootedCore
  rcases preferredOrientation_or_reverse (z := z) left right with
    hleft | hright
  · exact Or.inl ⟨{
        chosen := left
        reverse := right
        preferred := hleft
      }⟩
  · exact Or.inr ⟨{
        chosen := right
        reverse := left
        preferred := hright
      }⟩

end MinimalCounterexample

end COY

end DeanK5
