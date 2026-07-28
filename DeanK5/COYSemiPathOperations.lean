import DeanK5.COYConcatenation

/-!
# Fixed connectors for semi-admissible path families

Appending or prepending one nontrivial fixed connector to a
semi-admissible family raises its first path length from at least one to at
least two.  The result is therefore an admissible family.  These are the
path-level operations used in the prefix construction of COY Claim 3.16.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY.SemiAdmissiblePathFamily

/--
Append a fixed nontrivial path to every member of a semi-admissible family.
-/
def appendFixedToAdmissible
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (F : SemiAdmissiblePathFamily G x y q)
    (Q : SimplePath G y z)
    (hQ : 1 ≤ Q.length)
    (hdisjoint : ∀ i,
      (F.path i).walk.support.Disjoint
        Q.walk.support.tail) :
    AdmissiblePathFamily G x z q where
  start := F.start + Q.length
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := by
    have hF := F.start_ge_one
    omega
  path i :=
    (F.path i).appendDisjoint Q (hdisjoint i)
  length_path i := by
    rw [SimplePath.appendDisjoint_length,
      F.length_path]
    omega

@[simp] theorem appendFixedToAdmissible_path
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (F : SemiAdmissiblePathFamily G x y q)
    (Q : SimplePath G y z)
    (hQ : 1 ≤ Q.length)
    (hdisjoint)
    (i : Fin q) :
    (F.appendFixedToAdmissible Q hQ hdisjoint).path i =
      (F.path i).appendDisjoint Q (hdisjoint i) :=
  rfl

/--
Prepend a fixed nontrivial path to every member of a semi-admissible
family.
-/
def prependFixedToAdmissible
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (P : SimplePath G x y)
    (hP : 1 ≤ P.length)
    (F : SemiAdmissiblePathFamily G y z q)
    (hdisjoint : ∀ i,
      P.walk.support.Disjoint
        (F.path i).walk.support.tail) :
    AdmissiblePathFamily G x z q where
  start := P.length + F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := by
    have hF := F.start_ge_one
    omega
  path i :=
    P.appendDisjoint (F.path i) (hdisjoint i)
  length_path i := by
    rw [SimplePath.appendDisjoint_length,
      F.length_path]
    omega

@[simp] theorem prependFixedToAdmissible_path
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (P : SimplePath G x y)
    (hP : 1 ≤ P.length)
    (F : SemiAdmissiblePathFamily G y z q)
    (hdisjoint)
    (i : Fin q) :
    (F.prependFixedToAdmissible P hP hdisjoint).path i =
      P.appendDisjoint (F.path i) (hdisjoint i) :=
  rfl

end COY.SemiAdmissiblePathFamily

end DeanK5
