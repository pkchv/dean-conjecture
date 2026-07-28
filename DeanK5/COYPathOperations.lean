import DeanK5.Graph.Basic

/-!
# Fixed-connector operations for rooted path families

COY's induction repeatedly embeds an admissible family from a smaller
rooted graph and attaches the same connector to every member.  These
operations retain the exact support-disjointness needed for the result to
remain a family of simple paths.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace AdmissiblePathFamily

/-- Retain the first `r` paths of an admissible family. -/
def take
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : AdmissiblePathFamily G x y q)
    (r : ℕ) (hr : r ≤ q) :
    AdmissiblePathFamily G x y r where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := F.start_ge_two
  path i := F.path (Fin.castLE hr i)
  length_path i := by
    simpa using F.length_path (Fin.castLE hr i)

/--
Append one fixed path to every member of an admissible family.
-/
def appendFixed
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (F : AdmissiblePathFamily G x y q)
    (Q : SimplePath G y z)
    (hdisjoint : ∀ i,
      (F.path i).walk.support.Disjoint Q.walk.support.tail) :
    AdmissiblePathFamily G x z q where
  start := F.start + Q.length
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := F.start_ge_two.trans
    (Nat.le_add_right F.start Q.length)
  path i := (F.path i).appendDisjoint Q (hdisjoint i)
  length_path i := by
    rw [SimplePath.appendDisjoint_length, F.length_path]
    omega

@[simp] theorem appendFixed_path
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (F : AdmissiblePathFamily G x y q)
    (Q : SimplePath G y z)
    (hdisjoint) (i : Fin q) :
    (F.appendFixed Q hdisjoint).path i =
      (F.path i).appendDisjoint Q (hdisjoint i) :=
  rfl

/--
Prepend one fixed path to every member of an admissible family.
-/
def prependFixed
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (P : SimplePath G x y)
    (F : AdmissiblePathFamily G y z q)
    (hdisjoint : ∀ i,
      P.walk.support.Disjoint (F.path i).walk.support.tail) :
    AdmissiblePathFamily G x z q where
  start := P.length + F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := F.start_ge_two.trans
    (Nat.le_add_left F.start P.length)
  path i := P.appendDisjoint (F.path i) (hdisjoint i)
  length_path i := by
    rw [SimplePath.appendDisjoint_length, F.length_path]
    omega

@[simp] theorem prependFixed_path
    {G : SimpleGraph V} {x y z : V} {q : ℕ}
    (P : SimplePath G x y)
    (F : AdmissiblePathFamily G y z q)
    (hdisjoint) (i : Fin q) :
    (F.prependFixed P hdisjoint).path i =
      P.appendDisjoint (F.path i) (hdisjoint i) :=
  rfl

end AdmissiblePathFamily

end DeanK5
