import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Length arithmetic (paper Section 2)

This file contains the modular parts of paper Lemmas 2.1 and 2.3.  They
are deliberately independent of graph theory, so the final residue argument
can be audited without any graph-theoretic assumptions.
-/

namespace DeanK5

/-- The common differences allowed in an admissible family. -/
def IsAdmissibleStep (d : ℕ) : Prop := d = 1 ∨ d = 2

/--
Five terms of an arithmetic progression with common difference one or two
hit zero modulo five.
-/
theorem five_term_progression_hits_zero
    (a d : ℕ) (hd : IsAdmissibleStep d) :
    ∃ i : Fin 5, (a + i.val * d : ℕ) % 5 = 0 := by
  rcases hd with rfl | rfl
  · let i5 : ZMod 5 := -(a : ZMod 5)
    let i : Fin 5 := ⟨i5.val, i5.val_lt⟩
    refine ⟨i, ?_⟩
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [show (i.val : ZMod 5) = i5 by exact ZMod.natCast_zmod_val i5]
    simp [i5]
  · let i5 : ZMod 5 := -3 * (a : ZMod 5)
    let i : Fin 5 := ⟨i5.val, i5.val_lt⟩
    refine ⟨i, ?_⟩
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [show (i.val : ZMod 5) = i5 by exact ZMod.natCast_zmod_val i5]
    change (a : ZMod 5) + i5 * 2 = 0
    dsimp [i5]
    ring_nf
    rw [show (5 : ZMod 5) = 0 by decide]
    simp

/--
Paper Lemma 2.3, in its exact modular form.

If `R` has three distinct residues modulo five and `d` is one or two, one
of the nine sums `a + i*d + r`, with `i = 0,1,2` and `r ∈ R`, is zero.
-/
theorem three_add_three_mod_five
    (a d : ℕ) (hd : IsAdmissibleStep d)
    (R : Finset (ZMod 5)) (hR : R.card = 3) :
    ∃ (i : Fin 3) (r : ZMod 5), r ∈ R ∧
      (a : ZMod 5) + (i.val : ZMod 5) * (d : ZMod 5) + r = 0 := by
  let A : ZMod 5 := a
  let D : ZMod 5 := d
  let T : Finset (ZMod 5) := {-A, -(A + D), -(A + 2 * D)}
  have hD : D = 1 ∨ D = 2 := by
    rcases hd with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h01 : -A ≠ -(A + D) := by
    intro h
    have h' : D = 0 := by linear_combination h
    rcases hD with hD | hD
    · rw [hD] at h'
      exact (by decide : (1 : ZMod 5) ≠ 0) h'
    · rw [hD] at h'
      exact (by decide : (2 : ZMod 5) ≠ 0) h'
  have h02 : -A ≠ -(A + 2 * D) := by
    intro h
    have h' : 2 * D = 0 := by linear_combination h
    rcases hD with hD | hD
    · rw [hD] at h'
      exact (by decide : (2 : ZMod 5) ≠ 0) h'
    · rw [hD] at h'
      exact (by decide : (4 : ZMod 5) ≠ 0) h'
  have h12 : -(A + D) ≠ -(A + 2 * D) := by
    intro h
    have h' : D = 0 := by linear_combination h
    rcases hD with hD | hD
    · rw [hD] at h'
      exact (by decide : (1 : ZMod 5) ≠ 0) h'
    · rw [hD] at h'
      exact (by decide : (2 : ZMod 5) ≠ 0) h'
  have hT : T.card = 3 := by
    change ({-A, -(A + D), -(A + 2 * D)} : Finset (ZMod 5)).card = 3
    rw [Finset.card_insert_of_notMem]
    · simpa using Finset.card_pair_eq_two_iff.mpr h12
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, h02⟩
  have hcard : (Finset.univ : Finset (ZMod 5)).card <
      R.card + T.card := by
    simp [hR, hT]
  obtain ⟨r, hr⟩ :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (s := Finset.univ) (t := R) (u := T)
      (Finset.subset_univ R) (Finset.subset_univ T) hcard
  have hrR : r ∈ R := (Finset.mem_inter.mp hr).1
  have hrT : r ∈ T := (Finset.mem_inter.mp hr).2
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hrT
  rcases hrT with rfl | rfl | rfl
  · exact ⟨⟨0, by omega⟩, -A, hrR, by simp [A]⟩
  · exact ⟨⟨1, by omega⟩, -(A + D), hrR, by simp [A, D]⟩
  · exact ⟨⟨2, by omega⟩, -(A + 2 * D), hrR, by
      simp [A, D]⟩

end DeanK5
