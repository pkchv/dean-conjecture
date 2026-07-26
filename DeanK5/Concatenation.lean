import DeanK5.Graph.Basic

/-!
# Simple-cycle assembly (paper Section 2)

This is the repeatedly used `3+3` consequence of paper Lemmas 2.1
and 2.2.  The grid stores actual simple-cycle witnesses.  The arithmetic
selection below then extracts five cycles in an admissible progression.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
Three simple paths with consecutive lengths.  Unlike
`AdmissiblePathFamily`, the first length may be one; this is the core-side
family used in Lemma 5.1.
-/
structure ConsecutivePathTriple
    (G : SimpleGraph V) (x y : V) where
  /-- The length of the first path in the triple. -/
  start : ℕ
  /-- The three simple paths in increasing length order. -/
  path : Fin 3 → SimplePath G x y
  length_path : ∀ i, (path i).length = start + i.val

/-- A certified grid of simple cycles obtained by closing two path families. -/
structure ConcatenationGrid
    (G : SimpleGraph V) {x y : V}
    (left : AdmissiblePathFamily G x y 3)
    (right : AdmissiblePathFamily G y x 3) where
  /-- The simple cycle obtained from each pair of paths. -/
  cycle : Fin 3 → Fin 3 → SimpleCycle G
  length_cycle : ∀ i j,
    (cycle i j).length =
      (left.path i).length + (right.path j).length

/--
A closure grid with a fixed additional connector length.  Section 7 uses
this form because a cycle contains one path from each end block together
with fixed attachment, middle, and interface paths.
-/
structure OffsetConcatenationGrid
    (G : SimpleGraph V)
    {x₁ y₁ x₂ y₂ : V}
    (left : AdmissiblePathFamily G x₁ y₁ 3)
    (right : AdmissiblePathFamily G x₂ y₂ 3) where
  /-- The fixed connector contribution added to every cycle length. -/
  offset : ℕ
  /-- The simple cycle obtained from each pair of paths and the connector. -/
  cycle : Fin 3 → Fin 3 → SimpleCycle G
  length_cycle : ∀ i j,
    (cycle i j).length =
      (left.path i).length +
        (right.path j).length + offset

/--
The same `3 × 3` arithmetic as paper Lemma 2.1, with any fixed
connector offset.  The grid contains actual `SimpleCycle` witnesses.
-/
theorem offset_three_by_three_forces_cycle_divisible_by_five
    (G : SimpleGraph V)
    {x₁ y₁ x₂ y₂ : V}
    (left : AdmissiblePathFamily G x₁ y₁ 3)
    (right : AdmissiblePathFamily G x₂ y₂ 3)
    (grid : OffsetConcatenationGrid G left right) :
    HasCycleDivisibleBy G 5 := by
  rcases left.admissible_step with hleft | hleft <;>
    rcases right.admissible_step with hright | hright
  ·
    let li : Fin 5 → Fin 3 := ![0, 1, 2, 2, 2]
    let ri : Fin 5 → Fin 3 := ![0, 0, 0, 1, 2]
    let F : AdmissibleCycleFamily G 5 := {
      start := left.start + right.start + grid.offset
      step := 1
      admissible_step := Or.inl rfl
      cycle i := grid.cycle (li i) (ri i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [li, ri, grid.length_cycle,
            left.length_path, right.length_path,
            hleft, hright] <;> omega
    }
    exact F.hasCycleDivisibleByFive
  ·
    let li : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]
    let ri : Fin 5 → Fin 3 := ![0, 0, 0, 1, 1]
    let F : AdmissibleCycleFamily G 5 := {
      start := left.start + right.start + grid.offset
      step := 1
      admissible_step := Or.inl rfl
      cycle i := grid.cycle (li i) (ri i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [li, ri, grid.length_cycle,
            left.length_path, right.length_path,
            hleft, hright] <;> omega
    }
    exact F.hasCycleDivisibleByFive
  ·
    let li : Fin 5 → Fin 3 := ![0, 0, 0, 1, 1]
    let ri : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]
    let F : AdmissibleCycleFamily G 5 := {
      start := left.start + right.start + grid.offset
      step := 1
      admissible_step := Or.inl rfl
      cycle i := grid.cycle (li i) (ri i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [li, ri, grid.length_cycle,
            left.length_path, right.length_path,
            hleft, hright] <;> omega
    }
    exact F.hasCycleDivisibleByFive
  ·
    let li : Fin 5 → Fin 3 := ![0, 1, 2, 2, 2]
    let ri : Fin 5 → Fin 3 := ![0, 0, 0, 1, 2]
    let F : AdmissibleCycleFamily G 5 := {
      start := left.start + right.start + grid.offset
      step := 2
      admissible_step := Or.inr rfl
      cycle i := grid.cycle (li i) (ri i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [li, ri, grid.length_cycle,
            left.length_path, right.length_path,
            hleft, hright] <;> omega
    }
    exact F.hasCycleDivisibleByFive

/--
Build an offset grid from a two-parameter family of framed side paths and
one fixed return path.  The disjointness premise is exactly Mathlib's
simple-cycle condition.
-/
def OffsetConcatenationGrid.ofSidePaths
    (G : SimpleGraph V)
    {x₁ y₁ x₂ y₂ s t : V}
    (left : AdmissiblePathFamily G x₁ y₁ 3)
    (right : AdmissiblePathFamily G x₂ y₂ 3)
    (sideOffset : ℕ)
    (side : Fin 3 → Fin 3 → SimplePath G s t)
    (returnPath : SimplePath G t s)
    (hsideLength : ∀ i j,
      (side i j).length =
        (left.path i).length +
          (right.path j).length + sideOffset)
    (hdisjoint : ∀ i j,
      (side i j).walk.support.tail.Disjoint
        returnPath.walk.support.tail) :
    OffsetConcatenationGrid G left right where
  offset := sideOffset + returnPath.length
  cycle i j :=
    cycleOfDisjointPaths
      (side i j) returnPath (hdisjoint i j)
      (Or.inl (by
        rw [hsideLength]
        have hleft : 2 ≤ (left.path i).length := by
          rw [left.length_path]
          exact left.start_ge_two.trans
            (Nat.le_add_right left.start
              (i.val * left.step))
        omega))
  length_cycle i j := by
    rw [cycleOfDisjointPaths_length,
      hsideLength]
    omega

/--
Build the closure grid from the precise support-disjointness condition
required by Mathlib's cycle constructor.
-/
def ConcatenationGrid.ofDisjointSupports
    (G : SimpleGraph V) {x y : V}
    (left : AdmissiblePathFamily G x y 3)
    (right : AdmissiblePathFamily G y x 3)
    (hdisj : ∀ i j,
      (left.path i).walk.support.tail.Disjoint
        (right.path j).walk.support.tail) :
    ConcatenationGrid G left right where
  cycle i j :=
    cycleOfDisjointPaths (left.path i) (right.path j) (hdisj i j)
      (Or.inl (by
        have hs : 2 ≤ left.start := left.start_ge_two
        rw [left.length_path]
        omega))
  length_cycle i j := by
    apply cycleOfDisjointPaths_length

/--
Two three-term admissible path families whose pairwise closures are certified
simple cycles yield five admissible cycles.
-/
theorem three_by_three_concatenation
    (G : SimpleGraph V) {x y : V}
    (left : AdmissiblePathFamily G x y 3)
    (right : AdmissiblePathFamily G y x 3)
    (closures : ConcatenationGrid G left right) :
    Nonempty (AdmissibleCycleFamily G 5) := by
  rcases left.admissible_step with hleft | hleft <;>
    rcases right.admissible_step with hright | hright
  ·
    let li : Fin 5 → Fin 3 := ![0, 1, 2, 2, 2]
    let ri : Fin 5 → Fin 3 := ![0, 0, 0, 1, 2]
    refine ⟨{
      start := left.start + right.start
      step := 1
      admissible_step := Or.inl rfl
      cycle i := closures.cycle (li i) (ri i)
      length_cycle := ?_
    }⟩
    intro i
    fin_cases i <;>
      simp [li, ri, closures.length_cycle,
        left.length_path, right.length_path, hleft, hright] <;> omega
  ·
    let li : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]
    let ri : Fin 5 → Fin 3 := ![0, 0, 0, 1, 1]
    refine ⟨{
      start := left.start + right.start
      step := 1
      admissible_step := Or.inl rfl
      cycle i := closures.cycle (li i) (ri i)
      length_cycle := ?_
    }⟩
    intro i
    fin_cases i <;>
      simp [li, ri, closures.length_cycle,
        left.length_path, right.length_path, hleft, hright] <;> omega
  ·
    let li : Fin 5 → Fin 3 := ![0, 0, 0, 1, 1]
    let ri : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]
    refine ⟨{
      start := left.start + right.start
      step := 1
      admissible_step := Or.inl rfl
      cycle i := closures.cycle (li i) (ri i)
      length_cycle := ?_
    }⟩
    intro i
    fin_cases i <;>
      simp [li, ri, closures.length_cycle,
        left.length_path, right.length_path, hleft, hright] <;> omega
  ·
    let li : Fin 5 → Fin 3 := ![0, 1, 2, 2, 2]
    let ri : Fin 5 → Fin 3 := ![0, 0, 0, 1, 2]
    refine ⟨{
      start := left.start + right.start
      step := 2
      admissible_step := Or.inr rfl
      cycle i := closures.cycle (li i) (ri i)
      length_cycle := ?_
    }⟩
    intro i
    fin_cases i <;>
      simp [li, ri, closures.length_cycle,
        left.length_path, right.length_path, hleft, hright] <;> omega

/-- The generic contradiction form used repeatedly below. -/
theorem three_by_three_forces_cycle_divisible_by_five
    (G : SimpleGraph V) {x y : V}
    (left : AdmissiblePathFamily G x y 3)
    (right : AdmissiblePathFamily G y x 3)
    (closures : ConcatenationGrid G left right) :
    HasCycleDivisibleBy G 5 := by
  obtain ⟨F⟩ := three_by_three_concatenation G left right closures
  exact F.hasCycleDivisibleByFive

/--
Support-disjointness alone is enough to obtain the five-cycle contradiction;
the simple-cycle witnesses are constructed rather than assumed.
-/
theorem disjoint_three_by_three_forces_cycle_divisible_by_five
    (G : SimpleGraph V) {x y : V}
    (left : AdmissiblePathFamily G x y 3)
    (right : AdmissiblePathFamily G y x 3)
    (hdisj : ∀ i j,
      (left.path i).walk.support.tail.Disjoint
        (right.path j).walk.support.tail) :
    HasCycleDivisibleBy G 5 :=
  three_by_three_forces_cycle_divisible_by_five G left right
    (ConcatenationGrid.ofDisjointSupports G left right hdisj)

/--
A three-term admissible family closed by paths of three consecutive lengths
produces five consecutive cycle lengths.  The admissible family supplies the
required path of length at least two.
-/
theorem admissible_three_plus_consecutive_three_forces_divisible_cycle
    (G : SimpleGraph V) {x y : V}
    (outside : AdmissiblePathFamily G x y 3)
    (core : ConsecutivePathTriple G y x)
    (hdisj : ∀ i j,
      (outside.path i).walk.support.tail.Disjoint
        (core.path j).walk.support.tail) :
    HasCycleDivisibleBy G 5 := by
  let close (i j : Fin 3) : SimpleCycle G :=
    cycleOfDisjointPaths (outside.path i) (core.path j) (hdisj i j)
      (Or.inl (by
        rw [outside.length_path]
        exact outside.start_ge_two.trans
          (Nat.le_add_right outside.start (i.val * outside.step))))
  rcases outside.admissible_step with hstep | hstep
  · let oi : Fin 5 → Fin 3 := ![0, 0, 0, 1, 2]
    let ci : Fin 5 → Fin 3 := ![0, 1, 2, 2, 2]
    let F : AdmissibleCycleFamily G 5 := {
      start := outside.start + core.start
      step := 1
      admissible_step := Or.inl rfl
      cycle i := close (oi i) (ci i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [close, oi, ci, cycleOfDisjointPaths_length,
            outside.length_path, core.length_path, hstep] <;> omega
    }
    exact F.hasCycleDivisibleByFive
  · let oi : Fin 5 → Fin 3 := ![0, 0, 0, 1, 1]
    let ci : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]
    let F : AdmissibleCycleFamily G 5 := {
      start := outside.start + core.start
      step := 1
      admissible_step := Or.inl rfl
      cycle i := close (oi i) (ci i)
      length_cycle := by
        intro i
        fin_cases i <;>
          simp [close, oi, ci, cycleOfDisjointPaths_length,
            outside.length_path, core.length_path, hstep] <;> omega
    }
    exact F.hasCycleDivisibleByFive

end DeanK5
