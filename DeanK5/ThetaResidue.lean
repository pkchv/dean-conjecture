import DeanK5.Graph.Basic

/-!
# Theta residues in girth six (paper Lemma 2.4)

This file proves paper Lemma 2.4 directly.  It replaces the unrestricted
wording of GHLM Lemma 5.12, for which `K₂,₃` is a boundary counterexample;
the girth-at-least-six hypothesis rules that case out.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Pairwise distinct natural-number residues modulo five. -/
def PairwiseModFive (a b c : ℕ) : Prop :=
  a % 5 ≠ b % 5 ∧
    a % 5 ≠ c % 5 ∧
    b % 5 ≠ c % 5

/--
The elementary choice of one of the first two internal vertices used when
exactly two theta-leg residues agree.
-/
theorem duplicate_residue_arithmetic
    {a b c : ℕ} (ha : 3 ≤ a)
    (hab : a % 5 = b % 5)
    (hac : a % 5 ≠ c % 5) :
    PairwiseModFive
        (a - 1) (1 + b) (1 + c) ∨
      PairwiseModFive
        (a - 2) (2 + b) (2 + c) := by
  by_cases hbad :
      (a - 1) % 5 = (1 + c) % 5
  · right
    unfold PairwiseModFive
    omega
  · left
    unfold PairwiseModFive
    omega

/--
Three reroutings suffice when all three theta-leg residues agree.  The
chosen interior points are among the first two vertices of two long legs.
-/
theorem equal_residue_arithmetic
    {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hab : a % 5 = b % 5)
    (hac : a % 5 = c % 5) :
    PairwiseModFive
        (1 + 1) ((a - 1) + (b - 1))
          (1 + c + (b - 1)) ∨
      PairwiseModFive
        (1 + 2) ((a - 1) + (b - 2))
          (1 + c + (b - 2)) ∨
      PairwiseModFive
        (2 + 1) ((a - 2) + (b - 1))
          (2 + c + (b - 1)) := by
  by_cases h11 :
      PairwiseModFive
        (1 + 1) ((a - 1) + (b - 1))
          (1 + c + (b - 1))
  · exact Or.inl h11
  by_cases h12 :
      PairwiseModFive
        (1 + 2) ((a - 1) + (b - 2))
          (1 + c + (b - 2))
  · exact Or.inr (Or.inl h12)
  right
  right
  unfold PairwiseModFive at h11 h12 ⊢
  omega

namespace Theta

/--
In girth at least six, the lengths of any two distinct theta legs sum to
at least six.
-/
theorem six_le_add_lengths
    (T : Theta G) (hgirth : GirthAtLeast G 6)
    {i j : Fin 3} (hij : i ≠ j) :
    6 ≤ (T.path i).length + (T.path j).length := by
  obtain ⟨w, -, -, c, hc, hlen⟩ :=
    (T.path i).isPath.exists_isCycle_length_le_add_of_ne
      (T.path j).isPath (T.paths_ne i j hij)
  exact (hgirth ⟨w, c, hc⟩).trans hlen

/--
Join an initial segment of leg `i`, traversed backwards, to the whole of
leg `j`.  The result runs from an internal point of `i` through the first
theta root and then to the second root.
-/
def viaStart
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r : ℕ) (hr : r < (T.path i).length) :
    SimplePath G ((T.path i).walk.getVert r) T.y :=
  (T.path i).take r |>.reverse |>.appendDisjoint
    (T.path j) (by
      apply List.disjoint_left.mpr
      intro z hzi hzj
      have hziTake :
          z ∈ ((T.path i).take r).walk.support := by
        simpa [SimplePath.reverse] using hzi
      have hziPath :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_take r hziTake
      have hzjPath :
          z ∈ (T.path j).walk.support :=
        List.mem_of_mem_tail hzj
      rcases T.eq_root_of_mem_two_paths hij
          hziPath hzjPath with rfl | rfl
      · exact (T.path j).start_not_mem_tail hzj
      · exact (T.path i).end_not_mem_take hr hziTake)

@[simp] theorem viaStart_length
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r : ℕ) (hr : r < (T.path i).length) :
    (T.viaStart hij r hr).length =
      r + (T.path j).length := by
  simp [viaStart, min_eq_left hr.le]

/--
Join terminal segments of two legs through the second theta root.
-/
def viaEnd
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r ≤ (T.path i).length) :
    SimplePath G ((T.path i).walk.getVert r)
      ((T.path j).walk.getVert s) :=
  (T.path i).drop r |>.appendDisjoint
    ((T.path j).drop s).reverse (by
      apply List.disjoint_left.mpr
      intro z hzi hzj
      have hziPath :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_drop r hzi
      have hzjReverse :
          z ∈ ((T.path j).drop s).reverse.walk.support :=
        List.mem_of_mem_tail hzj
      have hzjDrop :
          z ∈ ((T.path j).drop s).walk.support := by
        simpa [SimplePath.reverse] using hzjReverse
      have hzjPath :
          z ∈ (T.path j).walk.support :=
        (T.path j).mem_support_of_mem_drop s hzjDrop
      rcases T.eq_root_of_mem_two_paths hij
          hziPath hzjPath with rfl | rfl
      · exact (T.path i).start_not_mem_drop
          hrpos hr hzi
      · exact ((T.path j).drop s).reverse.start_not_mem_tail
          hzj)

@[simp] theorem viaEnd_length
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r ≤ (T.path i).length) :
    (T.viaEnd hij r s hrpos hr).length =
      ((T.path i).length - r) +
        ((T.path j).length - s) := by
  simp [viaEnd]

/--
Join two initial segments through the first theta root.
-/
def viaFirstRoot
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hr : r < (T.path i).length) :
    SimplePath G ((T.path i).walk.getVert r)
      ((T.path j).walk.getVert s) :=
  (T.path i).take r |>.reverse |>.appendDisjoint
    ((T.path j).take s) (by
      apply List.disjoint_left.mpr
      intro z hzi hzj
      have hziTake :
          z ∈ ((T.path i).take r).walk.support := by
        simpa [SimplePath.reverse] using hzi
      have hziPath :
          z ∈ (T.path i).walk.support :=
        (T.path i).mem_support_of_mem_take r hziTake
      have hzjPath :
          z ∈ (T.path j).walk.support :=
        (T.path j).mem_support_of_mem_take s
          (List.mem_of_mem_tail hzj)
      rcases T.eq_root_of_mem_two_paths hij
          hziPath hzjPath with rfl | rfl
      · exact ((T.path j).take s).start_not_mem_tail hzj
      · exact (T.path i).end_not_mem_take hr hziTake)

@[simp] theorem viaFirstRoot_length
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hr : r < (T.path i).length)
    (hs : s ≤ (T.path j).length) :
    (T.viaFirstRoot hij r s hr).length = r + s := by
  simp [viaFirstRoot, min_eq_left hr.le, min_eq_left hs]

/--
Run from leg `i` to the first root, along leg `k`, and then backwards
along the terminal segment of leg `j`.
-/
def viaMiddle
    (T : Theta G) {i j k : Fin 3}
    (hik : i ≠ k) (hij : i ≠ j) (hkj : k ≠ j)
    (r s : ℕ)
    (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s ≤ (T.path j).length) :
    SimplePath G ((T.path i).walk.getVert r)
      ((T.path j).walk.getVert s) :=
  (T.viaStart hik r hr).appendDisjoint
    ((T.path j).drop s).reverse (by
      apply List.disjoint_left.mpr
      intro z hzleft hzright
      have hzrightSupport :
          z ∈ ((T.path j).drop s).reverse.walk.support :=
        List.mem_of_mem_tail hzright
      have hzrightDrop :
          z ∈ ((T.path j).drop s).walk.support := by
        simpa [SimplePath.reverse] using hzrightSupport
      have hzj :
          z ∈ (T.path j).walk.support :=
        (T.path j).mem_support_of_mem_drop s hzrightDrop
      have hxRight :
          T.x ∉ ((T.path j).drop s).reverse.walk.support := by
        simpa [SimplePath.reverse] using
          (T.path j).start_not_mem_drop hspos hs
      have hyRightTail :
          T.y ∉ ((T.path j).drop s).reverse.walk.support.tail :=
        ((T.path j).drop s).reverse.start_not_mem_tail
      simp only [viaStart, SimplePath.appendDisjoint,
        SimpleGraph.Walk.support_append,
        List.mem_append] at hzleft
      rcases hzleft with hzi | hzk
      · have hziTake :
            z ∈ ((T.path i).take r).walk.support := by
          simpa [SimplePath.reverse] using hzi
        have hziPath :
            z ∈ (T.path i).walk.support :=
          (T.path i).mem_support_of_mem_take r hziTake
        rcases T.eq_root_of_mem_two_paths hij
            hziPath hzj with rfl | rfl
        · exact hxRight hzrightSupport
        · exact hyRightTail hzright
      · have hzkPath :
            z ∈ (T.path k).walk.support :=
          List.mem_of_mem_tail hzk
        rcases T.eq_root_of_mem_two_paths hkj
            hzkPath hzj with rfl | rfl
        · exact hxRight hzrightSupport
        · exact hyRightTail hzright)

@[simp] theorem viaMiddle_length
    (T : Theta G) {i j k : Fin 3}
    (hik : i ≠ k) (hij : i ≠ j) (hkj : k ≠ j)
    (r s : ℕ)
    (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s ≤ (T.path j).length) :
    (T.viaMiddle hik hij hkj r s hr hspos hs).length =
      r + (T.path k).length +
        ((T.path j).length - s) := by
  simp [viaMiddle, Nat.add_assoc]

theorem containsPath_viaStart
    [DecidableEq V]
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r : ℕ) (hr : r < (T.path i).length) :
    T.ContainsPath (T.viaStart hij r hr) := by
  apply ContainsPath.appendDisjoint
  · exact (T.containsPath_path i).take r |>.reverse
  · exact T.containsPath_path j

theorem containsPath_viaEnd
    [DecidableEq V]
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hrpos : 0 < r) (hr : r ≤ (T.path i).length) :
    T.ContainsPath (T.viaEnd hij r s hrpos hr) := by
  apply ContainsPath.appendDisjoint
  · exact (T.containsPath_path i).drop r
  · exact (T.containsPath_path j).drop s |>.reverse

theorem containsPath_viaFirstRoot
    [DecidableEq V]
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j)
    (r s : ℕ)
    (hr : r < (T.path i).length) :
    T.ContainsPath (T.viaFirstRoot hij r s hr) := by
  apply ContainsPath.appendDisjoint
  · exact (T.containsPath_path i).take r |>.reverse
  · exact (T.containsPath_path j).take s

theorem containsPath_viaMiddle
    [DecidableEq V]
    (T : Theta G) {i j k : Fin 3}
    (hik : i ≠ k) (hij : i ≠ j) (hkj : k ≠ j)
    (r s : ℕ)
    (hr : r < (T.path i).length)
    (hspos : 0 < s) (hs : s ≤ (T.path j).length) :
    T.ContainsPath
      (T.viaMiddle hik hij hkj r s hr hspos hs) := by
  apply ContainsPath.appendDisjoint
  · exact T.containsPath_viaStart hik r hr
  · exact (T.containsPath_path j).drop s |>.reverse

/--
Reroute at one of the first two internal vertices of a long repeated-residue
leg when the third leg has a different residue.
-/
theorem exists_three_paths_of_duplicate_long
    [DecidableEq V]
    (T : Theta G) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k)
    (hi : 3 ≤ (T.path i).length)
    (hmodij :
      (T.path i).length % 5 =
        (T.path j).length % 5)
    (hmodik :
      (T.path i).length % 5 ≠
        (T.path k).length % 5) :
    ∃ (x y : V), x ≠ y ∧
      ∃ P : Fin 3 → SimplePath G x y,
        (∀ q, T.ContainsPath (P q)) ∧
        (∀ q q', q ≠ q' →
          (P q).length % 5 ≠
            (P q').length % 5) := by
  have harith :=
    duplicate_residue_arithmetic hi hmodij hmodik
  have make :
      ∀ (r : ℕ),
        0 < r → r < (T.path i).length →
        PairwiseModFive
          ((T.path i).length - r)
          (r + (T.path j).length)
          (r + (T.path k).length) →
        ∃ (x y : V), x ≠ y ∧
          ∃ P : Fin 3 → SimplePath G x y,
            (∀ q, T.ContainsPath (P q)) ∧
            (∀ q q', q ≠ q' →
              (P q).length % 5 ≠
                (P q').length % 5) := by
    intro r hrpos hr hpair
    have hrle : r ≤ (T.path i).length := hr.le
    let P : Fin 3 →
        SimplePath G ((T.path i).walk.getVert r) T.y :=
      ![(T.path i).drop r,
        T.viaStart hij r hr,
        T.viaStart hik r hr]
    have hxy :
        (T.path i).walk.getVert r ≠ T.y := by
      intro heq
      have hrEq :
          r = (T.path i).walk.length :=
        ((T.path i).isPath.getVert_eq_end_iff
          (by simpa [SimplePath.length] using hrle)).1 heq
      simpa [SimplePath.length] using hr.ne hrEq
    refine ⟨_, T.y, hxy, P, ?_, ?_⟩
    · intro q
      fin_cases q
      · exact (T.containsPath_path i).drop r
      · exact T.containsPath_viaStart hij r hr
      · exact T.containsPath_viaStart hik r hr
    · intro q q' hqq'
      fin_cases q <;> fin_cases q' <;>
        simp_all [P, PairwiseModFive] <;> omega
  rcases harith with h1 | h2
  · exact make 1 (by omega) (by omega) (by simpa using h1)
  · exact make 2 (by omega) (by omega) (by simpa using h2)

/--
The duplicate-residue case. Girth six guarantees that one of the two
equal-residue legs is long enough to reroute at its first two vertices.
-/
theorem exists_three_paths_of_duplicate
    [DecidableEq V]
    (T : Theta G) (hgirth : GirthAtLeast G 6)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmodij :
      (T.path i).length % 5 =
        (T.path j).length % 5)
    (hmodik :
      (T.path i).length % 5 ≠
        (T.path k).length % 5) :
    ∃ (x y : V), x ≠ y ∧
      ∃ P : Fin 3 → SimplePath G x y,
        (∀ q, T.ContainsPath (P q)) ∧
        (∀ q q', q ≠ q' →
          (P q).length % 5 ≠
            (P q').length % 5) := by
  have hsum :=
    T.six_le_add_lengths hgirth hij
  by_cases hi : 3 ≤ (T.path i).length
  · exact T.exists_three_paths_of_duplicate_long
      hij hik hi hmodij hmodik
  · have hj : 3 ≤ (T.path j).length := by
      omega
    have hmodjk :
        (T.path j).length % 5 ≠
          (T.path k).length % 5 := by
      intro heq
      exact hmodik (hmodij.trans heq)
    exact T.exists_three_paths_of_duplicate_long
      hij.symm hjk hj hmodij.symm hmodjk

/--
The all-equal-residue case. Two legs are long by the pairwise girth-six
bounds; choosing their first or second internal vertices yields three
reroutings with distinct residues.
-/
theorem exists_three_paths_of_all_equal_long
    [DecidableEq V]
    (T : Theta G) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (hi : 3 ≤ (T.path i).length)
    (hj : 3 ≤ (T.path j).length)
    (hmodij :
      (T.path i).length % 5 =
        (T.path j).length % 5)
    (hmodik :
      (T.path i).length % 5 =
        (T.path k).length % 5) :
    ∃ (x y : V), x ≠ y ∧
      ∃ P : Fin 3 → SimplePath G x y,
        (∀ q, T.ContainsPath (P q)) ∧
        (∀ q q', q ≠ q' →
          (P q).length % 5 ≠
            (P q').length % 5) := by
  have harith :=
    equal_residue_arithmetic hi hj hmodij hmodik
  have make :
      ∀ (r s : ℕ),
        0 < r → r < (T.path i).length →
        0 < s → s < (T.path j).length →
        PairwiseModFive
          (r + s)
          (((T.path i).length - r) +
            ((T.path j).length - s))
          (r + (T.path k).length +
            ((T.path j).length - s)) →
        ∃ (x y : V), x ≠ y ∧
          ∃ P : Fin 3 → SimplePath G x y,
            (∀ q, T.ContainsPath (P q)) ∧
            (∀ q q', q ≠ q' →
              (P q).length % 5 ≠
                (P q').length % 5) := by
    intro r s hrpos hr hspos hs hpair
    have hrle : r ≤ (T.path i).length := hr.le
    have hsle : s ≤ (T.path j).length := hs.le
    let P : Fin 3 →
        SimplePath G
          ((T.path i).walk.getVert r)
          ((T.path j).walk.getVert s) :=
      ![T.viaFirstRoot hij r s hr,
        T.viaEnd hij r s hrpos hrle,
        T.viaMiddle hik hij hkj r s
          hr hspos hsle]
    have hxy :
        (T.path i).walk.getVert r ≠
          (T.path j).walk.getVert s := by
      intro heq
      have hir :
          (T.path i).walk.getVert r ∈
            (T.path i).walk.support :=
        SimpleGraph.Walk.getVert_mem_support _ _
      have hjr :
          (T.path i).walk.getVert r ∈
            (T.path j).walk.support := by
        rw [heq]
        exact SimpleGraph.Walk.getVert_mem_support _ _
      rcases T.eq_root_of_mem_two_paths hij hir hjr with hx | hy
      · have :
            r = 0 :=
          ((T.path i).isPath.getVert_eq_start_iff
            (by simpa [SimplePath.length] using hrle)).1 hx
        omega
      · have :
            r = (T.path i).walk.length :=
          ((T.path i).isPath.getVert_eq_end_iff
            (by simpa [SimplePath.length] using hrle)).1 hy
        simpa [SimplePath.length] using hr.ne this
    refine ⟨_, _, hxy, P, ?_, ?_⟩
    · intro q
      fin_cases q
      · exact T.containsPath_viaFirstRoot hij r s hr
      · exact T.containsPath_viaEnd hij r s hrpos hrle
      · exact T.containsPath_viaMiddle
          hik hij hkj r s hr hspos hsle
    · intro q q' hqq'
      fin_cases q <;> fin_cases q' <;>
        simp_all [P, PairwiseModFive] <;> omega
  rcases harith with h11 | h12 | h21
  · exact make 1 1 (by omega) (by omega)
      (by omega) (by omega) (by simpa using h11)
  · exact make 1 2 (by omega) (by omega)
      (by omega) (by omega) (by simpa using h12)
  · exact make 2 1 (by omega) (by omega)
      (by omega) (by omega) (by simpa using h21)

end Theta

/--
Every theta in a graph of girth at least six contains three paths between
some pair of distinct vertices whose lengths are pairwise distinct modulo
five.

This is paper Lemma 2.4, the precisely scoped form of the
unrestricted wording of GHLM Lemma 5.12.
-/
theorem theta_three_distinct_residue_paths_of_girth_six
    [DecidableEq V]
    (G : SimpleGraph V) (hgirth : GirthAtLeast G 6)
    (T : Theta G) :
    ∃ (x y : V), x ≠ y ∧
      ∃ P : Fin 3 → SimplePath G x y,
        (∀ q, T.ContainsPath (P q)) ∧
        (∀ q q', q ≠ q' →
          (P q).length % 5 ≠
            (P q').length % 5) := by
  let l : Fin 3 → ℕ := fun i => (T.path i).length
  by_cases h01 : l 0 % 5 = l 1 % 5
  · by_cases h02 : l 0 % 5 = l 2 % 5
    · have h12 : l 1 % 5 = l 2 % 5 :=
        h01.symm.trans h02
      have hsum01 :
          6 ≤ l 0 + l 1 :=
        T.six_le_add_lengths hgirth (by decide)
      have hsum02 :
          6 ≤ l 0 + l 2 :=
        T.six_le_add_lengths hgirth (by decide)
      have hsum12 :
          6 ≤ l 1 + l 2 :=
        T.six_le_add_lengths hgirth (by decide)
      by_cases h0 : 3 ≤ l 0
      · by_cases h1 : 3 ≤ l 1
        · exact T.exists_three_paths_of_all_equal_long
            (i := 0) (j := 1) (k := 2)
            (by decide) (by decide) (by decide)
            h0 h1 h01 h02
        · have h2 : 3 ≤ l 2 := by omega
          exact T.exists_three_paths_of_all_equal_long
            (i := 0) (j := 2) (k := 1)
            (by decide) (by decide) (by decide)
            h0 h2 h02 h01
      · have h1 : 3 ≤ l 1 := by omega
        have h2 : 3 ≤ l 2 := by omega
        exact T.exists_three_paths_of_all_equal_long
          (i := 1) (j := 2) (k := 0)
          (by decide) (by decide) (by decide)
          h1 h2 h12 h01.symm
    · exact T.exists_three_paths_of_duplicate
        hgirth (i := 0) (j := 1) (k := 2)
        (by decide) (by decide) (by decide)
        h01 h02
  · by_cases h02 : l 0 % 5 = l 2 % 5
    · exact T.exists_three_paths_of_duplicate
        hgirth (i := 0) (j := 2) (k := 1)
        (by decide) (by decide) (by decide)
        h02 h01
    · by_cases h12 : l 1 % 5 = l 2 % 5
      · have h10 : l 1 % 5 ≠ l 0 % 5 :=
          fun h => h01 h.symm
        exact T.exists_three_paths_of_duplicate
          hgirth (i := 1) (j := 2) (k := 0)
          (by decide) (by decide) (by decide)
          h12 h10
      · refine ⟨T.x, T.y, T.roots_ne,
          T.path, T.containsPath_path, ?_⟩
        intro q q' hqq'
        fin_cases q <;> fin_cases q' <;>
          simp_all [l] <;> omega

end DeanK5
