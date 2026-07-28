import DeanK5.BoundaryLifting
import DeanK5.BipartitePaths
import DeanK5.Graph.BoundaryAuxiliary
import DeanK5.SmallSubgraphs

/-!
# Boundary lifting and the four-cycle exclusion (paper Section 6)

This module starts with the variable-endpoint form of the concatenation
arithmetic used throughout the lifted complete-bipartite-core argument.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
A certified grid of simple cycles formed by closing each member of an
admissible variable-endpoint sequence with a core path progression.
-/
structure PathSequenceCoreGrid
    (G : SimpleGraph V) {q : ℕ}
    (outside : AdmissiblePathSequence G q) (r : ℕ) where
  /-- The length of the first core return path. -/
  coreStart : ℕ
  /-- The common difference of the core return-path lengths. -/
  coreStep : ℕ
  core_admissible_step : IsAdmissibleStep coreStep
  /-- The certified cycle formed from outside path `i` and core path `j`. -/
  cycle : Fin q → Fin r → SimpleCycle G
  length_cycle : ∀ i j,
    (cycle i j).length =
      (outside.path i).length + coreStart + j.val * coreStep

/--
Construct the core grid from actual return paths and the exact
support-disjointness condition required for their unions to be simple
cycles.
-/
def PathSequenceCoreGrid.ofDisjointCorePaths
    (G : SimpleGraph V) {q r : ℕ}
    (outside : AdmissiblePathSequence G q)
    (coreStart coreStep : ℕ)
    (hcoreStep : IsAdmissibleStep coreStep)
    (core : ∀ i : Fin q, ∀ _j : Fin r,
      SimplePath G (outside.y i) (outside.x i))
    (hcoreLength : ∀ i j,
      (core i j).length = coreStart + j.val * coreStep)
    (hdisjoint : ∀ i j,
      (outside.path i).walk.support.tail.Disjoint
        (core i j).walk.support.tail) :
    PathSequenceCoreGrid G outside r where
  coreStart := coreStart
  coreStep := coreStep
  core_admissible_step := hcoreStep
  cycle i j :=
    cycleOfDisjointPaths (outside.path i) (core i j)
      (hdisjoint i j)
      (Or.inl (by
        rw [outside.length_path]
        exact outside.start_ge_two.trans
          (Nat.le_add_right outside.start
            (i.val * outside.step))))
  length_cycle i j := by
    rw [cycleOfDisjointPaths_length, hcoreLength]
    omega

/--
A concrete selection of five entries of the closure grid whose offset sums
form an admissible five-term progression forces a mod-five cycle.
-/
theorem PathSequenceCoreGrid.force_with_selection
    (G : SimpleGraph V) {q r : ℕ}
    (outside : AdmissiblePathSequence G q)
    (grid : PathSequenceCoreGrid G outside r)
    (oi : Fin 5 → Fin q) (ci : Fin 5 → Fin r)
    (d : ℕ) (hd : IsAdmissibleStep d)
    (hoffset : ∀ k,
      (oi k).val * outside.step +
        (ci k).val * grid.coreStep = k.val * d) :
    HasCycleDivisibleBy G 5 := by
  let F : AdmissibleCycleFamily G 5 := {
    start := outside.start + grid.coreStart
    step := d
    admissible_step := hd
    cycle k := grid.cycle (oi k) (ci k)
    length_cycle := by
      intro k
      rw [grid.length_cycle, outside.length_path]
      have hk := hoffset k
      omega
  }
  exact F.hasCycleDivisibleByFive

/--
The form of paper Lemma 2.2 used in every case of Lemma 6.3:
at least two outside paths and at least two core paths, with a total of six,
produce five admissible simple cycles.
-/
theorem six_path_grid_forces_divisible_cycle
    (G : SimpleGraph V) {q r : ℕ}
    (outside : AdmissiblePathSequence G q)
    (grid : PathSequenceCoreGrid G outside r)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hsix : q + r = 6) :
    HasCycleDivisibleBy G 5 := by
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 := by omega
  rcases hcases with hq2 | hq3 | hq4
  · subst q
    have hr4 : r = 4 := by omega
    subst r
    rcases outside.admissible_step with hout | hout <;>
      rcases grid.core_admissible_step with hcore | hcore
    · let oi : Fin 5 → Fin 2 := ![0, 1, 1, 1, 1]
      let ci : Fin 5 → Fin 4 := ![0, 0, 1, 2, 3]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 2 := ![0, 1, 0, 1, 0]
      let ci : Fin 5 → Fin 4 := ![0, 0, 1, 1, 2]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 2 := ![0, 0, 0, 0, 1]
      let ci : Fin 5 → Fin 4 := ![0, 1, 2, 3, 2]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 2 := ![0, 1, 1, 1, 1]
      let ci : Fin 5 → Fin 4 := ![0, 0, 1, 2, 3]
      apply grid.force_with_selection G outside oi ci 2 (Or.inr rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
  · subst q
    have hr3 : r = 3 := by omega
    subst r
    rcases outside.admissible_step with hout | hout <;>
      rcases grid.core_admissible_step with hcore | hcore
    · let oi : Fin 5 → Fin 3 := ![0, 1, 2, 2, 2]
      let ci : Fin 5 → Fin 3 := ![0, 0, 0, 1, 2]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]
      let ci : Fin 5 → Fin 3 := ![0, 0, 0, 1, 1]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 3 := ![0, 0, 0, 1, 1]
      let ci : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 3 := ![0, 1, 2, 2, 2]
      let ci : Fin 5 → Fin 3 := ![0, 0, 0, 1, 2]
      apply grid.force_with_selection G outside oi ci 2 (Or.inr rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
  · subst q
    have hr2 : r = 2 := by omega
    subst r
    rcases outside.admissible_step with hout | hout <;>
      rcases grid.core_admissible_step with hcore | hcore
    · let oi : Fin 5 → Fin 4 := ![0, 1, 2, 3, 3]
      let ci : Fin 5 → Fin 2 := ![0, 0, 0, 0, 1]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 4 := ![0, 1, 2, 3, 2]
      let ci : Fin 5 → Fin 2 := ![0, 0, 0, 0, 1]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 4 := ![0, 0, 1, 1, 2]
      let ci : Fin 5 → Fin 2 := ![0, 1, 0, 1, 0]
      apply grid.force_with_selection G outside oi ci 1 (Or.inl rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]
    · let oi : Fin 5 → Fin 4 := ![0, 1, 2, 3, 3]
      let ci : Fin 5 → Fin 2 := ![0, 0, 0, 0, 1]
      apply grid.force_with_selection G outside oi ci 2 (Or.inr rfl)
      intro k
      fin_cases k <;> simp [oi, ci, hout, hcore]

universe v

variable {W : Type v}

/--
A copy of a complete bipartite graph, or one with one cross-edge deleted,
on an explicit carrier inside `J`.
-/
structure BipartiteCore
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) where
  /-- The ambient vertices occupied by the bipartite core. -/
  carrier : Finset W
  /-- The left bipartition class on the induced carrier. -/
  left : Finset (↑carrier : Set W)
  /-- The right bipartition class on the induced carrier. -/
  right : Finset (↑carrier : Set W)
  core : IsCompleteBipartiteMinusAtMostOne
    (J.induce (↑carrier : Set W)) left right

namespace BipartiteCore

variable [Fintype W] [DecidableEq W]
    {J : SimpleGraph W}

/-- The smaller of the two bipartition-class sizes. -/
def rank (C : BipartiteCore J) : ℕ :=
  min C.left.card C.right.card

theorem two_le_rank (C : BipartiteCore J) :
    2 ≤ C.rank :=
  C.core.2.2.1

theorem sides_cover (C : BipartiteCore J) :
    C.left ∪ C.right = Finset.univ :=
  C.core.2.1

/-- Exchange the two sides of a bipartite core, including the orientation
of its possible missing cross-edge. -/
def swap (C : BipartiteCore J) : BipartiteCore J where
  carrier := C.carrier
  left := C.right
  right := C.left
  core := by
    rcases C.core with
      ⟨hdisjoint, hcover, hrank,
        missing, hmissingParts, hmissingSize, hadj⟩
    refine ⟨hdisjoint.symm, ?_, ?_, ?_⟩
    · rw [Finset.union_comm]
      exact hcover
    · simpa [Nat.min_comm] using hrank
    · cases missing with
      | none =>
          refine ⟨none, ?_, ?_, ?_⟩
          · intro p hp
            simp at hp
          · simp
          · intro u v
            simpa [or_comm] using hadj u v
      | some p =>
          refine ⟨some (p.2, p.1), ?_, ?_, ?_⟩
          · intro q hq
            have hqp : q = (p.2, p.1) := by
              simpa using hq.symm
            subst q
            have hpParts :=
              hmissingParts p rfl
            exact ⟨hpParts.2, hpParts.1⟩
          · have hsize := hmissingSize (by simp)
            simpa [Nat.max_comm] using hsize
          · intro u v
            simpa [or_comm, and_comm, and_left_comm] using
              hadj u v

@[simp] theorem rank_swap (C : BipartiteCore J) :
    C.swap.rank = C.rank := by
  simp [swap, rank, Nat.min_comm]

/--
Regard a raw finite vertex set `A ⊆ U` as a finite set in the subtype
carried by `U`.  Keeping this coercion explicit avoids silently identifying
the two subtype carriers when a core vertex is deleted.
-/
def rawSide (U A : Finset W) (hAU : A ⊆ U) :
    Finset (↑U : Set W) :=
  A.attach.map {
    toFun := fun x => ⟨x.1, hAU x.2⟩
    inj' := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg
        (fun z : (↑U : Set W) => z.1) hxy
  }

omit [Fintype W] [DecidableEq W] in
@[simp] theorem mem_rawSide
    (U A : Finset W) (hAU : A ⊆ U)
    (x : (↑U : Set W)) :
    x ∈ rawSide U A hAU ↔ x.1 ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, -, hax⟩ :=
      Finset.mem_map.1 hx
    have haval : a.1 = x.1 :=
      congrArg (fun z : (↑U : Set W) => z.1) hax
    exact haval ▸ a.2
  · intro hx
    apply Finset.mem_map.2
    refine ⟨⟨x.1, hx⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

omit [Fintype W] [DecidableEq W] in
@[simp] theorem card_rawSide
    (U A : Finset W) (hAU : A ⊆ U) :
    (rawSide U A hAU).card = A.card := by
  simp [rawSide]

/--
Construct a certified complete bipartite core from raw, disjoint vertex
sets and an exact ambient adjacency characterization on their union.
-/
def ofCompleteRaw
    (J : SimpleGraph W)
    (L R : Finset W)
    (hLR : Disjoint L R)
    (hLcard : 2 ≤ L.card)
    (hRcard : 2 ≤ R.card)
    (hadj :
      ∀ u v : W,
        u ∈ L ∪ R → v ∈ L ∪ R →
          (J.Adj u v ↔
            (u ∈ L ∧ v ∈ R) ∨
              (u ∈ R ∧ v ∈ L))) :
    BipartiteCore J where
  carrier := L ∪ R
  left := rawSide (L ∪ R) L
    (fun _ hx => Finset.mem_union_left R hx)
  right := rawSide (L ∪ R) R
    (fun _ hx => Finset.mem_union_right L hx)
  core := by
    let hLsub : L ⊆ L ∪ R :=
      fun _ hx => Finset.mem_union_left R hx
    let hRsub : R ⊆ L ∪ R :=
      fun _ hx => Finset.mem_union_right L hx
    refine ⟨?_, ?_, ?_, none, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro x hxL hxR
      exact Finset.disjoint_left.mp hLR
        ((mem_rawSide (L ∪ R) L hLsub x).1 hxL)
        ((mem_rawSide (L ∪ R) R hRsub x).1 hxR)
    · ext x
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      have hx : x.1 ∈ L ∪ R := x.2
      rcases Finset.mem_union.mp hx with hxL | hxR
      · exact Or.inl
          ((mem_rawSide (L ∪ R) L hLsub x).2 hxL)
      · exact Or.inr
          ((mem_rawSide (L ∪ R) R hRsub x).2 hxR)
    · rw [card_rawSide, card_rawSide]
      omega
    · intro p hp
      simp at hp
    · simp
    · intro u v
      have hu : u.1 ∈ L ∪ R := u.2
      have hv : v.1 ∈ L ∪ R := v.2
      change
        J.Adj u.1 v.1 ↔
          (((u ∈ rawSide (L ∪ R) L hLsub ∧
              v ∈ rawSide (L ∪ R) R hRsub) ∨
            (u ∈ rawSide (L ∪ R) R hRsub ∧
              v ∈ rawSide (L ∪ R) L hLsub)) ∧ True)
      rw [hadj u.1 v.1 hu hv]
      simp only [mem_rawSide, and_true]

/--
Construct a certified one-missing-edge bipartite core from raw, disjoint
vertex sets and an exact ambient adjacency characterization on their
union.
-/
def ofMissingRaw
    (J : SimpleGraph W)
    (L R : Finset W)
    (xMissing yMissing : W)
    (hLR : Disjoint L R)
    (hxMissing : xMissing ∈ L)
    (hyMissing : yMissing ∈ R)
    (hLcard : 2 ≤ L.card)
    (hRcard : 2 ≤ R.card)
    (hlarge : 3 ≤ max L.card R.card)
    (hadj :
      ∀ u v : W,
        u ∈ L ∪ R → v ∈ L ∪ R →
          (J.Adj u v ↔
            ((u ∈ L ∧ v ∈ R) ∨
              (u ∈ R ∧ v ∈ L)) ∧
            ¬((u = xMissing ∧ v = yMissing) ∨
              (u = yMissing ∧ v = xMissing)))) :
    BipartiteCore J where
  carrier := L ∪ R
  left := rawSide (L ∪ R) L
    (fun _ hx => Finset.mem_union_left R hx)
  right := rawSide (L ∪ R) R
    (fun _ hx => Finset.mem_union_right L hx)
  core := by
    let hLsub : L ⊆ L ∪ R :=
      fun _ hx => Finset.mem_union_left R hx
    let hRsub : R ⊆ L ∪ R :=
      fun _ hx => Finset.mem_union_right L hx
    let xC : (↑(L ∪ R) : Set W) :=
      ⟨xMissing, hLsub hxMissing⟩
    let yC : (↑(L ∪ R) : Set W) :=
      ⟨yMissing, hRsub hyMissing⟩
    refine ⟨?_, ?_, ?_,
      some (xC, yC), ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro z hzL hzR
      exact Finset.disjoint_left.mp hLR
        ((mem_rawSide (L ∪ R) L hLsub z).1 hzL)
        ((mem_rawSide (L ∪ R) R hRsub z).1 hzR)
    · ext z
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      rcases Finset.mem_union.mp z.2 with hzL | hzR
      · exact Or.inl
          ((mem_rawSide (L ∪ R) L hLsub z).2 hzL)
      · exact Or.inr
          ((mem_rawSide (L ∪ R) R hRsub z).2 hzR)
    · rw [card_rawSide, card_rawSide]
      omega
    · intro p hp
      have hpEq : (xC, yC) = p := by
        simpa only [Option.some.injEq] using hp
      subst p
      exact ⟨
        (mem_rawSide (L ∪ R) L hLsub xC).2
          hxMissing,
        (mem_rawSide (L ∪ R) R hRsub yC).2
          hyMissing⟩
    · intro _
      simpa only [card_rawSide] using hlarge
    · intro u v
      have hu : u.1 ∈ L ∪ R := u.2
      have hv : v.1 ∈ L ∪ R := v.2
      change
        J.Adj u.1 v.1 ↔
          (((u ∈ rawSide (L ∪ R) L hLsub ∧
              v ∈ rawSide (L ∪ R) R hRsub) ∨
            (u ∈ rawSide (L ∪ R) R hRsub ∧
              v ∈ rawSide (L ∪ R) L hLsub)) ∧
            ¬((u = xC ∧ v = yC) ∨
              (u = yC ∧ v = xC)))
      rw [hadj u.1 v.1 hu hv]
      simp only [mem_rawSide]
      apply and_congr_right
      intro _
      apply not_congr
      constructor
      · rintro (⟨hux, hvy⟩ | ⟨huy, hvx⟩)
        · left
          constructor
          · apply Subtype.ext
            exact hux
          · apply Subtype.ext
            exact hvy
        · right
          constructor
          · apply Subtype.ext
            exact huy
          · apply Subtype.ext
            exact hvx
      · rintro (⟨hux, hvy⟩ | ⟨huy, hvx⟩)
        · left
          exact ⟨congrArg Subtype.val hux,
            congrArg Subtype.val hvy⟩
        · right
          exact ⟨congrArg Subtype.val huy,
            congrArg Subtype.val hvx⟩

end BipartiteCore

/-- Forget the carrier subtype on a finite set of core vertices. -/
def coreVertexSet
    {J : SimpleGraph W} [Fintype W] [DecidableEq W]
    (C : BipartiteCore J)
    (A : Finset (↑C.carrier : Set W)) : Finset W :=
  A.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem card_coreVertexSet
    {J : SimpleGraph W} [Fintype W] [DecidableEq W]
    (C : BipartiteCore J)
    (A : Finset (↑C.carrier : Set W)) :
    (coreVertexSet C A).card = A.card := by
  simp [coreVertexSet]

@[simp] theorem mem_coreVertexSet
    {J : SimpleGraph W} [Fintype W] [DecidableEq W]
    (C : BipartiteCore J)
    (A : Finset (↑C.carrier : Set W)) (x : W) :
    x ∈ coreVertexSet C A ↔
      ∃ hx : x ∈ C.carrier,
        (⟨x, hx⟩ : (↑C.carrier : Set W)) ∈ A := by
  simp [coreVertexSet]

theorem disjoint_coreVertexSet
    {J : SimpleGraph W} [Fintype W] [DecidableEq W]
    (C : BipartiteCore J)
    {A E : Finset (↑C.carrier : Set W)}
    (hAE : Disjoint A E) :
    Disjoint (coreVertexSet C A) (coreVertexSet C E) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxE
  obtain ⟨hxC, hxA'⟩ :=
    (mem_coreVertexSet C A x).1 hxA
  obtain ⟨hxC', hxE'⟩ :=
    (mem_coreVertexSet C E x).1 hxE
  have hsub :
      (⟨x, hxC⟩ : (↑C.carrier : Set W)) =
        ⟨x, hxC'⟩ :=
    Subtype.ext rfl
  exact Finset.disjoint_left.mp hAE hxA'
    (hsub ▸ hxE')

/-- Forgetting the carrier subtype sends the two core sides onto the full
raw carrier. -/
theorem union_coreVertexSet_sides
    {J : SimpleGraph W} [Fintype W] [DecidableEq W]
    (C : BipartiteCore J) :
    coreVertexSet C C.left ∪
        coreVertexSet C C.right =
      C.carrier := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxL | hxR
    · exact ((mem_coreVertexSet C C.left x).1 hxL).choose
    · exact ((mem_coreVertexSet C C.right x).1 hxR).choose
  · intro hxC
    let xC : (↑C.carrier : Set W) := ⟨x, hxC⟩
    have hxSides : xC ∈ C.left ∪ C.right := by
      rw [C.sides_cover]
      simp
    rcases Finset.mem_union.mp hxSides with hxL | hxR
    · exact Finset.mem_union_left _
        ((mem_coreVertexSet C C.left x).2
          ⟨hxC, hxL⟩)
    · exact Finset.mem_union_right _
        ((mem_coreVertexSet C C.right x).2
          ⟨hxC, hxR⟩)

namespace BipartiteCore

variable [Fintype W] [DecidableEq W]
    {J : SimpleGraph W}

/-- Concrete data exposed when the core certificate has one missing edge. -/
structure MissingEdgeData (C : BipartiteCore J) where
  /-- The left endpoint of the unique missing cross-edge. -/
  xMissing : W
  /-- The right endpoint of the unique missing cross-edge. -/
  yMissing : W
  x_left : xMissing ∈ coreVertexSet C C.left
  y_right : yMissing ∈ coreVertexSet C C.right
  large_side : 3 ≤ max C.left.card C.right.card
  cross_except_left :
    ∀ x ∈ coreVertexSet C C.left,
      ∀ y ∈ coreVertexSet C C.right,
        x ≠ xMissing → J.Adj x y
  cross_except :
    ∀ x ∈ coreVertexSet C C.left,
      ∀ y ∈ coreVertexSet C C.right,
        y ≠ yMissing → J.Adj x y
  missing_not_adjacent : ¬ J.Adj xMissing yMissing

/--
Expose the exact complete-versus-one-missing-edge dichotomy from the
published core predicate.
-/
theorem complete_or_missing (C : BipartiteCore J) :
    (∀ x ∈ coreVertexSet C C.left,
      ∀ y ∈ coreVertexSet C C.right,
        J.Adj x y) ∨
      Nonempty C.MissingEdgeData := by
  classical
  rcases C.core with
    ⟨hdisjoint, -, -, missing,
      hmissingParts, hmissingSize, hadj⟩
  cases missing with
  | none =>
      left
      intro x hx y hy
      obtain ⟨hxCore, hxLeft⟩ :=
        (mem_coreVertexSet C C.left x).1 hx
      obtain ⟨hyCore, hyRight⟩ :=
        (mem_coreVertexSet C C.right y).1 hy
      exact (hadj ⟨x, hxCore⟩ ⟨y, hyCore⟩).2
        ⟨Or.inl ⟨hxLeft, hyRight⟩, by simp⟩
  | some p =>
      right
      have hpParts := hmissingParts p rfl
      have hlarge := hmissingSize (by simp)
      let xMissing := p.1.1
      let yMissing := p.2.1
      have hxMissing :
          xMissing ∈ coreVertexSet C C.left := by
        exact (mem_coreVertexSet C C.left xMissing).2
          ⟨p.1.2, by simpa [xMissing] using hpParts.1⟩
      have hyMissing :
          yMissing ∈ coreVertexSet C C.right := by
        exact (mem_coreVertexSet C C.right yMissing).2
          ⟨p.2.2, by simpa [yMissing] using hpParts.2⟩
      refine ⟨{
        xMissing := xMissing
        yMissing := yMissing
        x_left := hxMissing
        y_right := hyMissing
        large_side := hlarge
        cross_except_left := ?_
        cross_except := ?_
        missing_not_adjacent := ?_
      }⟩
      · intro x hx y hy hxNe
        obtain ⟨hxCore, hxLeft⟩ :=
          (mem_coreVertexSet C C.left x).1 hx
        obtain ⟨hyCore, hyRight⟩ :=
          (mem_coreVertexSet C C.right y).1 hy
        apply (hadj ⟨x, hxCore⟩ ⟨y, hyCore⟩).2
        refine ⟨Or.inl ⟨hxLeft, hyRight⟩, ?_⟩
        rintro (hforward | hreverse)
        · have hxEq : x = p.1.1 :=
            congrArg Subtype.val hforward.1
          exact hxNe (by
            simpa [xMissing] using hxEq)
        · have hyLeft :
              (⟨y, hyCore⟩ :
                (↑C.carrier : Set W)) ∈ C.left := by
            have hyEq : y = p.1.1 :=
              congrArg Subtype.val hreverse.2
            exact hyEq ▸ hpParts.1
          exact Finset.disjoint_left.mp hdisjoint
            hyLeft hyRight
      · intro x hx y hy hyNe
        obtain ⟨hxCore, hxLeft⟩ :=
          (mem_coreVertexSet C C.left x).1 hx
        obtain ⟨hyCore, hyRight⟩ :=
          (mem_coreVertexSet C C.right y).1 hy
        apply (hadj ⟨x, hxCore⟩ ⟨y, hyCore⟩).2
        refine ⟨Or.inl ⟨hxLeft, hyRight⟩, ?_⟩
        rintro (hforward | hreverse)
        · have hyEq : y = p.2.1 :=
            congrArg Subtype.val hforward.2
          exact hyNe (by
            simpa [yMissing] using hyEq)
        · have hxRight :
              (⟨x, hxCore⟩ :
                (↑C.carrier : Set W)) ∈ C.right := by
            have hxEq : x = p.2.1 :=
              congrArg Subtype.val hreverse.1
            exact hxEq ▸ hpParts.2
          exact Finset.disjoint_left.mp hdisjoint
            hxLeft hxRight
      · intro hmissingAdj
        have hspec :=
          (hadj p.1 p.2).1 hmissingAdj
        apply hspec.2
        exact Or.inl ⟨rfl, rfl⟩

/-- Swap the orientation of explicit missing-edge data. -/
def MissingEdgeData.swap
    {C : BipartiteCore J}
    (M : C.MissingEdgeData) :
    C.swap.MissingEdgeData where
  xMissing := M.yMissing
  yMissing := M.xMissing
  x_left := by
    obtain ⟨hyCore, hyRight⟩ :=
      (mem_coreVertexSet C C.right M.yMissing).1
        M.y_right
    exact (mem_coreVertexSet C.swap C.swap.left
      M.yMissing).2
        ⟨by simpa [BipartiteCore.swap] using hyCore,
          by
            change
              (⟨M.yMissing, _⟩ :
                (↑C.carrier : Set W)) ∈ C.right
            convert hyRight using 1⟩
  y_right := by
    obtain ⟨hxCore, hxLeft⟩ :=
      (mem_coreVertexSet C C.left M.xMissing).1
        M.x_left
    exact (mem_coreVertexSet C.swap C.swap.right
      M.xMissing).2
        ⟨by simpa [BipartiteCore.swap] using hxCore,
          by
            change
              (⟨M.xMissing, _⟩ :
                (↑C.carrier : Set W)) ∈ C.left
            convert hxLeft using 1⟩
  large_side := by
    simpa [BipartiteCore.swap, Nat.max_comm] using
      M.large_side
  cross_except_left := by
    intro x hx y hy hxNe
    have hxOld :
        x ∈ coreVertexSet C C.right := by
      simpa [BipartiteCore.swap, coreVertexSet] using hx
    have hyOld :
        y ∈ coreVertexSet C C.left := by
      simpa [BipartiteCore.swap, coreVertexSet] using hy
    exact (M.cross_except y hyOld x hxOld hxNe).symm
  cross_except := by
    intro x hx y hy hyNe
    have hxOld :
        x ∈ coreVertexSet C C.right := by
      simpa [BipartiteCore.swap, coreVertexSet] using hx
    have hyOld :
        y ∈ coreVertexSet C C.left := by
      simpa [BipartiteCore.swap, coreVertexSet] using hy
    exact (M.cross_except_left y hyOld x hxOld hyNe).symm
  missing_not_adjacent := by
    intro h
    exact M.missing_not_adjacent h.symm

/--
The exact deletion used in the rank-two minimality argument.  When the
left side has size two, deleting the missing endpoint on the right produces
a strictly smaller certified complete bipartite core of rank two.
-/
theorem MissingEdgeData.exists_smaller_complete_core_of_left_card_two
    {C : BipartiteCore J}
    (M : C.MissingEdgeData)
    (hleftCard : C.left.card = 2) :
    ∃ C' : BipartiteCore J,
      C'.rank = 2 ∧
        C'.carrier = C.carrier.erase M.yMissing := by
  classical
  let L := coreVertexSet C C.left
  let R := coreVertexSet C C.right
  let R' := R.erase M.yMissing
  have hLcard : L.card = 2 := by
    simpa [L] using hleftCard
  have hrightTwo : 2 ≤ C.right.card :=
    C.two_le_rank.trans
      (Nat.min_le_right C.left.card C.right.card)
  have hrightThree : 3 ≤ C.right.card := by
    have hlarge := M.large_side
    rw [hleftCard, Nat.max_eq_right hrightTwo] at hlarge
    exact hlarge
  have hyR : M.yMissing ∈ R := by
    simpa [R] using M.y_right
  have hR'card : 2 ≤ R'.card := by
    change 2 ≤ (R.erase M.yMissing).card
    rw [Finset.card_erase_of_mem hyR]
    have hRthree : 3 ≤ R.card := by
      simpa [R] using hrightThree
    omega
  have hLR : Disjoint L R :=
    disjoint_coreVertexSet C C.core.1
  have hyNotL : M.yMissing ∉ L := by
    intro hyL
    exact Finset.disjoint_left.mp hLR hyL hyR
  have hLR' : Disjoint L R' :=
    hLR.mono_right (Finset.erase_subset _ _)
  have hcarrier :
      L ∪ R' = C.carrier.erase M.yMissing := by
    ext z
    rw [Finset.mem_union, Finset.mem_erase,
      ← union_coreVertexSet_sides C]
    simp only [L, R, Finset.mem_union,
      Finset.mem_erase]
    constructor
    · rintro (hzL | ⟨hzy, hzR⟩)
      · exact ⟨fun hzyEq =>
          hyNotL (hzyEq ▸ hzL), Or.inl hzL⟩
      · exact ⟨hzy, Or.inr hzR⟩
    · rintro ⟨hzy, hzL | hzR⟩
      · exact Or.inl hzL
      · exact Or.inr ⟨hzy, hzR⟩
  have hadjSmall :
      ∀ u v : W,
        u ∈ L ∪ R' → v ∈ L ∪ R' →
          (J.Adj u v ↔
            (u ∈ L ∧ v ∈ R') ∨
              (u ∈ R' ∧ v ∈ L)) := by
    intro u v hu hv
    have huC : u ∈ C.carrier := by
      rw [← union_coreVertexSet_sides C]
      rcases Finset.mem_union.mp hu with huL | huR'
      · exact Finset.mem_union_left _ huL
      · exact Finset.mem_union_right _
          (Finset.mem_of_mem_erase huR')
    have hvC : v ∈ C.carrier := by
      rw [← union_coreVertexSet_sides C]
      rcases Finset.mem_union.mp hv with hvL | hvR'
      · exact Finset.mem_union_left _ hvL
      · exact Finset.mem_union_right _
          (Finset.mem_of_mem_erase hvR')
    constructor
    · intro huv
      obtain ⟨missing, -, -, hadjCore⟩ :=
        C.core.2.2.2
      have hcross :=
        ((hadjCore
          (⟨u, huC⟩ : (↑C.carrier : Set W))
          (⟨v, hvC⟩ : (↑C.carrier : Set W))).1 huv).1
      rcases hcross with hcross | hcross
      · left
        have huL :
            u ∈ L :=
          (mem_coreVertexSet C C.left u).2
            ⟨huC, hcross.1⟩
        have hvR :
            v ∈ R :=
          (mem_coreVertexSet C C.right v).2
            ⟨hvC, hcross.2⟩
        refine ⟨huL, ?_⟩
        rcases Finset.mem_union.mp hv with hvL | hvR'
        · exact False.elim
            (Finset.disjoint_left.mp hLR hvL hvR)
        · exact hvR'
      · right
        have huR :
            u ∈ R :=
          (mem_coreVertexSet C C.right u).2
            ⟨huC, hcross.1⟩
        have hvL :
            v ∈ L :=
          (mem_coreVertexSet C C.left v).2
            ⟨hvC, hcross.2⟩
        refine ⟨?_, hvL⟩
        rcases Finset.mem_union.mp hu with huL | huR'
        · exact False.elim
            (Finset.disjoint_left.mp hLR huL huR)
        · exact huR'
    · rintro (⟨huL, hvR'⟩ | ⟨huR', hvL⟩)
      · have hvErase := Finset.mem_erase.mp hvR'
        exact M.cross_except u huL v hvErase.2
          hvErase.1
      · have huErase := Finset.mem_erase.mp huR'
        exact (M.cross_except v hvL u huErase.2
          huErase.1).symm
  let C' :=
    BipartiteCore.ofCompleteRaw J L R'
      hLR' (by omega) hR'card hadjSmall
  refine ⟨C', ?_, ?_⟩
  · dsimp [C', BipartiteCore.rank,
      BipartiteCore.ofCompleteRaw]
    rw [card_rawSide, card_rawSide]
    omega
  · exact hcarrier

end BipartiteCore

/--
The left endpoint set in the one-part branch of Lemma 6.3: vertices with at
least two represented neighbors expose all of them at both roots; otherwise
only the prescribed left part is exposed.
-/
noncomputable def adaptiveLeftBoundaryEnds
    (J : SimpleGraph W) (Q T T₁ : Finset W)
    (w : (↑Q : Set W)) : Finset W :=
  if 2 ≤ (boundaryEndsIn J Q T w).card then
    boundaryEndsIn J Q T w
  else
    boundaryEndsIn J Q T₁ w

/-- Right-hand analogue of `adaptiveLeftBoundaryEnds`. -/
noncomputable def adaptiveRightBoundaryEnds
    (J : SimpleGraph W) (Q T T₂ : Finset W)
    (w : (↑Q : Set W)) : Finset W :=
  if 2 ≤ (boundaryEndsIn J Q T w).card then
    boundaryEndsIn J Q T w
  else
    boundaryEndsIn J Q T₂ w

theorem adaptive_boundary_ends_distinct
    (J : SimpleGraph W) (Q T T₁ T₂ : Finset W)
    (hdisj : Disjoint T₁ T₂)
    (u v : (↑Q : Set W))
    (hu :
      (adaptiveLeftBoundaryEnds J Q T T₁ u).Nonempty)
    (hv :
      (adaptiveRightBoundaryEnds J Q T T₂ v).Nonempty) :
    ∃ x ∈ adaptiveLeftBoundaryEnds J Q T T₁ u,
      ∃ y ∈ adaptiveRightBoundaryEnds J Q T T₂ v,
        x ≠ y := by
  classical
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := hv
  by_cases hxy : x ≠ y
  · exact ⟨x, hx, y, hy, hxy⟩
  · have hxyEq : x = y := by
      exact Classical.not_not.mp hxy
    subst y
    by_cases huLarge :
        2 ≤ (boundaryEndsIn J Q T u).card
    · have hxAll :
          x ∈ boundaryEndsIn J Q T u := by
        simpa [adaptiveLeftBoundaryEnds, huLarge] using hx
      obtain ⟨a, ha, b, hb, hab⟩ :=
        Finset.one_lt_card.mp (by omega : 1 <
          (boundaryEndsIn J Q T u).card)
      by_cases hax : a ≠ x
      · exact ⟨a, by
          simpa [adaptiveLeftBoundaryEnds, huLarge] using ha,
          x, hy, hax⟩
      · have haxEq : a = x :=
          Classical.not_not.mp hax
        have hbx : b ≠ x := by
          intro hbx
          exact hab (haxEq.trans hbx.symm)
        exact ⟨b, by
          simpa [adaptiveLeftBoundaryEnds, huLarge] using hb,
          x, hy, hbx⟩
    · by_cases hvLarge :
          2 ≤ (boundaryEndsIn J Q T v).card
      · obtain ⟨a, ha, b, hb, hab⟩ :=
          Finset.one_lt_card.mp (by omega : 1 <
            (boundaryEndsIn J Q T v).card)
        by_cases hax : a ≠ x
        · exact ⟨x, hx, a, by
            simpa [adaptiveRightBoundaryEnds, hvLarge] using ha,
            hax.symm⟩
        · have haxEq : a = x :=
            Classical.not_not.mp hax
          have hbx : b ≠ x := by
            intro hbx
            exact hab (haxEq.trans hbx.symm)
          exact ⟨x, hx, b, by
            simpa [adaptiveRightBoundaryEnds, hvLarge] using hb,
            hbx.symm⟩
      · have hxT₁ : x ∈ T₁ := by
          have :=
            (mem_boundaryEndsIn J Q T₁ u x).1
              (by
                simpa [adaptiveLeftBoundaryEnds, huLarge] using hx)
          exact this.1
        have hxT₂ : x ∈ T₂ := by
          have :=
            (mem_boundaryEndsIn J Q T₂ v x).1
              (by
                simpa [adaptiveRightBoundaryEnds, hvLarge] using hy)
          exact this.1
        exact False.elim
          (Finset.disjoint_left.mp hdisj hxT₁ hxT₂)

namespace BipartiteCore

/-- In a complete core, a left vertex has exactly all right vertices as its
neighbors inside the carrier. -/
theorem finiteBoundaryDegree_eq_right_card_of_complete
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (C : BipartiteCore J)
    (hcomplete :
      ∀ x ∈ coreVertexSet C C.left,
        ∀ y ∈ coreVertexSet C C.right,
          J.Adj x y)
    (x : W) (hx : x ∈ coreVertexSet C C.left) :
    finiteBoundaryDegree J C.carrier x =
      C.right.card := by
  classical
  let R := coreVertexSet C C.right
  obtain ⟨hxCore, hxLeft⟩ :=
    (mem_coreVertexSet C C.left x).1 hx
  have hset :
      J.neighborSet x ∩ (↑C.carrier : Set W) =
        (↑R : Set W) := by
    ext z
    constructor
    · rintro ⟨hxz, hzCore⟩
      obtain ⟨missing, -, -, hadjCore⟩ :=
        C.core.2.2.2
      have hcross :=
        ((hadjCore
          (⟨x, hxCore⟩ :
            (↑C.carrier : Set W))
          (⟨z, hzCore⟩ :
            (↑C.carrier : Set W))).1 hxz).1
      rcases hcross with hcross | hcross
      · exact (mem_coreVertexSet C C.right z).2
          ⟨hzCore, hcross.2⟩
      · exact False.elim
          (Finset.disjoint_left.mp C.core.1
            hxLeft hcross.1)
    · intro hzR
      have hzR' : z ∈ coreVertexSet C C.right := by
        simpa [R] using hzR
      exact ⟨hcomplete x hx z hzR',
        ((mem_coreVertexSet C C.right z).1
          hzR').choose⟩
  unfold finiteBoundaryDegree
  rw [hset, Set.ncard_coe_finset]
  exact card_coreVertexSet C C.right

/-- Symmetric complete-core degree formula for a right vertex. -/
theorem finiteBoundaryDegree_eq_left_card_of_complete
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (C : BipartiteCore J)
    (hcomplete :
      ∀ x ∈ coreVertexSet C C.left,
        ∀ y ∈ coreVertexSet C C.right,
          J.Adj x y)
    (y : W) (hy : y ∈ coreVertexSet C C.right) :
    finiteBoundaryDegree J C.carrier y =
      C.left.card := by
  classical
  let L := coreVertexSet C C.left
  obtain ⟨hyCore, hyRight⟩ :=
    (mem_coreVertexSet C C.right y).1 hy
  have hset :
      J.neighborSet y ∩ (↑C.carrier : Set W) =
        (↑L : Set W) := by
    ext z
    constructor
    · rintro ⟨hyz, hzCore⟩
      obtain ⟨missing, -, -, hadjCore⟩ :=
        C.core.2.2.2
      have hcross :=
        ((hadjCore
          (⟨y, hyCore⟩ :
            (↑C.carrier : Set W))
          (⟨z, hzCore⟩ :
            (↑C.carrier : Set W))).1 hyz).1
      rcases hcross with hcross | hcross
      · exact False.elim
          (Finset.disjoint_left.mp C.core.1
            hcross.1 hyRight)
      · exact (mem_coreVertexSet C C.left z).2
          ⟨hzCore, hcross.2⟩
    · intro hzL
      have hzL' : z ∈ coreVertexSet C C.left := by
        simpa [L] using hzL
      exact ⟨(hcomplete z hzL' y hy).symm,
        ((mem_coreVertexSet C C.left z).1
          hzL').choose⟩
  unfold finiteBoundaryDegree
  rw [hset, Set.ncard_coe_finset]
  exact card_coreVertexSet C C.left

/-- The missing right endpoint has exactly `left.card - 1` core neighbors. -/
theorem MissingEdgeData.finiteBoundaryDegree_missing_right
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {C : BipartiteCore J}
    (M : C.MissingEdgeData) :
    finiteBoundaryDegree J C.carrier M.yMissing =
      C.left.card - 1 := by
  classical
  let L := coreVertexSet C C.left
  obtain ⟨hyCore, hyRight⟩ :=
    (mem_coreVertexSet C C.right M.yMissing).1
      M.y_right
  have hxL : M.xMissing ∈ L := by
    simpa [L] using M.x_left
  have hset :
      J.neighborSet M.yMissing ∩
          (↑C.carrier : Set W) =
        (↑(L.erase M.xMissing) : Set W) := by
    ext z
    constructor
    · rintro ⟨hyz, hzCore⟩
      obtain ⟨missing, -, -, hadjCore⟩ :=
        C.core.2.2.2
      have hcross :=
        ((hadjCore
          (⟨M.yMissing, hyCore⟩ :
            (↑C.carrier : Set W))
          (⟨z, hzCore⟩ :
            (↑C.carrier : Set W))).1 hyz).1
      rcases hcross with hcross | hcross
      · exact False.elim
          (Finset.disjoint_left.mp C.core.1
            hcross.1 hyRight)
      · refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro hzx
          subst z
          exact M.missing_not_adjacent hyz.symm
        · exact (mem_coreVertexSet C C.left z).2
            ⟨hzCore, hcross.2⟩
    · intro hz
      have hz' := Finset.mem_erase.mp hz
      exact ⟨(M.cross_except_left z hz'.2
        M.yMissing M.y_right hz'.1).symm,
        ((mem_coreVertexSet C C.left z).1
          hz'.2).choose⟩
  unfold finiteBoundaryDegree
  rw [hset, Set.ncard_coe_finset,
    Finset.card_erase_of_mem hxL,
    card_coreVertexSet]

/--
In the rank-two deletion step, the removed missing endpoint has at most one
neighbor in the remaining core.  This verifies the non-obvious new outside
vertex required by the preserved outside-neighbor bound.
-/
theorem MissingEdgeData.deleted_endpoint_boundary_degree_le_one
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {C : BipartiteCore J}
    (M : C.MissingEdgeData)
    (hleftCard : C.left.card = 2) :
    finiteBoundaryDegree J
      (C.carrier.erase M.yMissing) M.yMissing ≤ 1 := by
  classical
  let L := coreVertexSet C C.left
  obtain ⟨hyCore, hyRight⟩ :=
    (mem_coreVertexSet C C.right M.yMissing).1
      M.y_right
  have hsub :
      J.neighborSet M.yMissing ∩
          (↑(C.carrier.erase M.yMissing) : Set W) ⊆
        (↑(L.erase M.xMissing) : Set W) := by
    intro z hz
    have hzCore : z ∈ C.carrier :=
      Finset.mem_of_mem_erase hz.2
    obtain ⟨missing, -, -, hadjCore⟩ :=
      C.core.2.2.2
    have hcross :=
      ((hadjCore
        (⟨M.yMissing, hyCore⟩ :
          (↑C.carrier : Set W))
        (⟨z, hzCore⟩ :
          (↑C.carrier : Set W))).1 hz.1).1
    rcases hcross with hcross | hcross
    · exact False.elim
        (Finset.disjoint_left.mp C.core.1
          hcross.1 hyRight)
    · have hzL : z ∈ L :=
        (mem_coreVertexSet C C.left z).2
          ⟨hzCore, hcross.2⟩
      refine Finset.mem_erase.mpr ⟨?_, hzL⟩
      intro hzx
      subst z
      exact M.missing_not_adjacent hz.1.symm
  unfold finiteBoundaryDegree
  calc
    (J.neighborSet M.yMissing ∩
        (↑(C.carrier.erase M.yMissing) : Set W)).ncard
        ≤ (↑(L.erase M.xMissing) : Set W).ncard :=
      Set.ncard_le_ncard hsub
    _ = (L.erase M.xMissing).card :=
      Set.ncard_coe_finset _
    _ = 1 := by
      have hxL : M.xMissing ∈ L := by
        simpa [L] using M.x_left
      rw [Finset.card_erase_of_mem hxL]
      have hLcard : L.card = 2 := by
        simpa [L] using hleftCard
      omega

/--
Deleting the missing endpoint preserves the rank-two outside-neighbor bound
and strictly decreases the carrier.  This is the complete formal content of
the paper's “same outside-neighbor bound” assertion in the oriented
case.
-/
theorem MissingEdgeData.exists_smaller_bounded_core_of_left_card_two
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {C : BipartiteCore J}
    (M : C.MissingEdgeData)
    (hleftCard : C.left.card = 2)
    (houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤ 1) :
    ∃ C' : BipartiteCore J,
      C'.rank = 2 ∧
        C'.carrier.card < C.carrier.card ∧
        ∀ w, w ∉ C'.carrier →
          finiteBoundaryDegree J C'.carrier w ≤ 1 := by
  classical
  obtain ⟨C', hrank, hcarrier⟩ :=
    M.exists_smaller_complete_core_of_left_card_two
      hleftCard
  have hyCore : M.yMissing ∈ C.carrier :=
    ((mem_coreVertexSet C C.right
      M.yMissing).1 M.y_right).choose
  have hcard :
      C'.carrier.card < C.carrier.card := by
    rw [hcarrier,
      Finset.card_erase_of_mem hyCore]
    have hpositive : 0 < C.carrier.card :=
      Finset.card_pos.mpr ⟨M.yMissing, hyCore⟩
    omega
  refine ⟨C', hrank, hcard, ?_⟩
  intro w hw
  rw [hcarrier]
  by_cases hwy : w = M.yMissing
  · subst w
    exact M.deleted_endpoint_boundary_degree_le_one
      hleftCard
  · have hwOld : w ∉ C.carrier := by
      intro hwCore
      apply hw
      rw [hcarrier]
      exact Finset.mem_erase.mpr ⟨hwy, hwCore⟩
    exact (finiteBoundaryDegree_mono J
      (Finset.erase_subset _ _) w).trans
        (houtside w hwOld)

/--
Orientation-free rank-two deletion.  The smaller side is detected from the
definition of `rank`; if it is the right side, both the core and the
missing-edge certificate are swapped first.
-/
theorem MissingEdgeData.exists_smaller_bounded_core_of_rank_two
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} {C : BipartiteCore J}
    (M : C.MissingEdgeData)
    (hrank : C.rank = 2)
    (houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤ 1) :
    ∃ C' : BipartiteCore J,
      C'.rank = 2 ∧
        C'.carrier.card < C.carrier.card ∧
        ∀ w, w ∉ C'.carrier →
          finiteBoundaryDegree J C'.carrier w ≤ 1 := by
  classical
  by_cases hle : C.left.card ≤ C.right.card
  · have hleftCard : C.left.card = 2 := by
      rw [BipartiteCore.rank,
        Nat.min_eq_left hle] at hrank
      exact hrank
    exact M.exists_smaller_bounded_core_of_left_card_two
      hleftCard houtside
  · have hrightLe : C.right.card ≤ C.left.card :=
      Nat.le_of_not_ge hle
    have hrightCard : C.right.card = 2 := by
      rw [BipartiteCore.rank,
        Nat.min_eq_right hrightLe] at hrank
      exact hrank
    have houtsideSwap :
        ∀ w, w ∉ C.swap.carrier →
          finiteBoundaryDegree J C.swap.carrier w ≤ 1 := by
      simpa [BipartiteCore.swap] using houtside
    obtain ⟨C', hC'rank, hC'card, hC'outside⟩ :=
      M.swap.exists_smaller_bounded_core_of_left_card_two
        (by
          simpa [BipartiteCore.swap] using hrightCard)
        houtsideSwap
    exact ⟨C', hC'rank,
      by simpa [BipartiteCore.swap] using hC'card,
      hC'outside⟩

/--
Minimality rules out a genuine missing edge at rank two.  The conclusion is
the exact completeness statement consumed by the component theorem.
-/
theorem rank_two_complete_of_minimal
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} (C : BipartiteCore J)
    (hrank : C.rank = 2)
    (houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1)
    (hminimal :
      ∀ C' : BipartiteCore J,
        (∀ w, w ∉ C'.carrier →
          finiteBoundaryDegree J C'.carrier w ≤
            C'.rank - 1) →
        C.carrier.card ≤ C'.carrier.card) :
    ∀ x ∈ coreVertexSet C C.left,
      ∀ y ∈ coreVertexSet C C.right,
        J.Adj x y := by
  classical
  rcases C.complete_or_missing with hcomplete | hmissing
  · exact hcomplete
  · let M : C.MissingEdgeData :=
      Classical.choice hmissing
    have houtsideOne :
        ∀ w, w ∉ C.carrier →
          finiteBoundaryDegree J C.carrier w ≤ 1 := by
      intro w hw
      simpa [hrank] using houtside w hw
    obtain ⟨C', hC'rank, hC'card, hC'outside⟩ :=
      M.exists_smaller_bounded_core_of_rank_two
        hrank houtsideOne
    have hminimal' : C.carrier.card ≤ C'.carrier.card :=
      hminimal C' (by
        intro w hw
        simpa [hC'rank] using hC'outside w hw)
    omega

/-- Select a minimum-order bounded core by well-ordering its carrier size. -/
theorem exists_minimal_bounded_core
    [Fintype W] [DecidableEq W]
    {J : SimpleGraph W}
    (C₀ : BipartiteCore J)
    (hC₀ :
      ∀ w, w ∉ C₀.carrier →
        finiteBoundaryDegree J C₀.carrier w ≤
          C₀.rank - 1) :
    ∃ C : BipartiteCore J,
      (∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1) ∧
      ∀ C' : BipartiteCore J,
        (∀ w, w ∉ C'.carrier →
          finiteBoundaryDegree J C'.carrier w ≤
            C'.rank - 1) →
        C.carrier.card ≤ C'.carrier.card := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ C : BipartiteCore J,
      (∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1) ∧
      C.carrier.card = n
  have hex : ∃ n, P n :=
    ⟨C₀.carrier.card, C₀, hC₀, rfl⟩
  obtain ⟨C, hC, hCcard⟩ :=
    Nat.find_spec hex
  refine ⟨C, hC, ?_⟩
  intro C' hC'
  have hP' : P C'.carrier.card :=
    ⟨C', hC', rfl⟩
  have hmin :=
    Nat.find_min' hex hP'
  rw [hCcard]
  exact hmin

end BipartiteCore

/--
The singleton-component exclusion at the start of Lemma 6.3.  Minimum
degree four and at most three core neighbors force every outside component
to contain at least two old vertices.
-/
theorem ComponentRegion.two_le_card_of_min_degree_four
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q : Finset W)
    (hQ : ComponentRegion J S Q)
    (hdegree : ∀ w ∈ Q, 4 ≤ finiteDegree J w)
    (hboundary :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J S w.1 ≤ 3) :
    2 ≤ Q.card := by
  by_contra hnot
  have hcard : Q.card = 1 := by
    have hpos := Finset.card_pos.mpr hQ.nonempty
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  subst Q
  let w : (↑({a} : Finset W) : Set W) :=
    ⟨a, by simp⟩
  have hpartition :=
    finiteDegree_le_induced_region_add_boundary
      J S {a} (by simpa using hQ) w
  have hinduced :
      finiteDegree
        (J.induce (↑({a} : Finset W) : Set W)) w = 0 := by
    unfold finiteDegree
    have hneighbors :
        (J.induce (↑({a} : Finset W) : Set W)).neighborSet w =
          ∅ := by
      ext z
      constructor
      · intro hwz
        have hzw : z = w := by
          exact Subtype.ext (by
            simpa [w] using z.2)
        subst z
        exact False.elim
          ((J.induce
            (↑({a} : Finset W) : Set W)).loopless.irrefl w hwz)
      · simp
    rw [hneighbors]
    simp
  have hambient : 4 ≤ finiteDegree J w.1 := by
    simpa [w] using hdegree a (by simp)
  have hboundary' :
      finiteBoundaryDegree J S w.1 ≤ 3 :=
    hboundary w
  rw [hinduced] at hpartition
  omega

/--
The exact numerical degree loss in (6.4), including the `r = 2` case.
At least one boundary edge replaces the lost core edges.
-/
theorem boundaryAux_degree_bound_one_root
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q : Finset W)
    (hQ : ComponentRegion J S Q)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (w : (↑Q : Set W)) (r : ℕ)
    (hrlo : 2 ≤ r) (hrhi : r ≤ 4)
    (hcore :
      finiteBoundaryDegree J S w.1 ≤ r - 1)
    (hattached :
      1 ≤ finiteBoundaryDegree J S w.1 →
        (leftEnds w).Nonempty ∨
          (rightEnds w).Nonempty) :
    (5 ≤ finiteDegree J w.1 →
      7 - r ≤
        finiteDegree
          (boundaryAuxGraph J Q leftEnds rightEnds)
          (boundaryOldVertex Q w)) ∧
    (4 ≤ finiteDegree J w.1 →
      6 - r ≤
        finiteDegree
          (boundaryAuxGraph J Q leftEnds rightEnds)
          (boundaryOldVertex Q w)) := by
  by_cases hzero :
      finiteBoundaryDegree J S w.1 = 0
  · have hbook :=
      ambientDegree_add_le_auxDegree_add_boundary
        J S Q hQ leftEnds rightEnds w 0 (by omega)
    constructor <;> intro hdegree <;> omega
  · have hpositive :
        1 ≤ finiteBoundaryDegree J S w.1 := by omega
    have hrootCount :
        1 ≤ (if (leftEnds w).Nonempty then 1 else 0) +
          (if (rightEnds w).Nonempty then 1 else 0) := by
      rcases hattached hpositive with hleft | hright
      · simp [hleft]
      · simp [hright]
    have hbook :=
      ambientDegree_add_le_auxDegree_add_boundary
        J S Q hQ leftEnds rightEnds w 1 hrootCount
    constructor <;> intro hdegree <;> omega

/--
The missing-edge variant of (6.4).  A vertex with two or more core
neighbors has a represented root edge.  If no root edge is present, the
only possible lost core edge is the single unrepresented missing-edge
endpoint; `r ≥ 3` makes that loss no worse than `r - 2`.
-/
theorem boundaryAux_degree_bound_missing_endpoint
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q : Finset W)
    (hQ : ComponentRegion J S Q)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (w : (↑Q : Set W)) (r : ℕ)
    (hrlo : 3 ≤ r) (hrhi : r ≤ 4)
    (hcore :
      finiteBoundaryDegree J S w.1 ≤ r - 1)
    (hattached :
      2 ≤ finiteBoundaryDegree J S w.1 →
        (leftEnds w).Nonempty ∨
          (rightEnds w).Nonempty) :
    (5 ≤ finiteDegree J w.1 →
      7 - r ≤
        finiteDegree
          (boundaryAuxGraph J Q leftEnds rightEnds)
          (boundaryOldVertex Q w)) ∧
    (4 ≤ finiteDegree J w.1 →
      6 - r ≤
        finiteDegree
          (boundaryAuxGraph J Q leftEnds rightEnds)
          (boundaryOldVertex Q w)) := by
  by_cases hsmall :
      finiteBoundaryDegree J S w.1 ≤ 1
  · have hbook :=
      ambientDegree_add_le_auxDegree_add_boundary
        J S Q hQ leftEnds rightEnds w 0 (by omega)
    constructor <;> intro hdegree <;> omega
  · have hlarge :
        2 ≤ finiteBoundaryDegree J S w.1 := by omega
    have hrootCount :
        1 ≤ (if (leftEnds w).Nonempty then 1 else 0) +
          (if (rightEnds w).Nonempty then 1 else 0) := by
      rcases hattached hlarge with hleft | hright
      · simp [hleft]
      · simp [hright]
    have hbook :=
      ambientDegree_add_le_auxDegree_add_boundary
        J S Q hQ leftEnds rightEnds w 1 hrootCount
    constructor <;> intro hdegree <;> omega

/--
The exact numerical degree loss in (6.5).  When there is at most one core
neighbor every lost edge is replaced; when there are at least two, both
root edges are present.
-/
theorem boundaryAux_degree_bound_two_roots
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (S Q : Finset W)
    (hQ : ComponentRegion J S Q)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (w : (↑Q : Set W)) (r : ℕ)
    (hrlo : 3 ≤ r) (hrhi : r ≤ 4)
    (hcore :
      finiteBoundaryDegree J S w.1 ≤ r - 1)
    (hreplaceSmall :
      finiteBoundaryDegree J S w.1 ≤ 1 →
        finiteBoundaryDegree J S w.1 ≤
          (if (leftEnds w).Nonempty then 1 else 0) +
            (if (rightEnds w).Nonempty then 1 else 0))
    (hbothLarge :
      2 ≤ finiteBoundaryDegree J S w.1 →
        (leftEnds w).Nonempty ∧ (rightEnds w).Nonempty) :
    (5 ≤ finiteDegree J w.1 →
      8 - r ≤
        finiteDegree
          (boundaryAuxGraph J Q leftEnds rightEnds)
          (boundaryOldVertex Q w)) ∧
    (4 ≤ finiteDegree J w.1 →
      7 - r ≤
        finiteDegree
          (boundaryAuxGraph J Q leftEnds rightEnds)
          (boundaryOldVertex Q w)) := by
  by_cases hsmall : finiteBoundaryDegree J S w.1 ≤ 1
  · have hbook :=
      ambientDegree_add_le_auxDegree_add_boundary
        J S Q hQ leftEnds rightEnds w
        (finiteBoundaryDegree J S w.1)
        (hreplaceSmall hsmall)
    constructor <;> intro hdegree <;> omega
  · have hlarge :
        2 ≤ finiteBoundaryDegree J S w.1 := by omega
    obtain ⟨hleft, hright⟩ := hbothLarge hlarge
    have hrootCount :
        2 ≤ (if (leftEnds w).Nonempty then 1 else 0) +
          (if (rightEnds w).Nonempty then 1 else 0) := by
      simp [hleft, hright]
    have hbook :=
      ambientDegree_add_le_auxDegree_add_boundary
        J S Q hQ leftEnds rightEnds w 2 hrootCount
    constructor <;> intro hdegree <;> omega

/-- A raw complete bipartite pair with independently specified side sizes. -/
def HasCompletePairSizes
    (J : SimpleGraph W) (s t : ℕ) : Prop :=
  ∃ L R : Finset W,
    L.card = s ∧
    R.card = t ∧
    Disjoint L R ∧
    ∀ x ∈ L, ∀ y ∈ R, J.Adj x y

/-- A balanced raw complete bipartite pair. -/
def HasCompletePairSize
    (J : SimpleGraph W) (s : ℕ) : Prop :=
  HasCompletePairSizes J s s

/--
A balanced raw bipartite pair in which one designated cross-edge is
allowed to be absent.
-/
def HasAlmostCompletePairSize
    (J : SimpleGraph W) (s : ℕ) : Prop :=
  ∃ (L R : Finset W) (xMissing yMissing : W),
    L.card = s ∧
    R.card = s ∧
    Disjoint L R ∧
    xMissing ∈ L ∧
    yMissing ∈ R ∧
    ∀ x ∈ L, ∀ y ∈ R,
      x ≠ xMissing ∨ y ≠ yMissing →
        J.Adj x y

/-- Complete right sides of a fixed raw left side. -/
def HasCompleteRightSide
    (J : SimpleGraph W) (L : Finset W) (t : ℕ) : Prop :=
  ∃ R : Finset W,
    R.card = t ∧
    Disjoint L R ∧
    ∀ x ∈ L, ∀ y ∈ R, J.Adj x y

/--
An actual simple four-cycle supplies two disjoint two-vertex sides with
all four cross-edges.  Injectivity of the cycle copy certifies that none of
the four vertices is accidentally reused.
-/
theorem four_cycle_has_complete_pair_size_two
    {J : SimpleGraph W}
    (hcycle : HasCycleLength J 4) :
    HasCompletePairSize J 2 := by
  classical
  obtain ⟨C, hClength⟩ := hcycle
  have hcontained :
      cycleGraph 4 ⊑ J :=
    (cycleGraph_isContained_iff (n := 4)
      (by omega)).2
      ⟨C.base, C.walk, C.isCycle, hClength⟩
  obtain ⟨K⟩ := hcontained
  refine ⟨{K (0 : Fin 4), K (2 : Fin 4)},
    {K (1 : Fin 4), K (3 : Fin 4)}, ?_, ?_,
    ?_, ?_⟩
  · exact Finset.card_pair
      (K.injective.ne (by decide))
  · exact Finset.card_pair
      (K.injective.ne (by decide))
  · apply Finset.disjoint_left.mpr
    intro x hxL hxR
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hxL hxR
    rcases hxL with rfl | rfl
    · rcases hxR with h | h
      · exact K.injective.ne (by decide) h
      · exact K.injective.ne (by decide) h
    · rcases hxR with h | h
      · exact K.injective.ne (by decide) h
      · exact K.injective.ne (by decide) h
  · intro x hxL y hyR
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hxL hyR
    rcases hxL with rfl | rfl <;>
      rcases hyR with rfl | rfl <;>
      apply K.toHom.map_adj <;>
      decide

/-- Every side size of a raw complete bipartite pair is bounded by order. -/
theorem complete_pair_size_le_card
    [Fintype W]
    {J : SimpleGraph W} {s : ℕ}
    (hpair : HasCompletePairSize J s) :
    s ≤ Fintype.card W := by
  obtain ⟨L, R, hLcard, -, -, -⟩ := hpair
  calc
    s = L.card := hLcard.symm
    _ ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ L)
    _ = Fintype.card W := Finset.card_univ

/--
Finite order selects a genuinely maximal balanced complete bipartite
side size, retaining an explicit witnessing pair.
-/
theorem exists_maximal_complete_pair_size
    [Fintype W]
    {J : SimpleGraph W}
    (hpair : HasCompletePairSize J 2) :
    ∃ s : ℕ,
      HasCompletePairSize J s ∧
      2 ≤ s ∧
      ∀ t, s < t → ¬HasCompletePairSize J t := by
  classical
  let P : ℕ → Prop := HasCompletePairSize J
  let s := Nat.findGreatest P (Fintype.card W)
  have htwoBound :
      2 ≤ Fintype.card W :=
    complete_pair_size_le_card hpair
  have hsPair : P s :=
    Nat.findGreatest_spec htwoBound hpair
  have htwoS : 2 ≤ s := by
    by_contra hlt
    have hslt : s < 2 := by omega
    exact Nat.findGreatest_is_greatest
      (P := P) hslt htwoBound hpair
  refine ⟨s, hsPair, htwoS, ?_⟩
  intro t hst htPair
  have htBound :
      t ≤ Fintype.card W :=
    complete_pair_size_le_card htPair
  exact Nat.findGreatest_is_greatest
    (P := P) hst htBound htPair

/-- Every complete right side of a fixed left side is bounded by order. -/
theorem complete_right_side_size_le_card
    [Fintype W]
    {J : SimpleGraph W} {L : Finset W} {t : ℕ}
    (hside : HasCompleteRightSide J L t) :
    t ≤ Fintype.card W := by
  obtain ⟨R, hRcard, -, -⟩ := hside
  calc
    t = R.card := hRcard.symm
    _ ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ R)
    _ = Fintype.card W := Finset.card_univ

/--
For a fixed left side, finite order selects a maximum complete right
side, again retaining a witness.
-/
theorem exists_maximal_complete_right_side
    [Fintype W]
    {J : SimpleGraph W} (L R₀ : Finset W)
    {t₀ : ℕ}
    (hR₀card : R₀.card = t₀)
    (hLR₀ : Disjoint L R₀)
    (hcross₀ :
      ∀ x ∈ L, ∀ y ∈ R₀, J.Adj x y) :
    ∃ t R,
      R.card = t ∧
      Disjoint L R ∧
      (∀ x ∈ L, ∀ y ∈ R, J.Adj x y) ∧
      t₀ ≤ t ∧
      ∀ E : Finset W,
        t < E.card →
        Disjoint L E →
        (∀ x ∈ L, ∀ y ∈ E, J.Adj x y) →
        False := by
  classical
  let P : ℕ → Prop :=
    HasCompleteRightSide J L
  let t := Nat.findGreatest P (Fintype.card W)
  have ht₀ : P t₀ :=
    ⟨R₀, hR₀card, hLR₀, hcross₀⟩
  have ht₀Bound :
      t₀ ≤ Fintype.card W :=
    complete_right_side_size_le_card ht₀
  have htSide : P t :=
    Nat.findGreatest_spec ht₀Bound ht₀
  obtain ⟨R, hRcard, hLR, hcross⟩ := htSide
  have ht₀t : t₀ ≤ t := by
    by_contra hlt
    have htt₀ : t < t₀ := by omega
    exact Nat.findGreatest_is_greatest
      (P := P) htt₀ ht₀Bound ht₀
  refine ⟨t, R, hRcard, hLR, hcross,
    ht₀t, ?_⟩
  intro E htE hLE hcrossE
  have hEside : P E.card :=
    ⟨E, rfl, hLE, hcrossE⟩
  have hEbound :
      E.card ≤ Fintype.card W :=
    complete_right_side_size_le_card hEside
  exact Nat.findGreatest_is_greatest
    (P := P) htE hEbound hEside

namespace StandingSetup

variable [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V]
    {J : SimpleGraph W} {B : SimpleGraph V}
    {c : V} {D : Finset W}

/--
Triangle-freeness makes opposite-side attachment edges independent at their
old endpoints: one component vertex cannot meet two adjacent core vertices.
-/
theorem opposite_attachment_old_vertices_ne
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (qLeft qRight : (↑Q : Set W))
    (x y : W)
    (hxCore : x ∈ C.carrier)
    (hyCore : y ∈ C.carrier)
    (hxy : J.Adj x y)
    (hqx : J.Adj qLeft.1 x)
    (hqy : J.Adj qRight.1 y) :
    qLeft ≠ qRight := by
  intro hroots
  apply setup.no_triangle
  refine ⟨{
    p := qLeft.1
    q := x
    r := y
    p_ne_q := ?_
    p_ne_r := ?_
    q_ne_r := hxy.ne
    pq := hqx
    qr := hxy
    rp := ?_
  }⟩
  · intro h
    exact hregion.not_mem_separator qLeft.2
      (h ▸ hxCore)
  · intro h
    exact hregion.not_mem_separator qLeft.2
      (h ▸ hyCore)
  · have hq :
        J.Adj qLeft.1 y := by
      simpa [hroots] using hqy
    exact hq.symm

/-- Map the old part of a boundary auxiliary graph into the ambient block. -/
def boundaryAuxOldHom
    (setup : StandingSetup J B c D)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W) :
    (boundaryAuxGraph J Q leftEnds rightEnds).induce
      {z | z ≠ boundaryLeftRoot Q ∧
        z ≠ boundaryRightRoot Q} →g B where
  toFun z := setup.inclusion (boundaryInteriorOld Q z).1
  map_rel' := by
    intro u v huv
    apply setup.inclusion.toHom.map_rel'
    have hu := boundaryOldVertex_interior Q u
    have hv := boundaryOldVertex_interior Q v
    change
      (boundaryAuxGraph J Q leftEnds rightEnds).Adj
        u.1 v.1 at huv
    rw [← hu, ← hv] at huv
    exact huv

theorem boundaryAuxOldHom_injective
    (setup : StandingSetup J B c D)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W) :
    Function.Injective
      (setup.boundaryAuxOldHom Q leftEnds rightEnds) := by
  intro u v huv
  have hold :
      boundaryInteriorOld Q u =
        boundaryInteriorOld Q v := by
    apply Subtype.ext
    exact setup.inclusion.injective huv
  apply Subtype.ext
  rw [← boundaryOldVertex_interior Q u,
    ← boundaryOldVertex_interior Q v, hold]

/-- The vertex embedding underlying the standing graph embedding. -/
def vertexEmbedding
    (setup : StandingSetup J B c D) : W ↪ V where
  toFun := setup.inclusion
  inj' := setup.inclusion.injective

/-- Map one represented core-end set from `J` into the ambient block `B`. -/
def mappedBoundaryEnds
    (setup : StandingSetup J B c D)
    (Q : Finset W)
    (ends : (↑Q : Set W) → Finset W)
    (z : {u : BoundaryAuxVertex Q //
      u ≠ boundaryLeftRoot Q ∧
        u ≠ boundaryRightRoot Q}) :
    Finset V :=
  (ends (boundaryInteriorOld Q z)).map setup.vertexEmbedding

@[simp] theorem mem_mappedBoundaryEnds
    (setup : StandingSetup J B c D)
    (Q : Finset W)
    (ends : (↑Q : Set W) → Finset W)
    (z : {u : BoundaryAuxVertex Q //
      u ≠ boundaryLeftRoot Q ∧
        u ≠ boundaryRightRoot Q})
    (x : V) :
    x ∈ setup.mappedBoundaryEnds Q ends z ↔
      ∃ y ∈ ends (boundaryInteriorOld Q z),
        setup.inclusion y = x := by
  simp [mappedBoundaryEnds, vertexEmbedding]

/-- Recover the core vertex represented by one mapped ambient endpoint. -/
noncomputable def coreVertexOfMappedEnds
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (ends : (↑Q : Set W) → Finset W)
    (hin : ∀ w x, x ∈ ends w → x ∈ C.carrier)
    (z : {u : BoundaryAuxVertex Q //
      u ≠ boundaryLeftRoot Q ∧
        u ≠ boundaryRightRoot Q})
    (x : {x : V // x ∈ setup.mappedBoundaryEnds Q ends z}) :
    (↑C.carrier : Set W) :=
  let hex :=
    (setup.mem_mappedBoundaryEnds Q ends z x.1).1 x.2
  ⟨Classical.choose hex,
    hin _ _ (Classical.choose_spec hex).1⟩

theorem coreVertexOfMappedEnds_mem
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (ends : (↑Q : Set W) → Finset W)
    (hin : ∀ w x, x ∈ ends w → x ∈ C.carrier)
    (z : {u : BoundaryAuxVertex Q //
      u ≠ boundaryLeftRoot Q ∧
        u ≠ boundaryRightRoot Q})
    (x : {x : V // x ∈ setup.mappedBoundaryEnds Q ends z}) :
    (coreVertexOfMappedEnds setup C Q ends hin z x).1 ∈
      ends (boundaryInteriorOld Q z) := by
  exact (Classical.choose_spec
    ((setup.mem_mappedBoundaryEnds Q ends z x.1).1 x.2)).1

theorem coreVertexOfMappedEnds_eq
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (ends : (↑Q : Set W) → Finset W)
    (hin : ∀ w x, x ∈ ends w → x ∈ C.carrier)
    (z : {u : BoundaryAuxVertex Q //
      u ≠ boundaryLeftRoot Q ∧
        u ≠ boundaryRightRoot Q})
    (x : {x : V // x ∈ setup.mappedBoundaryEnds Q ends z}) :
    x.1 =
      setup.inclusion
        (coreVertexOfMappedEnds setup C Q ends hin z x).1 := by
  exact (Classical.choose_spec
    ((setup.mem_mappedBoundaryEnds Q ends z x.1).1 x.2)).2.symm

/--
All internal data common to the auxiliary graphs in the three cases of
Lemma 6.3.  In particular, connectivity is retained as a proved certificate,
and every represented endpoint is certified to lie in the core and to be
adjacent to its old boundary vertex.
-/
structure BoundaryCoreModel
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W) where
  region : ComponentRegion J C.carrier Q
  /-- The connectivity certificate for the associated two-root auxiliary graph. -/
  connectivity :
    BoundaryAuxConnectivityData J Q leftEnds rightEnds
  left_in_core :
    ∀ w x, x ∈ leftEnds w → x ∈ C.carrier
  right_in_core :
    ∀ w y, y ∈ rightEnds w → y ∈ C.carrier
  left_adjacent :
    ∀ w x, x ∈ leftEnds w → J.Adj x w.1
  right_adjacent :
    ∀ w y, y ∈ rightEnds w → J.Adj w.1 y
  distinct_ends :
    ∀ u v,
      (leftEnds u).Nonempty →
      (rightEnds v).Nonempty →
      ∃ x ∈ leftEnds u, ∃ y ∈ rightEnds v, x ≠ y

namespace BoundaryCoreModel

variable
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds)

/-- Build the common model from two disjoint represented core sets. -/
noncomputable def ofRepresentedSets
    (L R : Finset W)
    (hL : L ⊆ C.carrier)
    (hR : R ⊆ C.carrier)
    (hLR : Disjoint L R)
    (hregion : ComponentRegion J C.carrier Q)
    (hconnectivity :
      BoundaryAuxConnectivityData J Q
        (boundaryEndsIn J Q L)
        (boundaryEndsIn J Q R)) :
    BoundaryCoreModel setup C Q
      (boundaryEndsIn J Q L)
      (boundaryEndsIn J Q R) where
  region := hregion
  connectivity := hconnectivity
  left_in_core := by
    intro w x hx
    exact hL ((mem_boundaryEndsIn J Q L w x).1 hx).1
  right_in_core := by
    intro w y hy
    exact hR ((mem_boundaryEndsIn J Q R w y).1 hy).1
  left_adjacent := by
    intro w x hx
    exact ((mem_boundaryEndsIn J Q L w x).1 hx).2.symm
  right_adjacent := by
    intro w y hy
    exact ((mem_boundaryEndsIn J Q R w y).1 hy).2
  distinct_ends := by
    intro u v hu hv
    obtain ⟨x, hx⟩ := hu
    obtain ⟨y, hy⟩ := hv
    refine ⟨x, hx, y, hy, ?_⟩
    have hxL := ((mem_boundaryEndsIn J Q L u x).1 hx).1
    have hyR := ((mem_boundaryEndsIn J Q R v y).1 hy).1
    intro hxy
    exact Finset.disjoint_left.mp hLR hxL (hxy ▸ hyR)

/--
Turn the concrete component/core data into the exact artificial-root
ambient structure consumed by Lemma 6.2.
-/
noncomputable def boundaryAmbient :
    BoundaryRootAmbient
      (boundaryAuxGraph J Q leftEnds rightEnds)
      (boundaryLeftRoot Q) (boundaryRightRoot Q)
      (boundaryDeficient D Q) B c where
  alpha_ne_beta := by
    simp [boundaryLeftRoot, boundaryRightRoot]
  alpha_not_Z := leftRoot_not_mem_boundaryDeficient D Q
  beta_not_Z := rightRoot_not_mem_boundaryDeficient D Q
  oldHom := setup.boundaryAuxOldHom Q leftEnds rightEnds
  oldHom_injective :=
    setup.boundaryAuxOldHom_injective Q leftEnds rightEnds
  c_not_old_range := by
    rintro ⟨z, hz⟩
    exact setup.c_not_old ⟨(boundaryInteriorOld Q z).1, by
      simpa [boundaryAuxOldHom] using hz⟩
  c_adjacent_Z := by
    intro z hz
    obtain ⟨w, hwD, hzw⟩ :=
      (mem_boundaryDeficient_iff D Q z).1 hz
    subst z
    simpa [boundaryAuxOldHom] using
      setup.deficient_adjacent_to_c w.1 hwD
  leftEnds := setup.mappedBoundaryEnds Q leftEnds
  rightEnds := setup.mappedBoundaryEnds Q rightEnds
  left_adjacent := by
    intro z x hx
    obtain ⟨y, hy, hyx⟩ :=
      (setup.mem_mappedBoundaryEnds Q leftEnds z x).1 hx
    subst x
    apply setup.inclusion.toHom.map_rel'
    exact M.left_adjacent _ y hy
  right_adjacent := by
    intro z y hy
    obtain ⟨x, hx, hxy⟩ :=
      (setup.mem_mappedBoundaryEnds Q rightEnds z y).1 hy
    subst y
    apply setup.inclusion.toHom.map_rel'
    exact M.right_adjacent _ x hx
  left_not_c := by
    intro z x hx hxc
    obtain ⟨y, hy, hyx⟩ :=
      (setup.mem_mappedBoundaryEnds Q leftEnds z x).1 hx
    exact setup.c_not_old ⟨y, hyx.trans hxc⟩
  right_not_c := by
    intro z y hy hyc
    obtain ⟨x, hx, hxy⟩ :=
      (setup.mem_mappedBoundaryEnds Q rightEnds z y).1 hy
    exact setup.c_not_old ⟨x, hxy.trans hyc⟩
  left_not_old_range := by
    intro z x hx
    obtain ⟨y, hy, rfl⟩ :=
      (setup.mem_mappedBoundaryEnds Q leftEnds z x).1 hx
    rintro ⟨w, hw⟩
    have hyw :
        y = (boundaryInteriorOld Q w).1 :=
      setup.inclusion.injective hw.symm
    have hyCore := M.left_in_core _ y hy
    have hwQ := (boundaryInteriorOld Q w).2
    exact M.region.not_mem_separator hwQ (hyw ▸ hyCore)
  right_not_old_range := by
    intro z y hy
    obtain ⟨x, hx, rfl⟩ :=
      (setup.mem_mappedBoundaryEnds Q rightEnds z y).1 hy
    rintro ⟨w, hw⟩
    have hxw :
        x = (boundaryInteriorOld Q w).1 :=
      setup.inclusion.injective hw.symm
    have hxCore := M.right_in_core _ x hx
    have hwQ := (boundaryInteriorOld Q w).2
    exact M.region.not_mem_separator hwQ (hxw ▸ hxCore)
  distinct_ends := by
    intro u v hαu hvβ
    have huVertex := boundaryOldVertex_interior Q u
    have hvVertex := boundaryOldVertex_interior Q v
    have hleft :
        (leftEnds (boundaryInteriorOld Q u)).Nonempty := by
      change
        (boundaryAuxGraph J Q leftEnds rightEnds).Adj
          (boundaryLeftRoot Q) u.1 at hαu
      rw [← huVertex] at hαu
      exact hαu
    have hright :
        (rightEnds (boundaryInteriorOld Q v)).Nonempty := by
      change
        (boundaryAuxGraph J Q leftEnds rightEnds).Adj
          v.1 (boundaryRightRoot Q) at hvβ
      rw [← hvVertex] at hvβ
      exact hvβ
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      M.distinct_ends _ _ hleft hright
    refine ⟨setup.inclusion x, ?_,
      setup.inclusion y, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    · exact fun h => hxy (setup.inclusion.injective h)

end BoundaryCoreModel

/-- Inclusion of an explicit core into the ambient block. -/
def coreHom
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J) :
    J.induce (↑C.carrier : Set W) →g B where
  toFun w := setup.inclusion w.1
  map_rel' := by
    intro x y hxy
    exact setup.inclusion.toHom.map_rel' hxy

theorem coreHom_injective
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J) :
    Function.Injective (setup.coreHom C) := by
  intro x y hxy
  apply Subtype.ext
  exact setup.inclusion.injective hxy

/--
The odd core paths in the precisely scoped opposite-part range used in
paper Section 6.2, constructed internally for an endpoint pair whose
joining edge is present.
-/
private noncomputable def oppositeCoreWitness
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hopposite :
      (x ∈ C.left ∧ y ∈ C.right) ∨
      (x ∈ C.right ∧ y ∈ C.left))
    (hadj : J.Adj x.1 y.1)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank) :
    {P : SimplePath (J.induce (↑C.carrier : Set W)) x y //
      P.length = 1 + 2 * i.val} := by
  let ℓ := 1 + 2 * i.val
  have hadjCore :
      (J.induce (↑C.carrier : Set W)).Adj x y := hadj
  have hodd : Odd ℓ := by
    exact ⟨i.val, by omega⟩
  have hhi : ℓ ≤ 2 * C.rank - 1 := by
    have hi := i.isLt
    omega
  have hex :=
    BGLP.complete_bipartite_core_opposite_part_paths
      (J.induce (↑C.carrier : Set W))
      C.left C.right C.core x y hxy hopposite
      (by simpa [BipartiteCore.rank] using hsafe) ℓ
      hodd hadjCore hhi
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- Map the `i`-th odd-length core path between opposite parts into `B`. -/
noncomputable def oppositeCorePath
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hopposite :
      (x ∈ C.left ∧ y ∈ C.right) ∨
      (x ∈ C.right ∧ y ∈ C.left))
    (hadj : J.Adj x.1 y.1)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank) :
    SimplePath B (setup.inclusion x.1) (setup.inclusion y.1) :=
  (oppositeCoreWitness C x y hxy hopposite hadj hsafe i).1.mapInjectiveHom
    (setup.coreHom C)
    (setup.coreHom_injective C)

@[simp] theorem oppositeCorePath_length
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hopposite :
      (x ∈ C.left ∧ y ∈ C.right) ∨
      (x ∈ C.right ∧ y ∈ C.left))
    (hadj : J.Adj x.1 y.1)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank) :
    (setup.oppositeCorePath C x y hxy hopposite hadj hsafe i).length =
      1 + 2 * i.val := by
  change
    ((oppositeCoreWitness C x y hxy hopposite hadj hsafe i).1.mapInjectiveHom
      (setup.coreHom C) (setup.coreHom_injective C)).length =
        1 + 2 * i.val
  calc
    _ = (oppositeCoreWitness C x y hxy hopposite hadj hsafe i).1.length := by
      apply SimplePath.mapInjectiveHom_length
    _ = 1 + 2 * i.val :=
      (oppositeCoreWitness C x y hxy hopposite hadj hsafe i).2

/--
A core of rank at least five yields an actual simple 10-cycle in the ambient
block.  The long side is a certified length-nine BGLP path and the closing
edge is a one-edge simple path; disjointness of their tails is proved before
forming the cycle.
-/
theorem core_rank_five_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (hrank : 5 ≤ C.rank) :
    False := by
  classical
  let L := coreVertexSet C C.left
  let R := coreVertexSet C C.right
  have hLcard : 5 ≤ L.card := by
    change 5 ≤ (coreVertexSet C C.left).card
    rw [card_coreVertexSet]
    exact hrank.trans
      (Nat.min_le_left C.left.card C.right.card)
  have hRcard : 5 ≤ R.card := by
    change 5 ≤ (coreVertexSet C C.right).card
    rw [card_coreVertexSet]
    exact hrank.trans
      (Nat.min_le_right C.left.card C.right.card)
  have hedge :
      ∃ x ∈ L, ∃ y ∈ R, J.Adj x y := by
    rcases C.complete_or_missing with hcomplete | hmissing
    · obtain ⟨x, hxL⟩ :=
        Finset.card_pos.mp (by omega : 0 < L.card)
      obtain ⟨y, hyR⟩ :=
        Finset.card_pos.mp (by omega : 0 < R.card)
      exact ⟨x, hxL, y, hyR,
        hcomplete x hxL y hyR⟩
    · let M : C.MissingEdgeData :=
        Classical.choice hmissing
      have hxMissing : M.xMissing ∈ L := by
        simpa [L] using M.x_left
      have hErasePos :
          0 < (L.erase M.xMissing).card := by
        rw [Finset.card_erase_of_mem hxMissing]
        omega
      obtain ⟨x, hxErase⟩ :=
        Finset.card_pos.mp hErasePos
      obtain ⟨y, hyR⟩ :=
        Finset.card_pos.mp (by omega : 0 < R.card)
      have hxL : x ∈ L :=
        Finset.mem_of_mem_erase hxErase
      have hxNe : x ≠ M.xMissing :=
        (Finset.mem_erase.mp hxErase).1
      exact ⟨x, hxL, y, hyR,
        M.cross_except_left x hxL y hyR hxNe⟩
  obtain ⟨x, hxL, y, hyR, hxy⟩ := hedge
  obtain ⟨hxCore, hxSide⟩ :=
    (mem_coreVertexSet C C.left x).1
      (by simpa [L] using hxL)
  obtain ⟨hyCore, hySide⟩ :=
    (mem_coreVertexSet C C.right y).1
      (by simpa [R] using hyR)
  let xC : (↑C.carrier : Set W) :=
    ⟨x, hxCore⟩
  let yC : (↑C.carrier : Set W) :=
    ⟨y, hyCore⟩
  have hxyC : xC ≠ yC := by
    intro heq
    exact hxy.ne
      (congrArg Subtype.val heq)
  have hopposite :
      (xC ∈ C.left ∧ yC ∈ C.right) ∨
        (xC ∈ C.right ∧ yC ∈ C.left) :=
    Or.inl ⟨hxSide, hySide⟩
  let i : Fin C.rank := ⟨4, hrank⟩
  let P :=
    setup.oppositeCorePath C xC yC
      hxyC hopposite hxy (Or.inl (hrank.trans' (by omega))) i
  have hxyB :
      B.Adj (setup.inclusion x)
        (setup.inclusion y) :=
    setup.inclusion.toHom.map_rel' hxy
  let Q :
      SimplePath B (setup.inclusion y)
        (setup.inclusion x) :=
    SimplePath.ofAdj hxyB.symm
  have hPlength : P.length = 9 := by
    simp [P, i]
  have hQlength : Q.length = 1 := by
    simp [Q]
  have hdisjoint :
      P.walk.support.tail.Disjoint
        Q.walk.support.tail := by
    simp [Q]
    have hstart := P.start_not_mem_tail
    change setup.inclusion x ∉
      P.walk.support.tail at hstart
    exact hstart
  let cycle :=
    cycleOfDisjointPaths P Q hdisjoint
      (Or.inl (by omega))
  have hcycleLength : cycle.length = 10 := by
    rw [cycleOfDisjointPaths_length]
    omega
  apply setup.no_divisible_cycle
  exact ⟨cycle, by simp [hcycleLength]⟩

/-- The numerical rank bound (6.2). -/
theorem core_rank_le_four
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J) :
    C.rank ≤ 4 := by
  by_contra hrank
  exact setup.core_rank_five_contradiction
    C (by omega)

/--
The core cannot span all vertices of `J`.  This is the full degree/counting
argument following (6.2), with ambient degree identified explicitly with
degree into the spanning carrier.
-/
theorem core_carrier_ne_univ
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (hrhi : C.rank ≤ 4) :
    C.carrier ≠ Finset.univ := by
  classical
  intro hcarrier
  have boundary_eq_degree
      (E : BipartiteCore J)
      (hEcarrier : E.carrier = Finset.univ)
      (w : W) :
      finiteBoundaryDegree J E.carrier w =
        finiteDegree J w := by
    simp [finiteBoundaryDegree, finiteDegree,
      hEcarrier]
  rcases C.complete_or_missing with hcomplete | hmissing
  · have oriented_complete_impossible
        (E : BipartiteCore J)
        (hEcomplete :
          ∀ x ∈ coreVertexSet E E.left,
            ∀ y ∈ coreVertexSet E E.right,
              J.Adj x y)
        (hEcarrier : E.carrier = Finset.univ)
        (hErank : E.rank ≤ 4)
        (hleftLe : E.left.card ≤ E.right.card) :
        False := by
      let L := coreVertexSet E E.left
      let R := coreVertexSet E E.right
      have hLcardTwo : 2 ≤ L.card := by
        change 2 ≤ (coreVertexSet E E.left).card
        rw [card_coreVertexSet]
        exact E.two_le_rank.trans
          (Nat.min_le_left E.left.card E.right.card)
      have hRcardTwo : 2 ≤ R.card := by
        change 2 ≤ (coreVertexSet E E.right).card
        rw [card_coreVertexSet]
        exact E.two_le_rank.trans
          (Nat.min_le_right E.left.card E.right.card)
      obtain ⟨x, hxL⟩ :=
        Finset.card_pos.mp (by omega : 0 < L.card)
      obtain ⟨y, hyR⟩ :=
        Finset.card_pos.mp (by omega : 0 < R.card)
      have hrightFour : 4 ≤ E.right.card := by
        have hdegree :=
          setup.degree_at_least_four x
        have hboundary :=
          E.finiteBoundaryDegree_eq_right_card_of_complete
            hEcomplete x (by simpa [L] using hxL)
        have heq :=
          boundary_eq_degree E hEcarrier x
        omega
      have hleftFour : 4 ≤ E.left.card := by
        have hdegree :=
          setup.degree_at_least_four y
        have hboundary :=
          E.finiteBoundaryDegree_eq_left_card_of_complete
            hEcomplete y (by simpa [R] using hyR)
        have heq :=
          boundary_eq_degree E hEcarrier y
        omega
      have hleftCard : E.left.card = 4 := by
        rw [BipartiteCore.rank,
          Nat.min_eq_left hleftLe] at hErank
        omega
      have hdegreeFourMem :
          ∀ w, finiteDegree J w = 4 → w ∈ D := by
        intro w hdegree
        by_contra hwD
        have hregular :=
          setup.degree_regular w hwD
        omega
      have hRsubD : R ⊆ D := by
        intro z hzR
        apply hdegreeFourMem z
        have hboundary :=
          E.finiteBoundaryDegree_eq_left_card_of_complete
            hEcomplete z (by simpa [R] using hzR)
        have heq :=
          boundary_eq_degree E hEcarrier z
        omega
      by_cases hRfive : 5 ≤ R.card
      · have hcardLe :=
          Finset.card_le_card hRsubD
        have hDcard := setup.deficient_card
        omega
      · have hRcard : R.card = 4 := by
          have : R.card = E.right.card :=
            card_coreVertexSet E E.right
          omega
        have hrightCard : E.right.card = 4 := by
          have hRraw :
              R.card = E.right.card :=
            card_coreVertexSet E E.right
          omega
        have hLsubD : L ⊆ D := by
          intro z hzL
          apply hdegreeFourMem z
          have hboundary :=
            E.finiteBoundaryDegree_eq_right_card_of_complete
              hEcomplete z (by simpa [L] using hzL)
          have heq :=
            boundary_eq_degree E hEcarrier z
          omega
        have hLR : Disjoint L R :=
          disjoint_coreVertexSet E E.core.1
        have hUnionSub : L ∪ R ⊆ D :=
          Finset.union_subset hLsubD hRsubD
        have hUnionCard :
            (L ∪ R).card = 8 := by
          rw [Finset.card_union_of_disjoint hLR]
          have hLcard : L.card = 4 := by
            simpa [L] using hleftCard
          omega
        have hcardLe :=
          Finset.card_le_card hUnionSub
        have hDcard := setup.deficient_card
        omega
    by_cases hle : C.left.card ≤ C.right.card
    · exact oriented_complete_impossible
        C hcomplete hcarrier hrhi hle
    · let C' := C.swap
      have hcomplete' :
          ∀ x ∈ coreVertexSet C' C'.left,
            ∀ y ∈ coreVertexSet C' C'.right,
              J.Adj x y := by
        intro x hx y hy
        have hxOld :
            x ∈ coreVertexSet C C.right := by
          simpa [C', BipartiteCore.swap,
            coreVertexSet] using hx
        have hyOld :
            y ∈ coreVertexSet C C.left := by
          simpa [C', BipartiteCore.swap,
            coreVertexSet] using hy
        exact (hcomplete y hyOld x hxOld).symm
      exact oriented_complete_impossible
        C' hcomplete'
        (by simpa [C', BipartiteCore.swap] using hcarrier)
        (by simpa [C'] using hrhi)
        (by
          simp [C', BipartiteCore.swap]
          exact Nat.le_of_not_ge hle)
  · let M : C.MissingEdgeData :=
      Classical.choice hmissing
    have oriented_missing_impossible
        (E : BipartiteCore J)
        (N : E.MissingEdgeData)
        (hEcarrier : E.carrier = Finset.univ)
        (hErank : E.rank ≤ 4)
        (hleftLe : E.left.card ≤ E.right.card) :
        False := by
      have hleftRank :
          E.left.card = E.rank := by
        simp [BipartiteCore.rank,
          Nat.min_eq_left hleftLe]
      have hboundary :=
        N.finiteBoundaryDegree_missing_right
      have heq :=
        boundary_eq_degree E hEcarrier N.yMissing
      have hdegree :=
        setup.degree_at_least_four N.yMissing
      omega
    by_cases hle : C.left.card ≤ C.right.card
    · exact oriented_missing_impossible
        C M hcarrier hrhi hle
    · exact oriented_missing_impossible
        C.swap M.swap
        (by simpa [BipartiteCore.swap] using hcarrier)
        (by simpa using hrhi)
        (by
          simp [BipartiteCore.swap]
          exact Nat.le_of_not_ge hle)

/--
The even core paths in the precisely scoped same-part range used in paper
Section 6.2, constructed internally. There are `rank - 1` lengths
`2,4,...,2 rank-2`.
-/
private noncomputable def sameCoreWitness
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsame :
      (x ∈ C.left ∧ y ∈ C.left) ∨
      (x ∈ C.right ∧ y ∈ C.right))
    (i : Fin (C.rank - 1)) :
    {P : SimplePath (J.induce (↑C.carrier : Set W)) x y //
      P.length = 2 + 2 * i.val} := by
  let ℓ := 2 + 2 * i.val
  have heven : Even ℓ := by
    exact ⟨i.val + 1, by omega⟩
  have hallowed :
      ℓ ≤ 2 * C.rank - 2 ∨
      (ℓ = 2 * C.rank ∧
        ((x ∈ C.left ∧ y ∈ C.left ∧ C.rank < C.left.card) ∨
         (x ∈ C.right ∧ y ∈ C.right ∧ C.rank < C.right.card))) := by
    left
    have hi := i.isLt
    have hr := C.two_le_rank
    omega
  have hshort :
      ℓ ≤ 2 * C.rank - 2 := by
    have hi := i.isLt
    have hr := C.two_le_rank
    dsimp [ℓ]
    omega
  have hex :=
    BGLP.complete_bipartite_core_same_part_paths
      (J.induce (↑C.carrier : Set W))
      C.left C.right C.core x y hxy hsame ℓ heven
      (by omega) hallowed
      (Or.inl (by
        simpa [BipartiteCore.rank] using hshort))
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- Map the `i`-th even-length core path between vertices in one part into `B`. -/
noncomputable def sameCorePath
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsame :
      (x ∈ C.left ∧ y ∈ C.left) ∨
      (x ∈ C.right ∧ y ∈ C.right))
    (i : Fin (C.rank - 1)) :
    SimplePath B (setup.inclusion x.1) (setup.inclusion y.1) :=
  (sameCoreWitness C x y hxy hsame i).1.mapInjectiveHom
    (setup.coreHom C)
    (setup.coreHom_injective C)

@[simp] theorem sameCorePath_length
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsame :
      (x ∈ C.left ∧ y ∈ C.left) ∨
      (x ∈ C.right ∧ y ∈ C.right))
    (i : Fin (C.rank - 1)) :
    (setup.sameCorePath C x y hxy hsame i).length =
      2 + 2 * i.val := by
  change
    ((sameCoreWitness C x y hxy hsame i).1.mapInjectiveHom
      (setup.coreHom C) (setup.coreHom_injective C)).length =
        2 + 2 * i.val
  calc
    _ = (sameCoreWitness C x y hxy hsame i).1.length := by
      apply SimplePath.mapInjectiveHom_length
    _ = 2 + 2 * i.val :=
      (sameCoreWitness C x y hxy hsame i).2

/--
The internally proved extended same-part clause corresponding to BGLP
Lemma 3.1. If the endpoint part is strictly larger than the core rank, the
additional terminal length `2 * rank` is available. This is the special
`r = 2`, `t ≥ 3` route in the rank-two branch of Lemma 6.3.
-/
private noncomputable def sameLargerCoreWitness
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsameLarger :
      (x ∈ C.left ∧ y ∈ C.left ∧
        C.rank < C.left.card) ∨
      (x ∈ C.right ∧ y ∈ C.right ∧
        C.rank < C.right.card))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank) :
    {P : SimplePath (J.induce (↑C.carrier : Set W)) x y //
      P.length = 2 + 2 * i.val} := by
  let ℓ := 2 + 2 * i.val
  have heven : Even ℓ := by
    exact ⟨i.val + 1, by omega⟩
  have hsame :
      (x ∈ C.left ∧ y ∈ C.left) ∨
      (x ∈ C.right ∧ y ∈ C.right) := by
    rcases hsameLarger with h | h
    · exact Or.inl ⟨h.1, h.2.1⟩
    · exact Or.inr ⟨h.1, h.2.1⟩
  have hallowed :
      ℓ ≤ 2 * C.rank - 2 ∨
      (ℓ = 2 * C.rank ∧
        ((x ∈ C.left ∧ y ∈ C.left ∧
            C.rank < C.left.card) ∨
         (x ∈ C.right ∧ y ∈ C.right ∧
            C.rank < C.right.card))) := by
    by_cases hshort : ℓ ≤ 2 * C.rank - 2
    · exact Or.inl hshort
    · exact Or.inr ⟨by
        have hi := i.isLt
        have hr := C.two_le_rank
        dsimp [ℓ] at hshort ⊢
        omega, hsameLarger⟩
  have hex :=
    BGLP.complete_bipartite_core_same_part_paths
      (J.induce (↑C.carrier : Set W))
      C.left C.right C.core x y hxy hsame ℓ heven
      (by omega) hallowed
      (by
        by_cases hshort : ℓ ≤ 2 * C.rank - 2
        · exact Or.inl hshort
        · right
          simpa [BipartiteCore.rank] using hsafe)
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/--
Map the extended `i`-th even core path into `B` when its endpoint part is
strictly larger than the core rank.
-/
noncomputable def sameLargerCorePath
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsameLarger :
      (x ∈ C.left ∧ y ∈ C.left ∧
        C.rank < C.left.card) ∨
      (x ∈ C.right ∧ y ∈ C.right ∧
        C.rank < C.right.card))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank) :
    SimplePath B (setup.inclusion x.1) (setup.inclusion y.1) :=
  (sameLargerCoreWitness C x y hxy hsameLarger hsafe i).1.mapInjectiveHom
    (setup.coreHom C)
    (setup.coreHom_injective C)

@[simp] theorem sameLargerCorePath_length
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsameLarger :
      (x ∈ C.left ∧ y ∈ C.left ∧
        C.rank < C.left.card) ∨
      (x ∈ C.right ∧ y ∈ C.right ∧
        C.rank < C.right.card))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank) :
    (setup.sameLargerCorePath C x y hxy
      hsameLarger hsafe i).length =
        2 + 2 * i.val := by
  change
    ((sameLargerCoreWitness C x y hxy
      hsameLarger hsafe i).1.mapInjectiveHom
        (setup.coreHom C)
        (setup.coreHom_injective C)).length =
          2 + 2 * i.val
  calc
    _ =
        (sameLargerCoreWitness C x y hxy
          hsameLarger hsafe i).1.length := by
      apply SimplePath.mapInjectiveHom_length
    _ = 2 + 2 * i.val :=
      (sameLargerCoreWitness C x y hxy
        hsameLarger hsafe i).2

/--
An outside path sequence whose two endpoints lie in an explicit core and
whose only core vertices are those endpoints.
-/
structure CoreEndpointSequence
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q) where
  /-- The core vertex represented by the left endpoint of path `i`. -/
  xCore : Fin q → (↑C.carrier : Set W)
  /-- The core vertex represented by the right endpoint of path `i`. -/
  yCore : Fin q → (↑C.carrier : Set W)
  x_eq : ∀ i, outside.x i = setup.inclusion (xCore i).1
  y_eq : ∀ i, outside.y i = setup.inclusion (yCore i).1
  meets_core_only_at_ends :
    ∀ i z,
      z ∈ (outside.path i).walk.support →
      z ∈ Set.range (setup.coreHom C) →
      z = outside.x i ∨ z = outside.y i

namespace CoreEndpointSequence

theorem core_endpoints_ne
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    (E : CoreEndpointSequence setup C outside)
    (i : Fin q) :
    E.xCore i ≠ E.yCore i := by
  intro hxy
  apply outside.endpoints_ne i
  rw [E.x_eq, E.y_eq, hxy]

end CoreEndpointSequence

/-- A core-endpoint sequence whose endpoints lie in opposite bipartition classes. -/
structure OppositeCoreEndpointSequence
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    extends CoreEndpointSequence setup C outside where
  opposite : ∀ i,
    (xCore i ∈ C.left ∧ yCore i ∈ C.right) ∨
    (xCore i ∈ C.right ∧ yCore i ∈ C.left)
  adjacent : ∀ i, J.Adj (xCore i).1 (yCore i).1

/-- A core-endpoint sequence whose endpoints lie in the same bipartition class. -/
structure SameCoreEndpointSequence
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    extends CoreEndpointSequence setup C outside where
  same : ∀ i,
    (xCore i ∈ C.left ∧ yCore i ∈ C.left) ∨
    (xCore i ∈ C.right ∧ yCore i ∈ C.right)

/--
Same-part endpoints in a side strictly larger than the core rank. This is
exactly the extra hypothesis in the internally proved terminal-length clause
corresponding to BGLP Lemma 3.1.
-/
structure SameLargerCoreEndpointSequence
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    extends CoreEndpointSequence setup C outside where
  same_larger : ∀ i,
    (xCore i ∈ C.left ∧ yCore i ∈ C.left ∧
      C.rank < C.left.card) ∨
    (xCore i ∈ C.right ∧ yCore i ∈ C.right ∧
      C.rank < C.right.card)

/--
Compatibility between the boundary sets in Lemma 6.2 and one explicit
bipartite core.
-/
structure CoreBoundaryAmbient
    {U : Type*} [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {H : SimpleGraph U} {α β : U} {Z : Finset U}
    (A : BoundaryRootAmbient H α β Z B c) where
  /-- Recover the core vertex represented by a selected left boundary endpoint. -/
  leftCore :
    ∀ u, {x : V // x ∈ A.leftEnds u} →
      (↑C.carrier : Set W)
  /-- Recover the core vertex represented by a selected right boundary endpoint. -/
  rightCore :
    ∀ v, {y : V // y ∈ A.rightEnds v} →
      (↑C.carrier : Set W)
  left_eq :
    ∀ u x, x.1 =
      setup.inclusion (leftCore u x).1
  right_eq :
    ∀ v y, y.1 =
      setup.inclusion (rightCore v y).1
  interior_disjoint :
    Disjoint (Set.range A.interiorHom)
      (Set.range (setup.coreHom C))

/--
The common boundary model automatically supplies the endpoint maps and the
interior/core disjointness certificate needed to close lifted paths into
simple cycles.
-/
noncomputable def BoundaryCoreModel.coreBoundaryAmbient
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds) :
    CoreBoundaryAmbient setup C
      (M.boundaryAmbient setup C Q leftEnds rightEnds) where
  leftCore u x :=
    coreVertexOfMappedEnds setup C Q leftEnds
      M.left_in_core u
      ⟨x.1, by
        exact x.2⟩
  rightCore v y :=
    coreVertexOfMappedEnds setup C Q rightEnds
      M.right_in_core v
      ⟨y.1, by
        exact y.2⟩
  left_eq u x := by
    apply coreVertexOfMappedEnds_eq setup C Q leftEnds
      M.left_in_core u
      ⟨x.1, by
        exact x.2⟩
  right_eq v y := by
    apply coreVertexOfMappedEnds_eq setup C Q rightEnds
      M.right_in_core v
      ⟨y.1, by
        exact y.2⟩
  interior_disjoint := by
    apply Set.disjoint_left.mpr
    intro z hzInterior hzCore
    obtain ⟨a, ha⟩ := hzInterior
    obtain ⟨k, hk⟩ := hzCore
    rcases a with ⟨a, haRoots⟩
    cases a with
    | none =>
        apply setup.c_not_old
        refine ⟨k.1, ?_⟩
        calc
          setup.inclusion k.1 =
              setup.coreHom C k := rfl
          _ = z := hk
          _ =
              (M.boundaryAmbient setup C Q
                leftEnds rightEnds).interiorHom
                ⟨none, haRoots⟩ := ha.symm
          _ = c := by
            rfl
    | some a =>
        let aOld :
            {z : BoundaryAuxVertex Q //
              z ≠ boundaryLeftRoot Q ∧
                z ≠ boundaryRightRoot Q} :=
          ⟨a, by
            constructor
            · intro h
              exact haRoots.1 (congrArg some h)
            · intro h
              exact haRoots.2 (congrArg some h)⟩
        have heq :
            setup.inclusion (boundaryInteriorOld Q aOld).1 =
              setup.inclusion k.1 := by
          calc
            setup.inclusion (boundaryInteriorOld Q aOld).1 =
                (M.boundaryAmbient setup C Q
                  leftEnds rightEnds).interiorHom
                  ⟨some a, haRoots⟩ := by
                    rfl
            _ = z := ha
            _ = setup.coreHom C k := hk.symm
            _ = setup.inclusion k.1 := rfl
        have hval :
            (boundaryInteriorOld Q aOld).1 = k.1 :=
          setup.inclusion.injective heq
        exact M.region.not_mem_separator
          (boundaryInteriorOld Q aOld).2
          (hval ▸ k.2)

/--
Boundary/core compatibility when every selected endpoint pair lies in
opposite bipartition classes and is joined by a core edge.
-/
structure OppositeCoreBoundaryAmbient
    {U : Type*} [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {H : SimpleGraph U} {α β : U} {Z : Finset U}
    (A : BoundaryRootAmbient H α β Z B c)
    extends CoreBoundaryAmbient setup C A where
  opposite :
    ∀ u v x y,
      (leftCore u x ∈ C.left ∧ rightCore v y ∈ C.right) ∨
      (leftCore u x ∈ C.right ∧ rightCore v y ∈ C.left)
  adjacent :
    ∀ u v x y,
      J.Adj (leftCore u x).1 (rightCore v y).1

/--
Boundary/core compatibility when every selected endpoint pair lies in the
same bipartition class.
-/
structure SameCoreBoundaryAmbient
    {U : Type*} [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {H : SimpleGraph U} {α β : U} {Z : Finset U}
    (A : BoundaryRootAmbient H α β Z B c)
    extends CoreBoundaryAmbient setup C A where
  same :
    ∀ u v x y,
      (leftCore u x ∈ C.left ∧ rightCore v y ∈ C.left) ∨
      (leftCore u x ∈ C.right ∧ rightCore v y ∈ C.right)

/-- Add opposite-part and joining-edge certificates to a common model. -/
noncomputable def BoundaryCoreModel.oppositeAmbient
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds)
    (hopposite :
      ∀ u v x y
        (hx : x ∈ leftEnds u) (hy : y ∈ rightEnds v),
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.right) ∨
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.right ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.left))
    (hadjacent :
      ∀ u v x y,
        x ∈ leftEnds u → y ∈ rightEnds v →
          J.Adj x y) :
    OppositeCoreBoundaryAmbient setup C
      (M.boundaryAmbient setup C Q leftEnds rightEnds) where
  toCoreBoundaryAmbient :=
    M.coreBoundaryAmbient setup C Q leftEnds rightEnds
  opposite := by
    intro u v x y
    let x' :
        {x : V // x ∈ setup.mappedBoundaryEnds Q leftEnds u} :=
      ⟨x.1, by
        exact x.2⟩
    let y' :
        {y : V // y ∈ setup.mappedBoundaryEnds Q rightEnds v} :=
      ⟨y.1, by
        exact y.2⟩
    have hx :=
      coreVertexOfMappedEnds_mem setup C Q leftEnds
        M.left_in_core u x'
    have hy :=
      coreVertexOfMappedEnds_mem setup C Q rightEnds
        M.right_in_core v y'
    simpa [BoundaryCoreModel.coreBoundaryAmbient, x', y'] using
      hopposite
        (boundaryInteriorOld Q u)
        (boundaryInteriorOld Q v)
        (coreVertexOfMappedEnds setup C Q leftEnds
          M.left_in_core u x').1
        (coreVertexOfMappedEnds setup C Q rightEnds
          M.right_in_core v y').1
        hx hy
  adjacent := by
    intro u v x y
    let x' :
        {x : V // x ∈ setup.mappedBoundaryEnds Q leftEnds u} :=
      ⟨x.1, by
        exact x.2⟩
    let y' :
        {y : V // y ∈ setup.mappedBoundaryEnds Q rightEnds v} :=
      ⟨y.1, by
        exact y.2⟩
    have hx :=
      coreVertexOfMappedEnds_mem setup C Q leftEnds
        M.left_in_core u x'
    have hy :=
      coreVertexOfMappedEnds_mem setup C Q rightEnds
        M.right_in_core v y'
    simpa [BoundaryCoreModel.coreBoundaryAmbient, x', y'] using
      hadjacent
        (boundaryInteriorOld Q u)
        (boundaryInteriorOld Q v)
        (coreVertexOfMappedEnds setup C Q leftEnds
          M.left_in_core u x').1
        (coreVertexOfMappedEnds setup C Q rightEnds
          M.right_in_core v y').1
        hx hy

/-- Add same-part certificates to a common boundary/core model. -/
noncomputable def BoundaryCoreModel.sameAmbient
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds)
    (hsame :
      ∀ u v x y
        (hx : x ∈ leftEnds u) (hy : y ∈ rightEnds v),
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.left) ∨
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.right ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.right)) :
    SameCoreBoundaryAmbient setup C
      (M.boundaryAmbient setup C Q leftEnds rightEnds) where
  toCoreBoundaryAmbient :=
    M.coreBoundaryAmbient setup C Q leftEnds rightEnds
  same := by
    intro u v x y
    let x' :
        {x : V // x ∈ setup.mappedBoundaryEnds Q leftEnds u} :=
      ⟨x.1, by
        exact x.2⟩
    let y' :
        {y : V // y ∈ setup.mappedBoundaryEnds Q rightEnds v} :=
      ⟨y.1, by
        exact y.2⟩
    have hx :=
      coreVertexOfMappedEnds_mem setup C Q leftEnds
        M.left_in_core u x'
    have hy :=
      coreVertexOfMappedEnds_mem setup C Q rightEnds
        M.right_in_core v y'
    simpa [BoundaryCoreModel.coreBoundaryAmbient, x', y'] using
      hsame
        (boundaryInteriorOld Q u)
        (boundaryInteriorOld Q v)
        (coreVertexOfMappedEnds setup C Q leftEnds
          M.left_in_core u x').1
        (coreVertexOfMappedEnds setup C Q rightEnds
          M.right_in_core v y').1
        hx hy

/--
Turn a lifted boundary family with opposite-part endpoints into an explicit
core-endpoint sequence.
-/
def OppositeCoreBoundaryAmbient.endpointSequence
    {U : Type*} [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {H : SimpleGraph U} {α β : U} {Z : Finset U}
    (A : BoundaryRootAmbient H α β Z B c)
    (K : OppositeCoreBoundaryAmbient setup C A)
    {q : ℕ}
    {F : AdmissiblePathFamily
      (adjoinRoot H Z) (some α) (some β) q}
    (R : BoundaryRootAmbient.BoundaryLiftedSequence A F) :
    OppositeCoreEndpointSequence setup C (R.family A) where
  xCore i :=
    K.leftCore (R.leftOld i)
      ⟨(R.family A).x i, R.left_mem i⟩
  yCore i :=
    K.rightCore (R.rightOld i)
      ⟨(R.family A).y i, R.right_mem i⟩
  x_eq i :=
    K.left_eq (R.leftOld i)
      ⟨(R.family A).x i, R.left_mem i⟩
  y_eq i :=
    K.right_eq (R.rightOld i)
      ⟨(R.family A).y i, R.right_mem i⟩
  meets_core_only_at_ends i z hz hzCore := by
    rcases R.support_cases A i hz with hzx | hzy | hzInterior
    · exact Or.inl hzx
    · exact Or.inr hzy
    · exact False.elim
        (Set.disjoint_left.1 K.interior_disjoint
          hzInterior hzCore)
  opposite i :=
    K.opposite (R.leftOld i) (R.rightOld i)
      ⟨(R.family A).x i, R.left_mem i⟩
      ⟨(R.family A).y i, R.right_mem i⟩
  adjacent i :=
    K.adjacent (R.leftOld i) (R.rightOld i)
      ⟨(R.family A).x i, R.left_mem i⟩
      ⟨(R.family A).y i, R.right_mem i⟩

/--
Turn a lifted boundary family with same-part endpoints into an explicit
core-endpoint sequence.
-/
def SameCoreBoundaryAmbient.endpointSequence
    {U : Type*} [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {H : SimpleGraph U} {α β : U} {Z : Finset U}
    (A : BoundaryRootAmbient H α β Z B c)
    (K : SameCoreBoundaryAmbient setup C A)
    {q : ℕ}
    {F : AdmissiblePathFamily
      (adjoinRoot H Z) (some α) (some β) q}
    (R : BoundaryRootAmbient.BoundaryLiftedSequence A F) :
    SameCoreEndpointSequence setup C (R.family A) where
  xCore i :=
    K.leftCore (R.leftOld i)
      ⟨(R.family A).x i, R.left_mem i⟩
  yCore i :=
    K.rightCore (R.rightOld i)
      ⟨(R.family A).y i, R.right_mem i⟩
  x_eq i :=
    K.left_eq (R.leftOld i)
      ⟨(R.family A).x i, R.left_mem i⟩
  y_eq i :=
    K.right_eq (R.rightOld i)
      ⟨(R.family A).y i, R.right_mem i⟩
  meets_core_only_at_ends i z hz hzCore := by
    rcases R.support_cases A i hz with hzx | hzy | hzInterior
    · exact Or.inl hzx
    · exact Or.inr hzy
    · exact False.elim
        (Set.disjoint_left.1 K.interior_disjoint
          hzInterior hzCore)
  same i :=
    K.same (R.leftOld i) (R.rightOld i)
      ⟨(R.family A).x i, R.left_mem i⟩
      ⟨(R.family A).y i, R.right_mem i⟩

theorem oppositeCorePath_support_range
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hopposite :
      (x ∈ C.left ∧ y ∈ C.right) ∨
      (x ∈ C.right ∧ y ∈ C.left))
    (hadj : J.Adj x.1 y.1)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank)
    {z : V}
    (hz : z ∈
      (setup.oppositeCorePath C x y hxy hopposite hadj hsafe i).walk.support) :
    z ∈ Set.range (setup.coreHom C) := by
  exact SimplePath.mem_range_of_mem_mapInjectiveHom_support
    (oppositeCoreWitness C x y hxy hopposite hadj hsafe i).1
    (setup.coreHom C) (setup.coreHom_injective C) hz

theorem sameCorePath_support_range
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsame :
      (x ∈ C.left ∧ y ∈ C.left) ∨
      (x ∈ C.right ∧ y ∈ C.right))
    (i : Fin (C.rank - 1))
    {z : V}
    (hz : z ∈
      (setup.sameCorePath C x y hxy hsame i).walk.support) :
    z ∈ Set.range (setup.coreHom C) := by
  exact SimplePath.mem_range_of_mem_mapInjectiveHom_support
    (sameCoreWitness C x y hxy hsame i).1
    (setup.coreHom C) (setup.coreHom_injective C) hz

theorem sameLargerCorePath_support_range
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (x y : (↑C.carrier : Set W))
    (hxy : x ≠ y)
    (hsameLarger :
      (x ∈ C.left ∧ y ∈ C.left ∧
        C.rank < C.left.card) ∨
      (x ∈ C.right ∧ y ∈ C.right ∧
        C.rank < C.right.card))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (i : Fin C.rank)
    {z : V}
    (hz : z ∈
      (setup.sameLargerCorePath C x y hxy
        hsameLarger hsafe i).walk.support) :
    z ∈ Set.range (setup.coreHom C) := by
  exact SimplePath.mem_range_of_mem_mapInjectiveHom_support
    (sameLargerCoreWitness C x y hxy
      hsameLarger hsafe i).1
    (setup.coreHom C) (setup.coreHom_injective C) hz

/-- Build all odd core closures for opposite-part endpoint pairs. -/
noncomputable def oppositeCoreGrid
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    (E : OppositeCoreEndpointSequence setup C outside)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b) :
    PathSequenceCoreGrid B outside C.rank := by
  let core (i : Fin q) (j : Fin C.rank) :
      SimplePath B (outside.y i) (outside.x i) :=
    ((setup.oppositeCorePath C
      (E.yCore i) (E.xCore i)
      (E.toCoreEndpointSequence.core_endpoints_ne
        setup C outside i).symm
      (by
        rcases E.opposite i with h | h
        · exact Or.inr ⟨h.2, h.1⟩
        · exact Or.inl ⟨h.2, h.1⟩)
      (E.adjacent i).symm hsafe j).castStart
        (E.y_eq i).symm).castEnd (E.x_eq i).symm
  have hlength : ∀ i j,
      (core i j).length = 1 + j.val * 2 := by
    intro i j
    simp [core, Nat.mul_comm]
  have hdisjoint : ∀ i j,
      (outside.path i).walk.support.tail.Disjoint
        (core i j).walk.support.tail := by
    intro i j
    rw [List.disjoint_left]
    intro z hzOutside hzCore
    have hzCoreFull :
        z ∈ (core i j).walk.support :=
      List.mem_of_mem_tail hzCore
    have hzRange : z ∈ Set.range (setup.coreHom C) := by
      apply setup.oppositeCorePath_support_range C
        (E.yCore i) (E.xCore i)
        (E.toCoreEndpointSequence.core_endpoints_ne
          setup C outside i).symm
        (by
          rcases E.opposite i with h | h
          · exact Or.inr ⟨h.2, h.1⟩
          · exact Or.inl ⟨h.2, h.1⟩)
        (E.adjacent i).symm hsafe j
      simpa [core] using hzCoreFull
    have hzEnds :=
      E.meets_core_only_at_ends i z
        (List.mem_of_mem_tail hzOutside) hzRange
    rcases hzEnds with hzx | hzy
    · exact (outside.path i).start_not_mem_tail
        (hzx ▸ hzOutside)
    · exact (core i j).start_not_mem_tail
        (hzy ▸ hzCore)
  exact PathSequenceCoreGrid.ofDisjointCorePaths
    B outside 1 2 (Or.inr rfl) core hlength hdisjoint

/-- Build all even core closures for same-part endpoint pairs. -/
noncomputable def sameCoreGrid
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    (E : SameCoreEndpointSequence setup C outside) :
    PathSequenceCoreGrid B outside (C.rank - 1) := by
  let core (i : Fin q) (j : Fin (C.rank - 1)) :
      SimplePath B (outside.y i) (outside.x i) :=
    ((setup.sameCorePath C
      (E.yCore i) (E.xCore i)
      (E.toCoreEndpointSequence.core_endpoints_ne
        setup C outside i).symm
      (by
        rcases E.same i with h | h
        · exact Or.inl ⟨h.2, h.1⟩
        · exact Or.inr ⟨h.2, h.1⟩)
      j).castStart (E.y_eq i).symm).castEnd (E.x_eq i).symm
  have hlength : ∀ i j,
      (core i j).length = 2 + j.val * 2 := by
    intro i j
    simp [core, Nat.mul_comm]
  have hdisjoint : ∀ i j,
      (outside.path i).walk.support.tail.Disjoint
        (core i j).walk.support.tail := by
    intro i j
    rw [List.disjoint_left]
    intro z hzOutside hzCore
    have hzCoreFull :
        z ∈ (core i j).walk.support :=
      List.mem_of_mem_tail hzCore
    have hzRange : z ∈ Set.range (setup.coreHom C) := by
      apply setup.sameCorePath_support_range C
        (E.yCore i) (E.xCore i)
        (E.toCoreEndpointSequence.core_endpoints_ne
          setup C outside i).symm
        (by
          rcases E.same i with h | h
          · exact Or.inl ⟨h.2, h.1⟩
          · exact Or.inr ⟨h.2, h.1⟩)
        j
      simpa [core] using hzCoreFull
    have hzEnds :=
      E.meets_core_only_at_ends i z
        (List.mem_of_mem_tail hzOutside) hzRange
    rcases hzEnds with hzx | hzy
    · exact (outside.path i).start_not_mem_tail
        (hzx ▸ hzOutside)
    · exact (core i j).start_not_mem_tail
        (hzy ▸ hzCore)
  exact PathSequenceCoreGrid.ofDisjointCorePaths
    B outside 2 2 (Or.inr rfl) core hlength hdisjoint

/--
Build the extended even core closures `2,4,...,2 rank` when the endpoint
side is strictly larger than the rank.
-/
noncomputable def sameLargerCoreGrid
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    (E : SameLargerCoreEndpointSequence setup C outside)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b) :
    PathSequenceCoreGrid B outside C.rank := by
  let core (i : Fin q) (j : Fin C.rank) :
      SimplePath B (outside.y i) (outside.x i) :=
    ((setup.sameLargerCorePath C
      (E.yCore i) (E.xCore i)
      (E.toCoreEndpointSequence.core_endpoints_ne
        setup C outside i).symm
      (by
        rcases E.same_larger i with h | h
        · exact Or.inl ⟨h.2.1, h.1, h.2.2⟩
        · exact Or.inr ⟨h.2.1, h.1, h.2.2⟩)
      hsafe j).castStart (E.y_eq i).symm).castEnd (E.x_eq i).symm
  have hlength : ∀ i j,
      (core i j).length = 2 + j.val * 2 := by
    intro i j
    simp [core, Nat.mul_comm]
  have hdisjoint : ∀ i j,
      (outside.path i).walk.support.tail.Disjoint
        (core i j).walk.support.tail := by
    intro i j
    rw [List.disjoint_left]
    intro z hzOutside hzCore
    have hzCoreFull :
        z ∈ (core i j).walk.support :=
      List.mem_of_mem_tail hzCore
    have hzRange : z ∈ Set.range (setup.coreHom C) := by
      apply setup.sameLargerCorePath_support_range C
        (E.yCore i) (E.xCore i)
        (E.toCoreEndpointSequence.core_endpoints_ne
          setup C outside i).symm
        (by
          rcases E.same_larger i with h | h
          · exact Or.inl ⟨h.2.1, h.1, h.2.2⟩
          · exact Or.inr ⟨h.2.1, h.1, h.2.2⟩)
        hsafe j
      simpa [core] using hzCoreFull
    have hzEnds :=
      E.meets_core_only_at_ends i z
        (List.mem_of_mem_tail hzOutside) hzRange
    rcases hzEnds with hzx | hzy
    · exact (outside.path i).start_not_mem_tail
        (hzx ▸ hzOutside)
    · exact (core i j).start_not_mem_tail
        (hzy ▸ hzCore)
  exact PathSequenceCoreGrid.ofDisjointCorePaths
    B outside 2 2 (Or.inr rfl) core hlength hdisjoint

/--
The opposite-part numerical cases of Lemma 6.3 after boundary lifting:
`q` outside paths and `rank` odd core paths, with `q + rank = 6`.
-/
theorem opposite_core_sequence_forces_divisible_cycle
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    (E : OppositeCoreEndpointSequence setup C outside)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (hq : 2 ≤ q)
    (hsix : q + C.rank = 6) :
    HasCycleDivisibleBy B 5 :=
  six_path_grid_forces_divisible_cycle B outside
    (setup.oppositeCoreGrid C outside E hsafe)
    hq C.two_le_rank hsix

/--
The same-part numerical cases of Lemma 6.3 after boundary lifting:
`q` outside paths and `rank-1` even core paths, with total six.
-/
theorem same_core_sequence_forces_divisible_cycle
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    (E : SameCoreEndpointSequence setup C outside)
    (hq : 2 ≤ q)
    (hrank : 3 ≤ C.rank)
    (hsix : q + (C.rank - 1) = 6) :
    HasCycleDivisibleBy B 5 :=
  six_path_grid_forces_divisible_cycle B outside
    (setup.sameCoreGrid C outside E)
    hq (by omega) hsix

/--
The exceptional same-part numerical case: `q` outside paths and `rank`
even core paths, including the terminal length `2 * rank`.
-/
theorem same_larger_core_sequence_forces_divisible_cycle
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    {q : ℕ}
    (outside : AdmissiblePathSequence B q)
    (E : SameLargerCoreEndpointSequence setup C outside)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (hq : 2 ≤ q)
    (hsix : q + C.rank = 6) :
    HasCycleDivisibleBy B 5 :=
  six_path_grid_forces_divisible_cycle B outside
    (setup.sameLargerCoreGrid C outside E hsafe)
    hq C.two_le_rank hsix

/--
One complete opposite-part invocation in the proof of Lemma 6.3: boundary
root lifting, endpoint replacement, BGLP core paths, simple-cycle
construction, and the six-to-five modular count.
-/
theorem opposite_boundary_core_case
    {U : Type*} [Fintype U] [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (q : ℕ) (H : SimpleGraph U) (D₀ Z : Finset U)
    (α β : U)
    (_hq : 1 ≤ q)
    (hαβ : α ≠ β)
    (hnotadj : ¬ H.Adj α β)
    (hconn : IsTwoConnected (H ⊔ edge α β))
    (hZD : Z ⊆ D₀)
    (hαZ : α ∉ Z) (hβZ : β ∉ Z)
    (hdeg : ∀ v, v ≠ α → v ≠ β → v ∉ Z →
      q + 1 ≤ finiteDegree H v)
    (hdegZ : ∀ z ∈ Z, q ≤ finiteDegree H z)
    (horder_one : Z.card = 1 → 4 ≤ Fintype.card U)
    (A : BoundaryRootAmbient H α β Z B c)
    (K : OppositeCoreBoundaryAmbient setup C A)
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (hqTwo : 2 ≤ q)
    (hsix : q + C.rank = 6) :
    HasCycleDivisibleBy B 5 := by
  have hqFour : q ≤ 4 := by
    have := C.two_le_rank
    omega
  obtain ⟨F, ⟨R⟩⟩ :=
    boundary_root_lifting_artificial_detailed
      q H D₀ Z α β hqTwo hqFour hαβ hnotadj hconn hZD hαZ hβZ
      hdeg hdegZ horder_one A
  exact setup.opposite_core_sequence_forces_divisible_cycle
    C (R.family A) (K.endpointSequence setup C A R) hsafe
    hqTwo hsix

/--
The same-part analogue of `opposite_boundary_core_case`, using the
`rank-1` even core paths.
-/
theorem same_boundary_core_case
    {U : Type*} [Fintype U] [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (q : ℕ) (H : SimpleGraph U) (D₀ Z : Finset U)
    (α β : U)
    (_hq : 1 ≤ q)
    (hαβ : α ≠ β)
    (hnotadj : ¬ H.Adj α β)
    (hconn : IsTwoConnected (H ⊔ edge α β))
    (hZD : Z ⊆ D₀)
    (hαZ : α ∉ Z) (hβZ : β ∉ Z)
    (hdeg : ∀ v, v ≠ α → v ≠ β → v ∉ Z →
      q + 1 ≤ finiteDegree H v)
    (hdegZ : ∀ z ∈ Z, q ≤ finiteDegree H z)
    (horder_one : Z.card = 1 → 4 ≤ Fintype.card U)
    (A : BoundaryRootAmbient H α β Z B c)
    (K : SameCoreBoundaryAmbient setup C A)
    (hqTwo : 2 ≤ q)
    (hrank : 3 ≤ C.rank)
    (hsix : q + (C.rank - 1) = 6) :
    HasCycleDivisibleBy B 5 := by
  have hqFour : q ≤ 4 := by
    omega
  obtain ⟨F, ⟨R⟩⟩ :=
    boundary_root_lifting_artificial_detailed
      q H D₀ Z α β hqTwo hqFour hαβ hnotadj hconn hZD hαZ hβZ
      hdeg hdegZ horder_one A
  exact setup.same_core_sequence_forces_divisible_cycle
    C (R.family A) (K.endpointSequence setup C A R)
    hqTwo hrank hsix

/--
The boundary-lifting composition for the special same-part clause in which
the endpoint side is larger than the core rank.
-/
theorem same_larger_boundary_core_case
    {U : Type*} [Fintype U] [DecidableEq U]
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (q : ℕ) (H : SimpleGraph U) (D₀ Z : Finset U)
    (α β : U)
    (_hq : 1 ≤ q)
    (hαβ : α ≠ β)
    (hnotadj : ¬ H.Adj α β)
    (hconn : IsTwoConnected (H ⊔ edge α β))
    (hZD : Z ⊆ D₀)
    (hαZ : α ∉ Z) (hβZ : β ∉ Z)
    (hdeg : ∀ v, v ≠ α → v ≠ β → v ∉ Z →
      q + 1 ≤ finiteDegree H v)
    (hdegZ : ∀ z ∈ Z, q ≤ finiteDegree H z)
    (horder_one : Z.card = 1 → 4 ≤ Fintype.card U)
    (A : BoundaryRootAmbient H α β Z B c)
    (K : SameCoreBoundaryAmbient setup C A)
    (hsameLarger :
      ∀ u v x y,
        (K.leftCore u x ∈ C.left ∧
          K.rightCore v y ∈ C.left ∧
          C.rank < C.left.card) ∨
        (K.leftCore u x ∈ C.right ∧
          K.rightCore v y ∈ C.right ∧
          C.rank < C.right.card))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (hqTwo : 2 ≤ q)
    (hsix : q + C.rank = 6) :
    HasCycleDivisibleBy B 5 := by
  have hqFour : q ≤ 4 := by
    have := C.two_le_rank
    omega
  obtain ⟨F, ⟨R⟩⟩ :=
    boundary_root_lifting_artificial_detailed
      q H D₀ Z α β hqTwo hqFour hαβ hnotadj hconn hZD hαZ hβZ
      hdeg hdegZ horder_one A
  let E₀ :=
    K.endpointSequence setup C A R
  let E :
      SameLargerCoreEndpointSequence
        setup C (R.family A) := {
    toCoreEndpointSequence :=
      E₀.toCoreEndpointSequence
    same_larger := by
      intro i
      exact hsameLarger
        (R.leftOld i) (R.rightOld i)
        ⟨(R.family A).x i, R.left_mem i⟩
        ⟨(R.family A).y i, R.right_mem i⟩
  }
  exact setup.same_larger_core_sequence_forces_divisible_cycle
    C (R.family A) E hsafe hqTwo hsix

/--
The both-parts branch of Lemma 6.3 after the concrete boundary/core model
has been built.  All root distinctness, deficiency membership, order,
connectivity, and the degree loss (6.4) are discharged here.
-/
theorem BoundaryCoreModel.opposite_case_contradiction_of_degree_bounds
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds)
    (K : OppositeCoreBoundaryAmbient setup C
      (M.boundaryAmbient setup C Q leftEnds rightEnds))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (hrhi : C.rank ≤ 4)
    (hdegreeBounds :
      ∀ w : (↑Q : Set W),
        (5 ≤ finiteDegree J w.1 →
          7 - C.rank ≤
            finiteDegree
              (boundaryAuxGraph J Q leftEnds rightEnds)
              (boundaryOldVertex Q w)) ∧
        (4 ≤ finiteDegree J w.1 →
          6 - C.rank ≤
            finiteDegree
              (boundaryAuxGraph J Q leftEnds rightEnds)
              (boundaryOldVertex Q w))) :
    False := by
  let H := boundaryAuxGraph J Q leftEnds rightEnds
  let Z := boundaryDeficient D Q
  let α := boundaryLeftRoot Q
  let β := boundaryRightRoot Q
  let q := 6 - C.rank
  have hrlo : 2 ≤ C.rank := C.two_le_rank
  have hqOne : 1 ≤ q := by
    dsimp [q]
    omega
  have hqTwo : 2 ≤ q := by
    dsimp [q]
    omega
  have hαβ : α ≠ β := by
    simp [α, β, boundaryLeftRoot, boundaryRightRoot]
  have hnotadj : ¬ H.Adj α β := by
    exact boundaryAuxGraph_roots_not_adjacent
      J Q leftEnds rightEnds
  have hconn : IsTwoConnected (H ⊔ edge α β) := by
    exact boundaryAuxGraph_add_roots_two_connected
      J Q leftEnds rightEnds M.connectivity
  have hαZ : α ∉ Z := by
    exact leftRoot_not_mem_boundaryDeficient D Q
  have hβZ : β ∉ Z := by
    exact rightRoot_not_mem_boundaryDeficient D Q
  have hdeg :
      ∀ v, v ≠ α → v ≠ β → v ∉ Z →
        q + 1 ≤ finiteDegree H v := by
    intro v hvα hvβ hvZ
    let vInterior :
        {z : BoundaryAuxVertex Q //
          z ≠ boundaryLeftRoot Q ∧
            z ≠ boundaryRightRoot Q} :=
      ⟨v, hvα, hvβ⟩
    let w := boundaryInteriorOld Q vInterior
    have hvOld :
        boundaryOldVertex Q w = v :=
      boundaryOldVertex_interior Q vInterior
    have hwD : w.1 ∉ D := by
      intro hwD
      apply hvZ
      rw [← hvOld]
      exact (mem_boundaryDeficient_old D Q w).2 hwD
    have hbounds := hdegreeBounds w
    have hregular :=
      hbounds.1 (setup.degree_regular w.1 hwD)
    dsimp [q, H]
    rw [← hvOld]
    omega
  have hdegZ :
      ∀ z ∈ Z, q ≤ finiteDegree H z := by
    intro z hz
    obtain ⟨w, hwD, hzw⟩ :=
      (mem_boundaryDeficient_iff D Q z).1 hz
    subst z
    have hbounds := hdegreeBounds w
    have hdeficient :=
      hbounds.2 (by
        rw [setup.degree_deficient w.1 hwD])
    exact hdeficient
  have horder :
      Z.card = 1 →
        4 ≤ Fintype.card (BoundaryAuxVertex Q) := by
    intro _
    have hQcard := M.connectivity.two_le_card
    have hQtype :
        Fintype.card (↑Q : Set W) = Q.card := by
      simp
    simp only [BoundaryAuxVertex, Fintype.card_option]
    rw [hQtype]
    omega
  have hsix : q + C.rank = 6 := by
    dsimp [q]
    omega
  have hcycle :=
    setup.opposite_boundary_core_case
      C q H Z Z α β hqOne hαβ hnotadj hconn
      Finset.Subset.rfl hαZ hβZ hdeg hdegZ horder
      (M.boundaryAmbient setup C Q leftEnds rightEnds)
      K hsafe hqTwo hsix
  exact setup.no_divisible_cycle hcycle

/--
The complete-boundary specialization of the opposite-part case.  Every
positive core degree is represented by at least one artificial root, so
the standard one-root loss estimate (6.4) supplies the degree certificate.
-/
theorem BoundaryCoreModel.opposite_case_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds)
    (K : OppositeCoreBoundaryAmbient setup C
      (M.boundaryAmbient setup C Q leftEnds rightEnds))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (hrhi : C.rank ≤ 4)
    (hcoreDegree :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1)
    (hrootWhenPositive :
      ∀ w : (↑Q : Set W),
        1 ≤ finiteBoundaryDegree J C.carrier w.1 →
          (leftEnds w).Nonempty ∨
            (rightEnds w).Nonempty) :
    False := by
  have hdegreeBounds :
      ∀ w : (↑Q : Set W),
        (5 ≤ finiteDegree J w.1 →
          7 - C.rank ≤
            finiteDegree
              (boundaryAuxGraph J Q leftEnds rightEnds)
              (boundaryOldVertex Q w)) ∧
        (4 ≤ finiteDegree J w.1 →
          6 - C.rank ≤
            finiteDegree
              (boundaryAuxGraph J Q leftEnds rightEnds)
              (boundaryOldVertex Q w)) := by
    intro w
    exact boundaryAux_degree_bound_one_root
      J C.carrier Q M.region leftEnds rightEnds
      w C.rank C.two_le_rank hrhi (hcoreDegree w)
      (hrootWhenPositive w)
  exact M.opposite_case_contradiction_of_degree_bounds
    setup C Q leftEnds rightEnds K hsafe hrhi hdegreeBounds

/--
The special same-part contradiction used when `rank = 2` and the endpoint
side has at least three vertices.  Its degree loss is still (6.4), while
the core supplies the extended even lengths through `2 * rank`.
-/
theorem BoundaryCoreModel.same_larger_case_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds)
    (K : SameCoreBoundaryAmbient setup C
      (M.boundaryAmbient setup C Q leftEnds rightEnds))
    (hsameLarger :
      ∀ u v x y,
        (K.leftCore u x ∈ C.left ∧
          K.rightCore v y ∈ C.left ∧
          C.rank < C.left.card) ∨
        (K.leftCore u x ∈ C.right ∧
          K.rightCore v y ∈ C.right ∧
          C.rank < C.right.card))
    (hsafe :
      3 ≤ C.rank ∨
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (hrhi : C.rank ≤ 4)
    (hcoreDegree :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1)
    (hrootWhenPositive :
      ∀ w : (↑Q : Set W),
        1 ≤ finiteBoundaryDegree J C.carrier w.1 →
          (leftEnds w).Nonempty ∨
            (rightEnds w).Nonempty) :
    False := by
  let H := boundaryAuxGraph J Q leftEnds rightEnds
  let Z := boundaryDeficient D Q
  let α := boundaryLeftRoot Q
  let β := boundaryRightRoot Q
  let q := 6 - C.rank
  have hqOne : 1 ≤ q := by
    dsimp [q]
    omega
  have hqTwo : 2 ≤ q := by
    dsimp [q]
    omega
  have hαβ : α ≠ β := by
    simp [α, β, boundaryLeftRoot, boundaryRightRoot]
  have hnotadj : ¬ H.Adj α β := by
    exact boundaryAuxGraph_roots_not_adjacent
      J Q leftEnds rightEnds
  have hconn : IsTwoConnected (H ⊔ edge α β) := by
    exact boundaryAuxGraph_add_roots_two_connected
      J Q leftEnds rightEnds M.connectivity
  have hαZ : α ∉ Z := by
    exact leftRoot_not_mem_boundaryDeficient D Q
  have hβZ : β ∉ Z := by
    exact rightRoot_not_mem_boundaryDeficient D Q
  have hdeg :
      ∀ v, v ≠ α → v ≠ β → v ∉ Z →
        q + 1 ≤ finiteDegree H v := by
    intro v hvα hvβ hvZ
    let vInterior :
        {z : BoundaryAuxVertex Q //
          z ≠ boundaryLeftRoot Q ∧
            z ≠ boundaryRightRoot Q} :=
      ⟨v, hvα, hvβ⟩
    let w := boundaryInteriorOld Q vInterior
    have hvOld :
        boundaryOldVertex Q w = v :=
      boundaryOldVertex_interior Q vInterior
    have hwD : w.1 ∉ D := by
      intro hwD
      apply hvZ
      rw [← hvOld]
      exact (mem_boundaryDeficient_old D Q w).2 hwD
    have hbounds :=
      boundaryAux_degree_bound_one_root
        J C.carrier Q M.region leftEnds rightEnds
        w C.rank C.two_le_rank hrhi (hcoreDegree w)
        (hrootWhenPositive w)
    have hregular :=
      hbounds.1 (setup.degree_regular w.1 hwD)
    dsimp [q, H]
    rw [← hvOld]
    omega
  have hdegZ :
      ∀ z ∈ Z, q ≤ finiteDegree H z := by
    intro z hz
    obtain ⟨w, hwD, hzw⟩ :=
      (mem_boundaryDeficient_iff D Q z).1 hz
    subst z
    have hbounds :=
      boundaryAux_degree_bound_one_root
        J C.carrier Q M.region leftEnds rightEnds
        w C.rank C.two_le_rank hrhi (hcoreDegree w)
        (hrootWhenPositive w)
    have hdeficient :=
      hbounds.2 (by
        rw [setup.degree_deficient w.1 hwD])
    exact hdeficient
  have horder :
      Z.card = 1 →
        4 ≤ Fintype.card (BoundaryAuxVertex Q) := by
    intro _
    have hQcard := M.connectivity.two_le_card
    have hQtype :
        Fintype.card (↑Q : Set W) = Q.card := by
      simp
    simp only [BoundaryAuxVertex, Fintype.card_option]
    rw [hQtype]
    omega
  have hsix : q + C.rank = 6 := by
    dsimp [q]
    omega
  have hcycle :=
    setup.same_larger_boundary_core_case
      C q H Z Z α β hqOne hαβ hnotadj hconn
      Finset.Subset.rfl hαZ hβZ hdeg hdegZ horder
      (M.boundaryAmbient setup C Q leftEnds rightEnds)
      K hsameLarger hsafe hqTwo hsix
  exact setup.no_divisible_cycle hcycle

/--
The one-part branch of Lemma 6.3 after the same-part boundary model is
built.  This is the complete formal counterpart of the two-root gain (6.5).
-/
theorem BoundaryCoreModel.same_case_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (leftEnds rightEnds : (↑Q : Set W) → Finset W)
    (M : BoundaryCoreModel setup C Q leftEnds rightEnds)
    (K : SameCoreBoundaryAmbient setup C
      (M.boundaryAmbient setup C Q leftEnds rightEnds))
    (hrlo : 3 ≤ C.rank)
    (hrhi : C.rank ≤ 4)
    (hcoreDegree :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1)
    (hreplaceSmall :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ 1 →
          finiteBoundaryDegree J C.carrier w.1 ≤
            (if (leftEnds w).Nonempty then 1 else 0) +
              (if (rightEnds w).Nonempty then 1 else 0))
    (hbothLarge :
      ∀ w : (↑Q : Set W),
        2 ≤ finiteBoundaryDegree J C.carrier w.1 →
          (leftEnds w).Nonempty ∧
            (rightEnds w).Nonempty) :
    False := by
  let H := boundaryAuxGraph J Q leftEnds rightEnds
  let Z := boundaryDeficient D Q
  let α := boundaryLeftRoot Q
  let β := boundaryRightRoot Q
  let q := 7 - C.rank
  have hqOne : 1 ≤ q := by
    dsimp [q]
    omega
  have hqTwo : 2 ≤ q := by
    dsimp [q]
    omega
  have hαβ : α ≠ β := by
    simp [α, β, boundaryLeftRoot, boundaryRightRoot]
  have hnotadj : ¬ H.Adj α β := by
    exact boundaryAuxGraph_roots_not_adjacent
      J Q leftEnds rightEnds
  have hconn : IsTwoConnected (H ⊔ edge α β) := by
    exact boundaryAuxGraph_add_roots_two_connected
      J Q leftEnds rightEnds M.connectivity
  have hαZ : α ∉ Z := by
    exact leftRoot_not_mem_boundaryDeficient D Q
  have hβZ : β ∉ Z := by
    exact rightRoot_not_mem_boundaryDeficient D Q
  have hdeg :
      ∀ v, v ≠ α → v ≠ β → v ∉ Z →
        q + 1 ≤ finiteDegree H v := by
    intro v hvα hvβ hvZ
    let vInterior :
        {z : BoundaryAuxVertex Q //
          z ≠ boundaryLeftRoot Q ∧
            z ≠ boundaryRightRoot Q} :=
      ⟨v, hvα, hvβ⟩
    let w := boundaryInteriorOld Q vInterior
    have hvOld :
        boundaryOldVertex Q w = v :=
      boundaryOldVertex_interior Q vInterior
    have hwD : w.1 ∉ D := by
      intro hwD
      apply hvZ
      rw [← hvOld]
      exact (mem_boundaryDeficient_old D Q w).2 hwD
    have hbounds :=
      boundaryAux_degree_bound_two_roots
        J C.carrier Q M.region leftEnds rightEnds
        w C.rank hrlo hrhi (hcoreDegree w)
        (hreplaceSmall w) (hbothLarge w)
    have hregular :=
      hbounds.1 (setup.degree_regular w.1 hwD)
    dsimp [q, H]
    rw [← hvOld]
    omega
  have hdegZ :
      ∀ z ∈ Z, q ≤ finiteDegree H z := by
    intro z hz
    obtain ⟨w, hwD, hzw⟩ :=
      (mem_boundaryDeficient_iff D Q z).1 hz
    subst z
    have hbounds :=
      boundaryAux_degree_bound_two_roots
        J C.carrier Q M.region leftEnds rightEnds
        w C.rank hrlo hrhi (hcoreDegree w)
        (hreplaceSmall w) (hbothLarge w)
    have hdeficient :=
      hbounds.2 (by
        rw [setup.degree_deficient w.1 hwD])
    exact hdeficient
  have horder :
      Z.card = 1 →
        4 ≤ Fintype.card (BoundaryAuxVertex Q) := by
    intro _
    have hQcard := M.connectivity.two_le_card
    have hQtype :
        Fintype.card (↑Q : Set W) = Q.card := by
      simp
    simp only [BoundaryAuxVertex, Fintype.card_option]
    rw [hQtype]
    omega
  have hsix :
      q + (C.rank - 1) = 6 := by
    dsimp [q]
    omega
  have hcycle :=
    setup.same_boundary_core_case
      C q H Z Z α β hqOne hαβ hnotadj hconn
      Finset.Subset.rfl hαZ hβZ hdeg hdegZ horder
      (M.boundaryAmbient setup C Q leftEnds rightEnds)
      K hqTwo hrlo hsix
  exact setup.no_divisible_cycle hcycle

/--
The complete-core subcase of the both-parts branch in Lemma 6.3.  The two
part-attachment edges are explicit, so Lean checks that their old endpoints
are distinct.
-/
theorem complete_core_component_both_parts_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (qLeft qRight : (↑Q : Set W))
    (x y : W)
    (hxLeft : x ∈ coreVertexSet C C.left)
    (hyRight : y ∈ coreVertexSet C C.right)
    (hqx : J.Adj qLeft.1 x)
    (hqy : J.Adj qRight.1 y)
    (hrootsDistinct : qLeft ≠ qRight)
    (hcross :
      ∀ x ∈ coreVertexSet C C.left,
        ∀ y ∈ coreVertexSet C C.right,
          J.Adj x y)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  let L := coreVertexSet C C.left
  let R := coreVertexSet C C.right
  let leftEnds := boundaryEndsIn J Q L
  let rightEnds := boundaryEndsIn J Q R
  have hLcore : L ⊆ C.carrier := by
    intro z hz
    exact ((mem_coreVertexSet C C.left z).1 hz).choose
  have hRcore : R ⊆ C.carrier := by
    intro z hz
    exact ((mem_coreVertexSet C C.right z).1 hz).choose
  have hLR : Disjoint L R := by
    exact disjoint_coreVertexSet C C.core.1
  have hdeleted :
      ∀ w : (↑Q : Set W),
        (J.induce
          {z | z ∉ insert w.1
            (C.carrier \ C.carrier)}).Connected := by
    apply deleted_boundary_connected_of_kConnected
      J C.carrier Q C.carrier 3 setup.three_connected
    simp
  have hrepresented :
      ∀ (a : (↑Q : Set W)) s,
        s ∈ C.carrier → J.Adj a.1 s →
          (leftEnds a).Nonempty ∨
            (rightEnds a).Nonempty := by
    intro a s hsC has
    let sC : (↑C.carrier : Set W) := ⟨s, hsC⟩
    have hsCover : sC ∈ C.left ∪ C.right := by
      rw [C.sides_cover]
      simp
    rcases Finset.mem_union.mp hsCover with hsLeft | hsRight
    · left
      apply boundaryEndsIn_nonempty_of_adj
        J Q L a
      · exact (mem_coreVertexSet C C.left s).2
          ⟨hsC, hsLeft⟩
      · exact has
    · right
      apply boundaryEndsIn_nonempty_of_adj
        J Q R a
      · exact (mem_coreVertexSet C C.right s).2
          ⟨hsC, hsRight⟩
      · exact has
  have hconnectivity :
      BoundaryAuxConnectivityData
        J Q leftEnds rightEnds := by
    have hleftNonempty :
        (leftEnds qLeft).Nonempty := by
      apply boundaryEndsIn_nonempty_of_adj J Q L qLeft
      · simpa [L] using hxLeft
      · exact hqx
    have hrightNonempty :
        (rightEnds qRight).Nonempty := by
      apply boundaryEndsIn_nonempty_of_adj J Q R qRight
      · simpa [R] using hyRight
      · exact hqy
    exact boundaryAuxConnectivityDataOfDeletedConnected
      J C.carrier Q C.carrier leftEnds rightEnds
      hregion Finset.Subset.rfl
      ⟨x, hLcore (by simpa [L] using hxLeft)⟩
      qLeft qRight hrootsDistinct
      hleftNonempty hrightNonempty
      hdeleted hrepresented
  let M : BoundaryCoreModel setup C Q leftEnds rightEnds :=
    BoundaryCoreModel.ofRepresentedSets
      setup C Q L R hLcore hRcore hLR
      hregion hconnectivity
  have hopposite :
      ∀ u v x y
        (hx : x ∈ leftEnds u) (hy : y ∈ rightEnds v),
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.right) ∨
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.right ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.left) := by
    intro u v x y hx hy
    left
    have hxL : x ∈ L :=
      ((mem_boundaryEndsIn J Q L u x).1 hx).1
    have hyR : y ∈ R :=
      ((mem_boundaryEndsIn J Q R v y).1 hy).1
    constructor
    · simpa using
        ((mem_coreVertexSet C C.left x).1 hxL).choose_spec
    · simpa using
        ((mem_coreVertexSet C C.right y).1 hyR).choose_spec
  have hadjacent :
      ∀ u v x y,
        x ∈ leftEnds u → y ∈ rightEnds v →
          J.Adj x y := by
    intro u v x y hx hy
    exact hcross x
      ((mem_boundaryEndsIn J Q L u x).1 hx).1
      y ((mem_boundaryEndsIn J Q R v y).1 hy).1
  let K :
      OppositeCoreBoundaryAmbient setup C
        (M.boundaryAmbient setup C Q leftEnds rightEnds) :=
    M.oppositeAmbient setup C Q leftEnds rightEnds
      hopposite hadjacent
  have hrootWhenPositive :
      ∀ w : (↑Q : Set W),
        1 ≤ finiteBoundaryDegree J C.carrier w.1 →
          (leftEnds w).Nonempty ∨
            (rightEnds w).Nonempty := by
    intro w hw
    obtain ⟨s, hsC, hws⟩ :=
      (finiteBoundaryDegree_pos_iff
        J C.carrier w.1).1 (by omega)
    exact hrepresented w s hsC hws
  exact M.opposite_case_contradiction
    setup C Q leftEnds rightEnds K
    (Or.inr (by
      intro a ha b hb
      exact hcross a.1
        ((mem_coreVertexSet C C.left a.1).2
          ⟨a.2, ha⟩)
        b.1
        ((mem_coreVertexSet C C.right b.1).2
          ⟨b.2, hb⟩)))
    hrhi
    houtside hrootWhenPositive

/--
The complete-core both-parts case with independence derived from
triangle-freeness.
-/
theorem complete_core_component_both_parts_contradiction_of_attachments
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (qLeft qRight : (↑Q : Set W))
    (x y : W)
    (hxLeft : x ∈ coreVertexSet C C.left)
    (hyRight : y ∈ coreVertexSet C C.right)
    (hqx : J.Adj qLeft.1 x)
    (hqy : J.Adj qRight.1 y)
    (hcross :
      ∀ x ∈ coreVertexSet C C.left,
        ∀ y ∈ coreVertexSet C C.right,
          J.Adj x y)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  have hxCore :=
    ((mem_coreVertexSet C C.left x).1 hxLeft).choose
  have hyCore :=
    ((mem_coreVertexSet C C.right y).1 hyRight).choose
  have hrootsDistinct :=
    setup.opposite_attachment_old_vertices_ne
      C Q hregion qLeft qRight x y
      hxCore hyCore (hcross x hxLeft y hyRight)
      hqx hqy
  exact setup.complete_core_component_both_parts_contradiction
    C Q hregion qLeft qRight x y hxLeft hyRight
    hqx hqy hrootsDistinct hcross hrhi houtside

/--
The `K⁻_{s,t}` subcase of the both-parts branch in Lemma 6.3.  The
missing-edge endpoint `yMissing` is deliberately omitted from the represented
right boundary.  Three-connectivity is applied after deleting that one
unrepresented core vertex and one old component vertex.  The special degree
estimate records that an old vertex receiving no root can then lose at most
the single edge to `yMissing`.
-/
theorem missing_edge_core_component_both_parts_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (yMissing : W)
    (hyMissingRight :
      yMissing ∈ coreVertexSet C C.right)
    (qLeft qRight : (↑Q : Set W))
    (x y : W)
    (hxLeft : x ∈ coreVertexSet C C.left)
    (hyRight : y ∈ coreVertexSet C C.right)
    (hyNotMissing : y ≠ yMissing)
    (hqx : J.Adj qLeft.1 x)
    (hqy : J.Adj qRight.1 y)
    (hrootsDistinct : qLeft ≠ qRight)
    (hcross :
      ∀ x ∈ coreVertexSet C C.left,
        ∀ y ∈ coreVertexSet C C.right,
          y ≠ yMissing → J.Adj x y)
    (hrlo : 3 ≤ C.rank)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  let L := coreVertexSet C C.left
  let Rfull := coreVertexSet C C.right
  let R := Rfull.erase yMissing
  let represented := C.carrier.erase yMissing
  let leftEnds := boundaryEndsIn J Q L
  let rightEnds := boundaryEndsIn J Q R
  have hLcore : L ⊆ C.carrier := by
    intro z hz
    exact ((mem_coreVertexSet C C.left z).1 hz).choose
  have hRfullCore : Rfull ⊆ C.carrier := by
    intro z hz
    exact ((mem_coreVertexSet C C.right z).1 hz).choose
  have hRcore : R ⊆ C.carrier := by
    intro z hz
    exact hRfullCore (Finset.mem_of_mem_erase hz)
  have hLRfull : Disjoint L Rfull := by
    exact disjoint_coreVertexSet C C.core.1
  have hLR : Disjoint L R := by
    exact hLRfull.mono_right (Finset.erase_subset _ _)
  have hyMissingCore : yMissing ∈ C.carrier :=
    hRfullCore (by simpa [Rfull] using hyMissingRight)
  have hxNotMissing : x ≠ yMissing := by
    intro hxy
    have hxL : x ∈ L := by
      simpa [L] using hxLeft
    have hyR : yMissing ∈ Rfull := by
      simpa [Rfull] using hyMissingRight
    exact Finset.disjoint_left.mp hLRfull
      hxL (hxy.symm ▸ hyR)
  have hrepresentedNonempty : represented.Nonempty := by
    exact ⟨x, Finset.mem_erase.mpr
      ⟨hxNotMissing, hLcore (by simpa [L] using hxLeft)⟩⟩
  have hdeleted :
      ∀ w : (↑Q : Set W),
        (J.induce
          {z | z ∉ insert w.1
            (C.carrier \ represented)}).Connected := by
    apply deleted_boundary_connected_of_kConnected
      J C.carrier Q represented 3 setup.three_connected
    have hdiff :
        C.carrier \ represented = {yMissing} := by
      ext z
      dsimp [represented]
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨hzCore, hzNot⟩
        by_contra hzNe
        exact hzNot (Finset.mem_erase.mpr
          ⟨hzNe, hzCore⟩)
      · intro hz
        subst z
        exact ⟨hyMissingCore, by simp⟩
    rw [hdiff]
    simp
  have hrepresented :
      ∀ (a : (↑Q : Set W)) s,
        s ∈ represented → J.Adj a.1 s →
          (leftEnds a).Nonempty ∨
            (rightEnds a).Nonempty := by
    intro a s hsRep has
    have hsCore : s ∈ C.carrier :=
      Finset.mem_of_mem_erase hsRep
    have hsNotMissing : s ≠ yMissing :=
      (Finset.mem_erase.mp hsRep).1
    let sC : (↑C.carrier : Set W) := ⟨s, hsCore⟩
    have hsCover : sC ∈ C.left ∪ C.right := by
      rw [C.sides_cover]
      simp
    rcases Finset.mem_union.mp hsCover with hsLeft | hsRight
    · left
      apply boundaryEndsIn_nonempty_of_adj J Q L a
      · exact (mem_coreVertexSet C C.left s).2
          ⟨hsCore, hsLeft⟩
      · exact has
    · right
      apply boundaryEndsIn_nonempty_of_adj J Q R a
      · apply Finset.mem_erase.mpr
        exact ⟨hsNotMissing,
          (mem_coreVertexSet C C.right s).2
            ⟨hsCore, hsRight⟩⟩
      · exact has
  have hleftWitness :
      (leftEnds qLeft).Nonempty := by
    apply boundaryEndsIn_nonempty_of_adj J Q L qLeft
    · simpa [L] using hxLeft
    · exact hqx
  have hrightWitness :
      (rightEnds qRight).Nonempty := by
    apply boundaryEndsIn_nonempty_of_adj J Q R qRight
    · exact Finset.mem_erase.mpr
        ⟨hyNotMissing, by simpa [Rfull] using hyRight⟩
    · exact hqy
  have hconnectivity :
      BoundaryAuxConnectivityData
        J Q leftEnds rightEnds :=
    boundaryAuxConnectivityDataOfDeletedConnected
      J C.carrier Q represented leftEnds rightEnds
      hregion (Finset.erase_subset _ _)
      hrepresentedNonempty
      qLeft qRight hrootsDistinct
      hleftWitness hrightWitness
      hdeleted hrepresented
  let M : BoundaryCoreModel setup C Q leftEnds rightEnds :=
    BoundaryCoreModel.ofRepresentedSets
      setup C Q L R hLcore hRcore hLR
      hregion hconnectivity
  have hopposite :
      ∀ u v x y
        (hx : x ∈ leftEnds u) (hy : y ∈ rightEnds v),
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.right) ∨
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.right ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.left) := by
    intro u v x' y' hx hy
    left
    have hxL : x' ∈ L :=
      ((mem_boundaryEndsIn J Q L u x').1 hx).1
    have hyR : y' ∈ R :=
      ((mem_boundaryEndsIn J Q R v y').1 hy).1
    constructor
    · simpa using
        ((mem_coreVertexSet C C.left x').1 hxL).choose_spec
    · have hyRfull : y' ∈ Rfull :=
        Finset.mem_of_mem_erase hyR
      simpa using
        ((mem_coreVertexSet C C.right y').1 hyRfull).choose_spec
  have hadjacent :
      ∀ u v x y,
        x ∈ leftEnds u → y ∈ rightEnds v →
          J.Adj x y := by
    intro u v x' y' hx hy
    have hxL :=
      ((mem_boundaryEndsIn J Q L u x').1 hx).1
    have hyR :=
      ((mem_boundaryEndsIn J Q R v y').1 hy).1
    exact hcross x' hxL y'
      (Finset.mem_of_mem_erase hyR)
      (Finset.mem_erase.mp hyR).1
  let K :
      OppositeCoreBoundaryAmbient setup C
        (M.boundaryAmbient setup C Q leftEnds rightEnds) :=
    M.oppositeAmbient setup C Q leftEnds rightEnds
      hopposite hadjacent
  have hrootWhenTwo :
      ∀ w : (↑Q : Set W),
        2 ≤ finiteBoundaryDegree J C.carrier w.1 →
          (leftEnds w).Nonempty ∨
            (rightEnds w).Nonempty := by
    intro w hw
    obtain ⟨s, hsCore, hws, hsNotMissing⟩ :=
      exists_boundary_neighbor_ne_of_two_le
        J C.carrier w.1 yMissing hw
    have hsRep : s ∈ represented :=
      Finset.mem_erase.mpr ⟨hsNotMissing, hsCore⟩
    exact hrepresented w s hsRep hws
  have hdegreeBounds :
      ∀ w : (↑Q : Set W),
        (5 ≤ finiteDegree J w.1 →
          7 - C.rank ≤
            finiteDegree
              (boundaryAuxGraph J Q leftEnds rightEnds)
              (boundaryOldVertex Q w)) ∧
        (4 ≤ finiteDegree J w.1 →
          6 - C.rank ≤
            finiteDegree
              (boundaryAuxGraph J Q leftEnds rightEnds)
              (boundaryOldVertex Q w)) := by
    intro w
    exact boundaryAux_degree_bound_missing_endpoint
      J C.carrier Q hregion leftEnds rightEnds
      w C.rank hrlo hrhi (houtside w)
      (hrootWhenTwo w)
  exact M.opposite_case_contradiction_of_degree_bounds
    setup C Q leftEnds rightEnds K (Or.inl hrlo)
      hrhi hdegreeBounds

/--
The missing-edge both-parts case with old-endpoint independence derived
from triangle-freeness.
-/
theorem missing_edge_core_component_both_parts_contradiction_of_attachments
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (yMissing : W)
    (hyMissingRight :
      yMissing ∈ coreVertexSet C C.right)
    (qLeft qRight : (↑Q : Set W))
    (x y : W)
    (hxLeft : x ∈ coreVertexSet C C.left)
    (hyRight : y ∈ coreVertexSet C C.right)
    (hyNotMissing : y ≠ yMissing)
    (hqx : J.Adj qLeft.1 x)
    (hqy : J.Adj qRight.1 y)
    (hcross :
      ∀ x ∈ coreVertexSet C C.left,
        ∀ y ∈ coreVertexSet C C.right,
          y ≠ yMissing → J.Adj x y)
    (hrlo : 3 ≤ C.rank)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  have hxCore :=
    ((mem_coreVertexSet C C.left x).1 hxLeft).choose
  have hyCore :=
    ((mem_coreVertexSet C C.right y).1 hyRight).choose
  have hxy := hcross x hxLeft y hyRight hyNotMissing
  have hrootsDistinct :=
    setup.opposite_attachment_old_vertices_ne
      C Q hregion qLeft qRight x y
      hxCore hyCore hxy hqx hqy
  exact setup.missing_edge_core_component_both_parts_contradiction
    C Q hregion yMissing hyMissingRight
    qLeft qRight x y hxLeft hyRight hyNotMissing
    hqx hqy hrootsDistinct hcross hrlo hrhi houtside

/--
The one-part branch of Lemma 6.3 with the paper's adaptive `T₁,T₂` endpoint
sets.  The distinct-end selection is provided by
`adaptive_boundary_ends_distinct`, including the possible `u = v` case.
-/
theorem same_part_component_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q T T₁ T₂ : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (hTcore : T ⊆ C.carrier)
    (hparts : T₁ ∪ T₂ = T)
    (hpartsDisjoint : Disjoint T₁ T₂)
    (q₁ q₂ : (↑Q : Set W))
    (y₁ y₂ : W)
    (hy₁ : y₁ ∈ T₁) (hy₂ : y₂ ∈ T₂)
    (hq₁ : J.Adj q₁.1 y₁)
    (hq₂ : J.Adj q₂.1 y₂)
    (hrootsDistinct : q₁ ≠ q₂)
    (honlyT :
      ∀ (w : (↑Q : Set W)) s,
        s ∈ C.carrier → J.Adj w.1 s → s ∈ T)
    (hTsame :
      ∀ y (hy : y ∈ T),
        (⟨y, hTcore hy⟩ :
          (↑C.carrier : Set W)) ∈ C.right)
    (hrlo : 3 ≤ C.rank)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  let leftEnds :=
    adaptiveLeftBoundaryEnds J Q T T₁
  let rightEnds :=
    adaptiveRightBoundaryEnds J Q T T₂
  have hT₁T : T₁ ⊆ T := by
    intro z hz
    rw [← hparts]
    exact Finset.mem_union_left T₂ hz
  have hT₂T : T₂ ⊆ T := by
    intro z hz
    rw [← hparts]
    exact Finset.mem_union_right T₁ hz
  have hleft_mem_T :
      ∀ (w : (↑Q : Set W)) x,
        x ∈ leftEnds w → x ∈ T := by
    intro w x hx
    by_cases hlarge :
        2 ≤ (boundaryEndsIn J Q T w).card
    · exact ((mem_boundaryEndsIn J Q T w x).1
        (by
          simpa [leftEnds, adaptiveLeftBoundaryEnds,
            hlarge] using hx)).1
    · exact hT₁T
        (((mem_boundaryEndsIn J Q T₁ w x).1
          (by
            simpa [leftEnds, adaptiveLeftBoundaryEnds,
              hlarge] using hx)).1)
  have hright_mem_T :
      ∀ (w : (↑Q : Set W)) y,
        y ∈ rightEnds w → y ∈ T := by
    intro w y hy
    by_cases hlarge :
        2 ≤ (boundaryEndsIn J Q T w).card
    · exact ((mem_boundaryEndsIn J Q T w y).1
        (by
          simpa [rightEnds, adaptiveRightBoundaryEnds,
            hlarge] using hy)).1
    · exact hT₂T
        (((mem_boundaryEndsIn J Q T₂ w y).1
          (by
            simpa [rightEnds, adaptiveRightBoundaryEnds,
              hlarge] using hy)).1)
  have hleft_adj :
      ∀ (w : (↑Q : Set W)) x,
        x ∈ leftEnds w → J.Adj w.1 x := by
    intro w x hx
    by_cases hlarge :
        2 ≤ (boundaryEndsIn J Q T w).card
    · exact ((mem_boundaryEndsIn J Q T w x).1
        (by
          simpa [leftEnds, adaptiveLeftBoundaryEnds,
            hlarge] using hx)).2
    · exact ((mem_boundaryEndsIn J Q T₁ w x).1
        (by
          simpa [leftEnds, adaptiveLeftBoundaryEnds,
            hlarge] using hx)).2
  have hright_adj :
      ∀ (w : (↑Q : Set W)) y,
        y ∈ rightEnds w → J.Adj w.1 y := by
    intro w y hy
    by_cases hlarge :
        2 ≤ (boundaryEndsIn J Q T w).card
    · exact ((mem_boundaryEndsIn J Q T w y).1
        (by
          simpa [rightEnds, adaptiveRightBoundaryEnds,
            hlarge] using hy)).2
    · exact ((mem_boundaryEndsIn J Q T₂ w y).1
        (by
          simpa [rightEnds, adaptiveRightBoundaryEnds,
            hlarge] using hy)).2
  have hdeleted :
      ∀ w : (↑Q : Set W),
        (J.induce
          {z | z ∉ insert w.1
            (C.carrier \ C.carrier)}).Connected := by
    apply deleted_boundary_connected_of_kConnected
      J C.carrier Q C.carrier 3 setup.three_connected
    simp
  have hrepresented :
      ∀ (a : (↑Q : Set W)) s,
        s ∈ C.carrier → J.Adj a.1 s →
          (leftEnds a).Nonempty ∨
            (rightEnds a).Nonempty := by
    intro a s hsC has
    have hsT := honlyT a s hsC has
    by_cases hlarge :
        2 ≤ (boundaryEndsIn J Q T a).card
    · have hall :
          (boundaryEndsIn J Q T a).Nonempty :=
        boundaryEndsIn_nonempty_of_adj J Q T a hsT has
      exact Or.inl (by
        simpa [leftEnds, adaptiveLeftBoundaryEnds,
          hlarge] using hall)
    · have hsParts : s ∈ T₁ ∪ T₂ := by
        rw [hparts]
        exact hsT
      rcases Finset.mem_union.mp hsParts with hs₁ | hs₂
      · exact Or.inl (by
          have hnon :=
            boundaryEndsIn_nonempty_of_adj
              J Q T₁ a hs₁ has
          simpa [leftEnds, adaptiveLeftBoundaryEnds,
            hlarge] using hnon)
      · exact Or.inr (by
          have hnon :=
            boundaryEndsIn_nonempty_of_adj
              J Q T₂ a hs₂ has
          simpa [rightEnds, adaptiveRightBoundaryEnds,
            hlarge] using hnon)
  have hleftWitness :
      (leftEnds q₁).Nonempty := by
    have hy₁T := hT₁T hy₁
    by_cases hlarge :
        2 ≤ (boundaryEndsIn J Q T q₁).card
    · have hnon :=
        boundaryEndsIn_nonempty_of_adj
          J Q T q₁ hy₁T hq₁
      simpa [leftEnds, adaptiveLeftBoundaryEnds,
        hlarge] using hnon
    · have hnon :=
        boundaryEndsIn_nonempty_of_adj
          J Q T₁ q₁ hy₁ hq₁
      simpa [leftEnds, adaptiveLeftBoundaryEnds,
        hlarge] using hnon
  have hrightWitness :
      (rightEnds q₂).Nonempty := by
    have hy₂T := hT₂T hy₂
    by_cases hlarge :
        2 ≤ (boundaryEndsIn J Q T q₂).card
    · have hnon :=
        boundaryEndsIn_nonempty_of_adj
          J Q T q₂ hy₂T hq₂
      simpa [rightEnds, adaptiveRightBoundaryEnds,
        hlarge] using hnon
    · have hnon :=
        boundaryEndsIn_nonempty_of_adj
          J Q T₂ q₂ hy₂ hq₂
      simpa [rightEnds, adaptiveRightBoundaryEnds,
        hlarge] using hnon
  have hconnectivity :
      BoundaryAuxConnectivityData
        J Q leftEnds rightEnds :=
    boundaryAuxConnectivityDataOfDeletedConnected
      J C.carrier Q C.carrier leftEnds rightEnds
      hregion Finset.Subset.rfl
      ⟨y₁, hTcore (hT₁T hy₁)⟩
      q₁ q₂ hrootsDistinct hleftWitness hrightWitness
      hdeleted hrepresented
  let M : BoundaryCoreModel setup C Q leftEnds rightEnds := {
    region := hregion
    connectivity := hconnectivity
    left_in_core := by
      intro w x hx
      exact hTcore (hleft_mem_T w x hx)
    right_in_core := by
      intro w y hy
      exact hTcore (hright_mem_T w y hy)
    left_adjacent := by
      intro w x hx
      exact (hleft_adj w x hx).symm
    right_adjacent := hright_adj
    distinct_ends := by
      intro u v hu hv
      exact adaptive_boundary_ends_distinct
        J Q T T₁ T₂ hpartsDisjoint u v
        (by simpa [leftEnds] using hu)
        (by simpa [rightEnds] using hv)
  }
  have hsame :
      ∀ u v x y
        (hx : x ∈ leftEnds u) (hy : y ∈ rightEnds v),
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.left) ∨
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.right ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.right) := by
    intro u v x y hx hy
    right
    constructor
    · simpa using hTsame x (hleft_mem_T u x hx)
    · simpa using hTsame y (hright_mem_T v y hy)
  let K :
      SameCoreBoundaryAmbient setup C
        (M.boundaryAmbient setup C Q leftEnds rightEnds) :=
    M.sameAmbient setup C Q leftEnds rightEnds hsame
  have hdegreeEq :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 =
          (boundaryEndsIn J Q T w).card := by
    intro w
    have hset :
        J.neighborSet w.1 ∩
            (↑C.carrier : Set W) =
          (↑(boundaryEndsIn J Q T w) : Set W) := by
      ext s
      constructor
      · rintro ⟨hws, hsC⟩
        exact (mem_boundaryEndsIn J Q T w s).2
          ⟨honlyT w s hsC hws, hws⟩
      · intro hs
        have hs' :=
          (mem_boundaryEndsIn J Q T w s).1 hs
        exact ⟨hs'.2, hTcore hs'.1⟩
    unfold finiteBoundaryDegree
    rw [hset, Set.ncard_coe_finset]
  have hreplaceSmall :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ 1 →
          finiteBoundaryDegree J C.carrier w.1 ≤
            (if (leftEnds w).Nonempty then 1 else 0) +
              (if (rightEnds w).Nonempty then 1 else 0) := by
    intro w hsmall
    rw [hdegreeEq w] at hsmall ⊢
    by_cases hzero :
        (boundaryEndsIn J Q T w).card = 0
    · omega
    · have hone :
          (boundaryEndsIn J Q T w).card = 1 := by
        omega
      obtain ⟨s, hs⟩ :
          (boundaryEndsIn J Q T w).Nonempty :=
        Finset.card_pos.mp (by omega)
      have hsT :=
        ((mem_boundaryEndsIn J Q T w s).1 hs).1
      have hsParts : s ∈ T₁ ∪ T₂ := by
        rw [hparts]
        exact hsT
      have hnotLarge :
          ¬ 2 ≤ (boundaryEndsIn J Q T w).card := by
        omega
      rcases Finset.mem_union.mp hsParts with hs₁ | hs₂
      · have hleft :
            (leftEnds w).Nonempty := by
          have hnon :=
            boundaryEndsIn_nonempty_of_adj
              J Q T₁ w hs₁
              ((mem_boundaryEndsIn J Q T w s).1 hs).2
          simpa [leftEnds, adaptiveLeftBoundaryEnds,
            hnotLarge] using hnon
        rw [hone]
        simp [hleft]
      · have hright :
            (rightEnds w).Nonempty := by
          have hnon :=
            boundaryEndsIn_nonempty_of_adj
              J Q T₂ w hs₂
              ((mem_boundaryEndsIn J Q T w s).1 hs).2
          simpa [rightEnds, adaptiveRightBoundaryEnds,
            hnotLarge] using hnon
        rw [hone]
        simp [hright]
  have hbothLarge :
      ∀ w : (↑Q : Set W),
        2 ≤ finiteBoundaryDegree J C.carrier w.1 →
          (leftEnds w).Nonempty ∧
            (rightEnds w).Nonempty := by
    intro w hlarge
    rw [hdegreeEq w] at hlarge
    have hall :
        (boundaryEndsIn J Q T w).Nonempty :=
      Finset.card_pos.mp (by omega)
    constructor
    · simpa [leftEnds, adaptiveLeftBoundaryEnds,
        hlarge] using hall
    · simpa [rightEnds, adaptiveRightBoundaryEnds,
        hlarge] using hall
  exact M.same_case_contradiction
    setup C Q leftEnds rightEnds K hrlo hrhi
    houtside hreplaceSmall hbothLarge

/--
The one-part subcase of the rank-two branch (`r = 2`).  Unlike the general
same-part case, the two endpoint sets are the fixed partition `T₁,T₂`, every
old vertex loses at most one core edge, and the larger endpoint side supplies
the exceptional BGLP length-four path.
-/
theorem rank_two_same_part_component_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q T T₁ T₂ : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (hTcore : T ⊆ C.carrier)
    (hparts : T₁ ∪ T₂ = T)
    (hpartsDisjoint : Disjoint T₁ T₂)
    (q₁ q₂ : (↑Q : Set W))
    (y₁ y₂ : W)
    (hy₁ : y₁ ∈ T₁) (hy₂ : y₂ ∈ T₂)
    (hq₁ : J.Adj q₁.1 y₁)
    (hq₂ : J.Adj q₂.1 y₂)
    (hrootsDistinct : q₁ ≠ q₂)
    (honlyT :
      ∀ (w : (↑Q : Set W)) s,
        s ∈ C.carrier → J.Adj w.1 s → s ∈ T)
    (hTsame :
      ∀ y (hy : y ∈ T),
        (⟨y, hTcore hy⟩ :
          (↑C.carrier : Set W)) ∈ C.right)
    (hrank : C.rank = 2)
    (hsideLarger : C.rank < C.right.card)
    (hcomplete :
      ∀ a ∈ C.left, ∀ b ∈ C.right,
        (J.induce (↑C.carrier : Set W)).Adj a b)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  let L := T₁
  let R := T₂
  let leftEnds := boundaryEndsIn J Q L
  let rightEnds := boundaryEndsIn J Q R
  have hT₁T : T₁ ⊆ T := by
    intro z hz
    rw [← hparts]
    exact Finset.mem_union_left T₂ hz
  have hT₂T : T₂ ⊆ T := by
    intro z hz
    rw [← hparts]
    exact Finset.mem_union_right T₁ hz
  have hLcore : L ⊆ C.carrier := by
    intro z hz
    exact hTcore (hT₁T (by simpa [L] using hz))
  have hRcore : R ⊆ C.carrier := by
    intro z hz
    exact hTcore (hT₂T (by simpa [R] using hz))
  have hLR : Disjoint L R := by
    simpa [L, R] using hpartsDisjoint
  have hdeleted :
      ∀ w : (↑Q : Set W),
        (J.induce
          {z | z ∉ insert w.1
            (C.carrier \ C.carrier)}).Connected := by
    apply deleted_boundary_connected_of_kConnected
      J C.carrier Q C.carrier 3 setup.three_connected
    simp
  have hrepresented :
      ∀ (a : (↑Q : Set W)) s,
        s ∈ C.carrier → J.Adj a.1 s →
          (leftEnds a).Nonempty ∨
            (rightEnds a).Nonempty := by
    intro a s hsCore has
    have hsT := honlyT a s hsCore has
    have hsParts : s ∈ T₁ ∪ T₂ := by
      rw [hparts]
      exact hsT
    rcases Finset.mem_union.mp hsParts with hs₁ | hs₂
    · left
      apply boundaryEndsIn_nonempty_of_adj J Q L a
      · simpa [L] using hs₁
      · exact has
    · right
      apply boundaryEndsIn_nonempty_of_adj J Q R a
      · simpa [R] using hs₂
      · exact has
  have hleftWitness :
      (leftEnds q₁).Nonempty := by
    apply boundaryEndsIn_nonempty_of_adj J Q L q₁
    · simpa [L] using hy₁
    · exact hq₁
  have hrightWitness :
      (rightEnds q₂).Nonempty := by
    apply boundaryEndsIn_nonempty_of_adj J Q R q₂
    · simpa [R] using hy₂
    · exact hq₂
  have hconnectivity :
      BoundaryAuxConnectivityData
        J Q leftEnds rightEnds :=
    boundaryAuxConnectivityDataOfDeletedConnected
      J C.carrier Q C.carrier leftEnds rightEnds
      hregion Finset.Subset.rfl
      ⟨y₁, hTcore (hT₁T hy₁)⟩
      q₁ q₂ hrootsDistinct
      hleftWitness hrightWitness
      hdeleted hrepresented
  let M : BoundaryCoreModel setup C Q leftEnds rightEnds :=
    BoundaryCoreModel.ofRepresentedSets
      setup C Q L R hLcore hRcore hLR
      hregion hconnectivity
  have hsame :
      ∀ u v x y
        (hx : x ∈ leftEnds u) (hy : y ∈ rightEnds v),
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.left) ∨
        ((⟨x, M.left_in_core u x hx⟩ :
            (↑C.carrier : Set W)) ∈ C.right ∧
          (⟨y, M.right_in_core v y hy⟩ :
            (↑C.carrier : Set W)) ∈ C.right) := by
    intro u v x y hx hy
    right
    have hxL : x ∈ L :=
      ((mem_boundaryEndsIn J Q L u x).1 hx).1
    have hyR : y ∈ R :=
      ((mem_boundaryEndsIn J Q R v y).1 hy).1
    constructor
    · simpa using hTsame x
        (hT₁T (by simpa [L] using hxL))
    · simpa using hTsame y
        (hT₂T (by simpa [R] using hyR))
  let K :
      SameCoreBoundaryAmbient setup C
        (M.boundaryAmbient setup C Q leftEnds rightEnds) :=
    M.sameAmbient setup C Q leftEnds rightEnds hsame
  have hsameLarger :
      ∀ u v x y,
        (K.leftCore u x ∈ C.left ∧
          K.rightCore v y ∈ C.left ∧
          C.rank < C.left.card) ∨
        (K.leftCore u x ∈ C.right ∧
          K.rightCore v y ∈ C.right ∧
          C.rank < C.right.card) := by
    intro u v x y
    right
    let x' :
        {x : V //
          x ∈ setup.mappedBoundaryEnds Q leftEnds u} :=
      ⟨x.1, by
        exact x.2⟩
    let y' :
        {y : V //
          y ∈ setup.mappedBoundaryEnds Q rightEnds v} :=
      ⟨y.1, by
        exact y.2⟩
    have hx :=
      coreVertexOfMappedEnds_mem setup C Q leftEnds
        M.left_in_core u x'
    have hy :=
      coreVertexOfMappedEnds_mem setup C Q rightEnds
        M.right_in_core v y'
    have hs :=
      hsame
        (boundaryInteriorOld Q u)
        (boundaryInteriorOld Q v)
        (coreVertexOfMappedEnds setup C Q leftEnds
          M.left_in_core u x').1
        (coreVertexOfMappedEnds setup C Q rightEnds
          M.right_in_core v y').1
        hx hy
    rcases hs with hs | hs
    · exact False.elim
        (Finset.disjoint_left.mp C.core.1
          hs.1
          (by
            have hcover :
                K.leftCore u x ∈ C.right := by
              simpa [K, BoundaryCoreModel.sameAmbient,
                BoundaryCoreModel.coreBoundaryAmbient,
                x'] using
                (hTsame
                  (coreVertexOfMappedEnds setup C Q leftEnds
                    M.left_in_core u x').1
                  (hT₁T (by
                    have hxL :=
                      ((mem_boundaryEndsIn J Q L
                        (boundaryInteriorOld Q u)
                        (coreVertexOfMappedEnds setup C Q leftEnds
                          M.left_in_core u x').1).1 hx).1
                    simpa [L] using hxL)))
            exact hcover))
    · refine ⟨?_, ?_, hsideLarger⟩
      · simpa [K, BoundaryCoreModel.sameAmbient,
          BoundaryCoreModel.coreBoundaryAmbient, x', y'] using hs.1
      · simpa [K, BoundaryCoreModel.sameAmbient,
          BoundaryCoreModel.coreBoundaryAmbient, x', y'] using hs.2
  have hrootWhenPositive :
      ∀ w : (↑Q : Set W),
        1 ≤ finiteBoundaryDegree J C.carrier w.1 →
          (leftEnds w).Nonempty ∨
            (rightEnds w).Nonempty := by
    intro w hw
    obtain ⟨s, hsCore, hws⟩ :=
      (finiteBoundaryDegree_pos_iff
        J C.carrier w.1).1 (by omega)
    exact hrepresented w s hsCore hws
  exact M.same_larger_case_contradiction
    setup C Q leftEnds rightEnds K hsameLarger
    (Or.inr hcomplete)
    (by omega) houtside hrootWhenPositive

/--
The one-part branch with the attachment matching and the `T₁,T₂` partition
derived internally.  The rank-two branch is routed to the exceptional
length-four core theorem; ranks three and four use the adaptive two-root
construction.
-/
theorem same_part_component_contradiction_of_connectivity
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q T : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (hTcore : T ⊆ C.carrier)
    (hTcard : 2 ≤ T.card)
    (honlyT :
      ∀ (w : (↑Q : Set W)) s,
        s ∈ C.carrier → J.Adj w.1 s → s ∈ T)
    (hTsame :
      ∀ y (hy : y ∈ T),
        (⟨y, hTcore hy⟩ :
          (↑C.carrier : Set W)) ∈ C.right)
    (hrhi : C.rank ≤ 4)
    (hsideLargerAtTwo :
      C.rank = 2 → C.rank < C.right.card)
    (hrankTwoComplete :
      C.rank = 2 →
        ∀ a ∈ C.left, ∀ b ∈ C.right,
          (J.induce (↑C.carrier : Set W)).Adj a b)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  have hQcard : 2 ≤ Q.card := by
    apply hregion.two_le_card_of_min_degree_four
      J C.carrier Q
    · intro w _
      exact setup.degree_at_least_four w
    · intro w
      have hw := houtside w
      omega
  have htwo : IsKConnected J 2 := by
    constructor
    · have horder := setup.three_connected.1
      omega
    · intro X hX
      exact setup.three_connected.2 X (by omega)
  have hregionT : ComponentRegion J T Q := {
    nonempty := hregion.nonempty
    disjoint := by
      apply Finset.disjoint_left.mpr
      intro q hqQ hqT
      exact hregion.not_mem_separator hqQ
        (hTcore hqT)
    connected := hregion.connected
    closed := by
      intro u v huQ huv hvT
      by_cases hvCore : v ∈ C.carrier
      · exact False.elim
          (hvT (honlyT ⟨u, huQ⟩ v hvCore huv))
      · exact hregion.closed huQ huv hvCore
  }
  obtain ⟨q₁, q₂, y₁, y₂,
      hy₁T, hy₂T, hq₁q₂, hy₁y₂, hq₁, hq₂⟩ :=
    hregionT.exists_independent_boundary_edges
      htwo hQcard hTcard
  let T₁ : Finset W := {y₁}
  let T₂ : Finset W := T.erase y₁
  have hparts : T₁ ∪ T₂ = T := by
    ext z
    simp [T₁, T₂, hy₁T]
  have hpartsDisjoint : Disjoint T₁ T₂ := by
    simp [T₁, T₂]
  have hy₁T₁ : y₁ ∈ T₁ := by
    simp [T₁]
  have hy₂T₂ : y₂ ∈ T₂ := by
    exact Finset.mem_erase.mpr
      ⟨hy₁y₂.symm, hy₂T⟩
  by_cases hrankTwo : C.rank = 2
  · exact setup.rank_two_same_part_component_contradiction
      C Q T T₁ T₂ hregion hTcore
      hparts hpartsDisjoint q₁ q₂ y₁ y₂
      hy₁T₁ hy₂T₂ hq₁ hq₂ hq₁q₂
      honlyT hTsame hrankTwo
      (hsideLargerAtTwo hrankTwo)
      (hrankTwoComplete hrankTwo) houtside
  · have hrlo : 3 ≤ C.rank := by
      have := C.two_le_rank
      omega
    exact setup.same_part_component_contradiction
      C Q T T₁ T₂ hregion hTcore
      hparts hpartsDisjoint q₁ q₂ y₁ y₂
      hy₁T₁ hy₂T₂ hq₁ hq₂ hq₁q₂
      honlyT hTsame hrlo hrhi houtside

/--
All component cases for a complete bipartite core.  Whether the component
meets both sides, only the right side, or only the left side is decided
internally.  The left-only case is reduced by swapping the core sides.
-/
theorem complete_core_component_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (hcross :
      ∀ x ∈ coreVertexSet C C.left,
        ∀ y ∈ coreVertexSet C C.right,
          J.Adj x y)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  let L := coreVertexSet C C.left
  let R := coreVertexSet C C.right
  have hLcore : L ⊆ C.carrier := by
    intro x hx
    exact ((mem_coreVertexSet C C.left x).1 hx).choose
  have hRcore : R ⊆ C.carrier := by
    intro y hy
    exact ((mem_coreVertexSet C C.right y).1 hy).choose
  have hLR : Disjoint L R := by
    exact disjoint_coreVertexSet C C.core.1
  have hLcard : 2 ≤ L.card := by
    rw [card_coreVertexSet]
    have hmin := Nat.min_le_left C.left.card C.right.card
    exact C.two_le_rank.trans hmin
  have hRcard : 2 ≤ R.card := by
    rw [card_coreVertexSet]
    have hmin := Nat.min_le_right C.left.card C.right.card
    exact C.two_le_rank.trans hmin
  let meetsLeft : Prop :=
    ∃ q : (↑Q : Set W), ∃ x ∈ L, J.Adj q.1 x
  let meetsRight : Prop :=
    ∃ q : (↑Q : Set W), ∃ y ∈ R, J.Adj q.1 y
  have hsideLarger
      (T U : Finset W)
      (hTcore : T ⊆ C.carrier)
      (hTU : Disjoint T U)
      (hUcore : U ⊆ C.carrier)
      (hTcard : 2 ≤ T.card)
      (honlyT :
        ∀ (w : (↑Q : Set W)) s,
          s ∈ C.carrier → J.Adj w.1 s → s ∈ T)
      (hUnonempty : U.Nonempty) :
      C.rank = 2 → C.rank < T.card := by
    intro hrank
    have hregionT : ComponentRegion J T Q := {
      nonempty := hregion.nonempty
      disjoint := by
        apply Finset.disjoint_left.mpr
        intro q hqQ hqT
        exact hregion.not_mem_separator hqQ
          (hTcore hqT)
      connected := hregion.connected
      closed := by
        intro u v huQ huv hvT
        by_cases hvCore : v ∈ C.carrier
        · exact False.elim
            (hvT (honlyT ⟨u, huQ⟩ v hvCore huv))
        · exact hregion.closed huQ huv hvCore
    }
    obtain ⟨z, hzU⟩ := hUnonempty
    have hzQ : z ∉ Q := by
      intro hzQ
      exact hregion.not_mem_separator hzQ
        (hUcore hzU)
    have hzT : z ∉ T := by
      exact fun hzT =>
        Finset.disjoint_left.mp hTU hzT hzU
    have hthree :
        3 ≤ T.card :=
      hregionT.connectivity_le_separator_card
        setup.three_connected hzQ hzT
    omega
  by_cases hleft : meetsLeft
  · by_cases hright : meetsRight
    · obtain ⟨qLeft, x, hxL, hqx⟩ := hleft
      obtain ⟨qRight, y, hyR, hqy⟩ := hright
      exact setup.complete_core_component_both_parts_contradiction_of_attachments
        C Q hregion qLeft qRight x y
        (by simpa [L] using hxL)
        (by simpa [R] using hyR)
        hqx hqy hcross hrhi houtside
    · have honlyL :
          ∀ (w : (↑Q : Set W)) s,
            s ∈ C.carrier → J.Adj w.1 s → s ∈ L := by
        intro w s hsCore hws
        let sC : (↑C.carrier : Set W) :=
          ⟨s, hsCore⟩
        have hsCover : sC ∈ C.left ∪ C.right := by
          rw [C.sides_cover]
          simp
        rcases Finset.mem_union.mp hsCover with hsL | hsR
        · exact (mem_coreVertexSet C C.left s).2
            ⟨hsCore, hsL⟩
        · exact False.elim (hright
            ⟨w, s,
              (mem_coreVertexSet C C.right s).2
                ⟨hsCore, hsR⟩, hws⟩)
      have hside :
          C.rank = 2 → C.rank < C.left.card := by
        intro hrank
        have hlarge :=
          hsideLarger L R hLcore hLR hRcore hLcard
            honlyL (Finset.card_pos.mp (by omega)) hrank
        simpa [L] using hlarge
      have hregionSwap :
          ComponentRegion J C.swap.carrier Q := by
        simpa [BipartiteCore.swap] using hregion
      have hLcoreSwap :
          L ⊆ C.swap.carrier := by
        simpa [BipartiteCore.swap] using hLcore
      have honlySwap :
          ∀ (w : (↑Q : Set W)) s,
            s ∈ C.swap.carrier →
              J.Adj w.1 s → s ∈ L := by
        simpa [BipartiteCore.swap] using honlyL
      have hLsameSwap :
          ∀ x (hx : x ∈ L),
            (⟨x, hLcoreSwap hx⟩ :
              (↑C.swap.carrier : Set W)) ∈ C.swap.right := by
        intro x hx
        have hx' :=
          ((mem_coreVertexSet C C.left x).1
            (by simpa [L] using hx)).choose_spec
        change
          (⟨x, hLcoreSwap hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left
        convert hx' using 1
      exact setup.same_part_component_contradiction_of_connectivity
        C.swap Q L hregionSwap hLcoreSwap hLcard
        honlySwap hLsameSwap
        (by simpa using hrhi)
        (by
          intro hrankSwap
          rw [BipartiteCore.rank_swap] at hrankSwap ⊢
          exact hside hrankSwap)
        (by
          intro _ a ha b hb
          change b ∈ C.left at hb
          change a ∈ C.right at ha
          change J.Adj a.1 b.1
          exact (hcross b.1
            ((mem_coreVertexSet C C.left b.1).2
              ⟨b.2, hb⟩)
            a.1
            ((mem_coreVertexSet C C.right a.1).2
              ⟨a.2, ha⟩)).symm)
        (by
          intro w
          change
            finiteBoundaryDegree J C.carrier w.1 ≤
              C.swap.rank - 1
          rw [BipartiteCore.rank_swap]
          exact houtside w)
  · by_cases hright : meetsRight
    · have honlyR :
          ∀ (w : (↑Q : Set W)) s,
            s ∈ C.carrier → J.Adj w.1 s → s ∈ R := by
        intro w s hsCore hws
        let sC : (↑C.carrier : Set W) :=
          ⟨s, hsCore⟩
        have hsCover : sC ∈ C.left ∪ C.right := by
          rw [C.sides_cover]
          simp
        rcases Finset.mem_union.mp hsCover with hsL | hsR
        · exact False.elim (hleft
            ⟨w, s,
              (mem_coreVertexSet C C.left s).2
                ⟨hsCore, hsL⟩, hws⟩)
        · exact (mem_coreVertexSet C C.right s).2
            ⟨hsCore, hsR⟩
      have hRsame :
          ∀ y (hy : y ∈ R),
            (⟨y, hRcore hy⟩ :
              (↑C.carrier : Set W)) ∈ C.right := by
        intro y hy
        exact ((mem_coreVertexSet C C.right y).1
          (by simpa [R] using hy)).choose_spec
      have hside :
          C.rank = 2 → C.rank < C.right.card := by
        intro hrank
        have hlarge :=
          hsideLarger R L hRcore hLR.symm hLcore hRcard
            honlyR (Finset.card_pos.mp (by omega)) hrank
        simpa [R] using hlarge
      exact setup.same_part_component_contradiction_of_connectivity
        C Q R hregion hRcore hRcard honlyR hRsame
        hrhi hside
        (by
          intro _ a ha b hb
          exact hcross a.1
            ((mem_coreVertexSet C C.left a.1).2
              ⟨a.2, ha⟩)
            b.1
            ((mem_coreVertexSet C C.right b.1).2
              ⟨b.2, hb⟩))
        houtside
    · have hQcard : 2 ≤ Q.card := by
        apply hregion.two_le_card_of_min_degree_four
          J C.carrier Q
        · intro w _
          exact setup.degree_at_least_four w
        · intro w
          have hw := houtside w
          omega
      have hcarrierCard : 2 ≤ C.carrier.card := by
        have hsub :
            C.left.card ≤
              (Finset.univ :
                Finset (↑C.carrier : Set W)).card :=
          Finset.card_le_card (Finset.subset_univ C.left)
        simpa using C.two_le_rank.trans
          (Nat.le_trans
            (Nat.min_le_left C.left.card C.right.card)
            hsub)
      have htwo : IsKConnected J 2 := by
        constructor
        · have := setup.three_connected.1
          omega
        · intro X hX
          exact setup.three_connected.2 X (by omega)
      obtain ⟨q₁, -, s₁, -, hs₁Core, -, -, -, hq₁s₁, -⟩ :=
        hregion.exists_independent_boundary_edges
          htwo hQcard hcarrierCard
      let sC : (↑C.carrier : Set W) :=
        ⟨s₁, hs₁Core⟩
      have hsCover : sC ∈ C.left ∪ C.right := by
        rw [C.sides_cover]
        simp
      rcases Finset.mem_union.mp hsCover with hsL | hsR
      · exact hleft ⟨q₁, s₁,
          (mem_coreVertexSet C C.left s₁).2
            ⟨hs₁Core, hsL⟩, hq₁s₁⟩
      · exact hright ⟨q₁, s₁,
          (mem_coreVertexSet C C.right s₁).2
            ⟨hs₁Core, hsR⟩, hq₁s₁⟩

/--
All component cases for a one-missing-edge core of rank at least three.
Three-connectivity first produces an attachment outside the two missing
endpoints.  If that attachment lies on the opposite orientation, the core
and its missing-edge data are swapped.
-/
theorem missing_core_component_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (M : C.MissingEdgeData)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (hrlo : 3 ≤ C.rank)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  let L := coreVertexSet C C.left
  let R := coreVertexSet C C.right
  have hLcore : L ⊆ C.carrier := by
    intro x hx
    exact ((mem_coreVertexSet C C.left x).1 hx).choose
  have hRcore : R ⊆ C.carrier := by
    intro y hy
    exact ((mem_coreVertexSet C C.right y).1 hy).choose
  have hLR : Disjoint L R := by
    exact disjoint_coreVertexSet C C.core.1
  have hLcard : 2 ≤ L.card := by
    rw [card_coreVertexSet]
    exact C.two_le_rank.trans
      (Nat.min_le_left C.left.card C.right.card)
  have hRcard : 2 ≤ R.card := by
    rw [card_coreVertexSet]
    exact C.two_le_rank.trans
      (Nat.min_le_right C.left.card C.right.card)
  have houtsideAttachment :
      ∃ q : (↑Q : Set W), ∃ s ∈ C.carrier,
        s ≠ M.xMissing ∧ s ≠ M.yMissing ∧
          J.Adj q.1 s := by
    by_contra hnone
    have honlyPair :
        ∀ (w : (↑Q : Set W)) s,
          s ∈ C.carrier → J.Adj w.1 s →
            s ∈ ({M.xMissing, M.yMissing} : Finset W) := by
      intro w s hsCore hws
      by_contra hsPair
      have hsx : s ≠ M.xMissing := by
        intro hsx
        apply hsPair
        simp [hsx]
      have hsy : s ≠ M.yMissing := by
        intro hsy
        apply hsPair
        simp [hsy]
      apply hnone
      exact ⟨w, s, hsCore, hsx, hsy, hws⟩
    let Z : Finset W := {M.xMissing, M.yMissing}
    have hZcore : Z ⊆ C.carrier := by
      intro z hz
      simp only [Z, Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ((mem_coreVertexSet C C.left
          M.xMissing).1 M.x_left).choose
      · exact ((mem_coreVertexSet C C.right
          M.yMissing).1 M.y_right).choose
    have hregionZ : ComponentRegion J Z Q := {
      nonempty := hregion.nonempty
      disjoint := by
        apply Finset.disjoint_left.mpr
        intro q hqQ hqZ
        exact hregion.not_mem_separator hqQ
          (hZcore hqZ)
      connected := hregion.connected
      closed := by
        intro u v huQ huv hvZ
        by_cases hvCore : v ∈ C.carrier
        · exact False.elim
            (hvZ (honlyPair ⟨u, huQ⟩ v hvCore huv))
        · exact hregion.closed huQ huv hvCore
    }
    have hErasePos :
        0 < (L.erase M.xMissing).card := by
      rw [Finset.card_erase_of_mem
        (by simpa [L] using M.x_left)]
      omega
    obtain ⟨z, hzErase⟩ :=
      Finset.card_pos.mp hErasePos
    have hzL : z ∈ L :=
      Finset.mem_of_mem_erase hzErase
    have hzx : z ≠ M.xMissing :=
      (Finset.mem_erase.mp hzErase).1
    have hzy : z ≠ M.yMissing := by
      intro hzy
      exact Finset.disjoint_left.mp hLR
        hzL (hzy ▸ (by simpa [R] using M.y_right))
    have hzQ : z ∉ Q := by
      intro hzQ
      exact hregion.not_mem_separator hzQ
        (hLcore hzL)
    have hzZ : z ∉ Z := by
      simp [Z, hzx, hzy]
    have hthree :
        3 ≤ Z.card :=
      hregionZ.connectivity_le_separator_card
        setup.three_connected hzQ hzZ
    have hZcard : Z.card ≤ 2 := by
      simpa [Z] using
        (Finset.card_le_two :
          ({M.xMissing, M.yMissing} : Finset W).card ≤ 2)
    omega
  obtain ⟨qOutside, sOutside, hsCore,
      hsNotX, hsNotY, hqOutside⟩ :=
    houtsideAttachment
  let sC : (↑C.carrier : Set W) :=
    ⟨sOutside, hsCore⟩
  have hsCover : sC ∈ C.left ∪ C.right := by
    rw [C.sides_cover]
    simp
  have hsSide :
      sOutside ∈ L ∨ sOutside ∈ R := by
    rcases Finset.mem_union.mp hsCover with hsL | hsR
    · exact Or.inl
        ((mem_coreVertexSet C C.left sOutside).2
          ⟨hsCore, hsL⟩)
    · exact Or.inr
        ((mem_coreVertexSet C C.right sOutside).2
          ⟨hsCore, hsR⟩)
  let meetsLeft : Prop :=
    ∃ q : (↑Q : Set W), ∃ x ∈ L, J.Adj q.1 x
  let meetsRight : Prop :=
    ∃ q : (↑Q : Set W), ∃ y ∈ R, J.Adj q.1 y
  by_cases hleft : meetsLeft
  · by_cases hright : meetsRight
    · obtain ⟨qLeft, x, hxL, hqx⟩ := hleft
      obtain ⟨qRight, y, hyR, hqy⟩ := hright
      rcases hsSide with hsL | hsR
      · let C' := C.swap
        let M' : C'.MissingEdgeData := M.swap
        have hregion' :
            ComponentRegion J C'.carrier Q := by
          simpa [C', BipartiteCore.swap] using hregion
        have hqLeftMem :
            y ∈ coreVertexSet C' C'.left := by
          simpa [C', BipartiteCore.swap,
            coreVertexSet, R] using hyR
        have hqRightMem :
            sOutside ∈ coreVertexSet C' C'.right := by
          simpa [C', BipartiteCore.swap,
            coreVertexSet, L] using hsL
        have hMissingMem :
            M.xMissing ∈
              coreVertexSet C' C'.right := by
          simpa [C', M', BipartiteCore.swap,
            coreVertexSet] using M.x_left
        exact setup.missing_edge_core_component_both_parts_contradiction_of_attachments
          C' Q hregion' M'.yMissing M'.y_right
          qRight qOutside y sOutside
          hqLeftMem hqRightMem
          (by
            change sOutside ≠ M.xMissing
            exact hsNotX)
          hqy hqOutside M'.cross_except
          (by simpa [C'] using hrlo)
          (by simpa [C'] using hrhi)
          (by
            intro w
            change
              finiteBoundaryDegree J C.carrier w.1 ≤
                C'.rank - 1
            simpa [C'] using houtside w)
      · exact setup.missing_edge_core_component_both_parts_contradiction_of_attachments
          C Q hregion M.yMissing M.y_right
          qLeft qOutside x sOutside
          (by simpa [L] using hxL)
          (by simpa [R] using hsR)
          hsNotY hqx hqOutside M.cross_except
          hrlo hrhi houtside
    · have honlyL :
          ∀ (w : (↑Q : Set W)) s,
            s ∈ C.carrier → J.Adj w.1 s → s ∈ L := by
        intro w s hsCore' hws
        let t : (↑C.carrier : Set W) :=
          ⟨s, hsCore'⟩
        have htCover : t ∈ C.left ∪ C.right := by
          rw [C.sides_cover]
          simp
        rcases Finset.mem_union.mp htCover with hsL | hsR
        · exact (mem_coreVertexSet C C.left s).2
            ⟨hsCore', hsL⟩
        · exact False.elim (hright
            ⟨w, s,
              (mem_coreVertexSet C C.right s).2
                ⟨hsCore', hsR⟩, hws⟩)
      let C' := C.swap
      have hregion' :
          ComponentRegion J C'.carrier Q := by
        simpa [C', BipartiteCore.swap] using hregion
      have hLcore' : L ⊆ C'.carrier := by
        simpa [C', BipartiteCore.swap] using hLcore
      have honlyL' :
          ∀ (w : (↑Q : Set W)) s,
            s ∈ C'.carrier → J.Adj w.1 s → s ∈ L := by
        simpa [C', BipartiteCore.swap] using honlyL
      have hLsame :
          ∀ x (hx : x ∈ L),
            (⟨x, hLcore' hx⟩ :
              (↑C'.carrier : Set W)) ∈ C'.right := by
        intro x hx
        have hx' :=
          ((mem_coreVertexSet C C.left x).1
            (by simpa [L] using hx)).choose_spec
        change
          (⟨x, hLcore' hx⟩ :
            (↑C.carrier : Set W)) ∈ C.left
        convert hx' using 1
      exact setup.same_part_component_contradiction_of_connectivity
        C' Q L hregion' hLcore' hLcard
        honlyL' hLsame
        (by simpa [C'] using hrhi)
        (by intro h; have : C.rank = 2 := by
              simpa [C'] using h
            omega)
        (by
          intro h
          have : C.rank = 2 := by
            simpa [C'] using h
          omega)
        (by
          intro w
          change
            finiteBoundaryDegree J C.carrier w.1 ≤
              C'.rank - 1
          simpa [C'] using houtside w)
  · by_cases hright : meetsRight
    · have honlyR :
          ∀ (w : (↑Q : Set W)) s,
            s ∈ C.carrier → J.Adj w.1 s → s ∈ R := by
        intro w s hsCore' hws
        let t : (↑C.carrier : Set W) :=
          ⟨s, hsCore'⟩
        have htCover : t ∈ C.left ∪ C.right := by
          rw [C.sides_cover]
          simp
        rcases Finset.mem_union.mp htCover with hsL | hsR
        · exact False.elim (hleft
            ⟨w, s,
              (mem_coreVertexSet C C.left s).2
                ⟨hsCore', hsL⟩, hws⟩)
        · exact (mem_coreVertexSet C C.right s).2
            ⟨hsCore', hsR⟩
      have hRsame :
          ∀ y (hy : y ∈ R),
            (⟨y, hRcore hy⟩ :
              (↑C.carrier : Set W)) ∈ C.right := by
        intro y hy
        exact ((mem_coreVertexSet C C.right y).1
          (by simpa [R] using hy)).choose_spec
      exact setup.same_part_component_contradiction_of_connectivity
        C Q R hregion hRcore hRcard
        honlyR hRsame hrhi
        (by intro h; omega)
        (by intro h; omega)
        houtside
    · rcases hsSide with hsL | hsR
      · exact hleft
          ⟨qOutside, sOutside, hsL, hqOutside⟩
      · exact hright
          ⟨qOutside, sOutside, hsR, hqOutside⟩

/--
Component form of the lifted core lemma for every rank from two through
four.  The only extra input isolates the minimality step in the paper:
a rank-two candidate must already be complete.  Complete rank-two cores are
handled by the exceptional same-part construction above, while a genuine
missing edge forces the rank to be at least three.
-/
theorem normalized_core_component_contradiction_of_rank_two_complete
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (hrlo : 2 ≤ C.rank)
    (hrhi : C.rank ≤ 4)
    (hrankTwoComplete :
      C.rank = 2 →
        ∀ x ∈ coreVertexSet C C.left,
          ∀ y ∈ coreVertexSet C C.right,
            J.Adj x y)
    (houtside :
      ∀ w : (↑Q : Set W),
        finiteBoundaryDegree J C.carrier w.1 ≤ C.rank - 1) :
    False := by
  classical
  rcases C.complete_or_missing with hcomplete | hmissing
  · exact setup.complete_core_component_contradiction
      C Q hregion hcomplete hrhi houtside
  · let M : C.MissingEdgeData :=
      Classical.choice hmissing
    have hrankNeTwo : C.rank ≠ 2 := by
      intro hrank
      exact M.missing_not_adjacent
        (hrankTwoComplete hrank
          M.xMissing M.x_left M.yMissing M.y_right)
    exact setup.missing_core_component_contradiction
      C M Q hregion (by omega) hrhi houtside

/--
The component contradiction for a globally minimal bounded core.  The
rank-two completeness premise of the previous theorem is now discharged by
the verified missing-endpoint deletion argument.
-/
theorem minimal_bounded_core_component_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (Q : Finset W)
    (hregion : ComponentRegion J C.carrier Q)
    (hrhi : C.rank ≤ 4)
    (houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1)
    (hminimal :
      ∀ C' : BipartiteCore J,
        (∀ w, w ∉ C'.carrier →
          finiteBoundaryDegree J C'.carrier w ≤
            C'.rank - 1) →
        C.carrier.card ≤ C'.carrier.card) :
    False := by
  have hrankTwoComplete :
      C.rank = 2 →
        ∀ x ∈ coreVertexSet C C.left,
          ∀ y ∈ coreVertexSet C C.right,
            J.Adj x y := by
    intro hrank
    exact BipartiteCore.rank_two_complete_of_minimal
      C hrank houtside hminimal
  exact setup.normalized_core_component_contradiction_of_rank_two_complete
    C Q hregion C.two_le_rank hrhi hrankTwoComplete
    (by
      intro w
      exact houtside w.1
        (hregion.not_mem_separator w.2))

/--
A minimum-order bounded core is impossible.  The complement component is
now an actual connected component of `J - C.carrier`, rather than an
abstract nonempty region supplied as a premise.
-/
theorem minimal_bounded_core_contradiction
    (setup : StandingSetup J B c D)
    (C : BipartiteCore J)
    (houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1)
    (hminimal :
      ∀ C' : BipartiteCore J,
        (∀ w, w ∉ C'.carrier →
          finiteBoundaryDegree J C'.carrier w ≤
            C'.rank - 1) →
        C.carrier.card ≤ C'.carrier.card) :
    False := by
  classical
  have hrhi : C.rank ≤ 4 :=
    setup.core_rank_le_four C
  have hproper : C.carrier ≠ Finset.univ :=
    setup.core_carrier_ne_univ C hrhi
  have houtsideVertex :
      ∃ w : W, w ∉ C.carrier := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    exact hproper
      (Finset.eq_univ_of_forall hnone)
  obtain ⟨w, hw⟩ := houtsideVertex
  let w' : {z : W // z ∉ C.carrier} :=
    ⟨w, hw⟩
  let K :=
    SimpleGraph.connectedComponentMk
      (deleteVertices J C.carrier) w'
  let Q :=
    componentVertices J C.carrier K
  have hregion :
      ComponentRegion J C.carrier Q :=
    componentRegion_componentVertices
      J C.carrier K
  exact setup.minimal_bounded_core_component_contradiction
    C Q hregion hrhi houtside hminimal

/--
Paper Lemma 6.3 in contradiction form under `StandingSetup`.
Starting from any member of the complete-bipartite-core family satisfying
the global outside-neighbor bound, well-ordering selects the minimum-order
candidate and the preceding internal proof yields the forbidden cycle.
-/
theorem lifted_core_contradiction
    (setup : StandingSetup J B c D)
    (C₀ : BipartiteCore J)
    (houtside :
      ∀ w, w ∉ C₀.carrier →
        finiteBoundaryDegree J C₀.carrier w ≤
          C₀.rank - 1) :
    False := by
  obtain ⟨C, hCoutside, hminimal⟩ :=
    BipartiteCore.exists_minimal_bounded_core
      C₀ houtside
  exact setup.minimal_bounded_core_contradiction
    C hCoutside hminimal

/--
Triangle-freeness upgrades a complete bipartite subgraph on raw sides to an
exact induced complete bipartite graph on their union.
-/
theorem complete_pair_adj_iff
    (setup : StandingSetup J B c D)
    (L R : Finset W)
    (hLR : Disjoint L R)
    (hLnonempty : L.Nonempty)
    (hRnonempty : R.Nonempty)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (u v : W)
    (hu : u ∈ L ∪ R)
    (hv : v ∈ L ∪ R) :
    J.Adj u v ↔
      (u ∈ L ∧ v ∈ R) ∨
        (u ∈ R ∧ v ∈ L) := by
  constructor
  · intro huv
    rcases Finset.mem_union.mp hu with huL | huR
    · rcases Finset.mem_union.mp hv with hvL | hvR
      · obtain ⟨z, hzR⟩ := hRnonempty
        have huz : J.Adj u z :=
          hcross u huL z hzR
        have hvz : J.Adj v z :=
          hcross v hvL z hzR
        exact False.elim (setup.no_triangle ⟨{
          p := u
          q := v
          r := z
          p_ne_q := huv.ne
          p_ne_r := by
            intro huzEq
            exact Finset.disjoint_left.mp hLR
              huL (huzEq ▸ hzR)
          q_ne_r := by
            intro hvzEq
            exact Finset.disjoint_left.mp hLR
              hvL (hvzEq ▸ hzR)
          pq := huv
          qr := hvz
          rp := huz.symm
        }⟩)
      · exact Or.inl ⟨huL, hvR⟩
    · rcases Finset.mem_union.mp hv with hvL | hvR
      · exact Or.inr ⟨huR, hvL⟩
      · obtain ⟨z, hzL⟩ := hLnonempty
        have hzu : J.Adj z u :=
          hcross z hzL u huR
        have hzv : J.Adj z v :=
          hcross z hzL v hvR
        exact False.elim (setup.no_triangle ⟨{
          p := u
          q := v
          r := z
          p_ne_q := huv.ne
          p_ne_r := by
            intro huzEq
            exact Finset.disjoint_left.mp hLR
              (huzEq ▸ hzL) huR
          q_ne_r := by
            intro hvzEq
            exact Finset.disjoint_left.mp hLR
              (hvzEq ▸ hzL) hvR
          pq := huv
          qr := hzv.symm
          rp := hzu
        }⟩)
  · rintro (⟨huL, hvR⟩ | ⟨huR, hvL⟩)
    · exact hcross u huL v hvR
    · exact (hcross v hvL u huR).symm

/--
Triangle-freeness likewise upgrades a raw near-complete bipartite pair to
the exact induced graph with its designated cross-edge deleted.
-/
theorem almost_pair_adj_iff
    (setup : StandingSetup J B c D)
    (L R : Finset W)
    (xMissing yMissing : W)
    (hLR : Disjoint L R)
    (hxMissing : xMissing ∈ L)
    (hyMissing : yMissing ∈ R)
    (hLtwo : 2 ≤ L.card)
    (hRtwo : 2 ≤ R.card)
    (hcrossExcept :
      ∀ x ∈ L, ∀ y ∈ R,
        x ≠ xMissing ∨ y ≠ yMissing →
          J.Adj x y)
    (hmissing : ¬J.Adj xMissing yMissing)
    (u v : W)
    (hu : u ∈ L ∪ R)
    (hv : v ∈ L ∪ R) :
    J.Adj u v ↔
      ((u ∈ L ∧ v ∈ R) ∨
        (u ∈ R ∧ v ∈ L)) ∧
      ¬((u = xMissing ∧ v = yMissing) ∨
        (u = yMissing ∧ v = xMissing)) := by
  constructor
  · intro huv
    rcases Finset.mem_union.mp hu with huL | huR
    · rcases Finset.mem_union.mp hv with hvL | hvR
      · obtain ⟨z, hzR, hzy⟩ :=
          R.exists_mem_ne (by omega) yMissing
        have huz : J.Adj u z :=
          hcrossExcept u huL z hzR (Or.inr hzy)
        have hvz : J.Adj v z :=
          hcrossExcept v hvL z hzR (Or.inr hzy)
        exact False.elim (setup.no_triangle ⟨{
          p := u
          q := v
          r := z
          p_ne_q := huv.ne
          p_ne_r := by
            intro huzEq
            exact Finset.disjoint_left.mp hLR
              huL (huzEq ▸ hzR)
          q_ne_r := by
            intro hvzEq
            exact Finset.disjoint_left.mp hLR
              hvL (hvzEq ▸ hzR)
          pq := huv
          qr := hvz
          rp := huz.symm
        }⟩)
      · refine ⟨Or.inl ⟨huL, hvR⟩, ?_⟩
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hmissing huv
        · exact Finset.disjoint_left.mp hLR
            huL hyMissing
    · rcases Finset.mem_union.mp hv with hvL | hvR
      · refine ⟨Or.inr ⟨huR, hvL⟩, ?_⟩
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact Finset.disjoint_left.mp hLR
            hxMissing huR
        · exact hmissing huv.symm
      · obtain ⟨z, hzL, hzx⟩ :=
          L.exists_mem_ne (by omega) xMissing
        have hzu : J.Adj z u :=
          hcrossExcept z hzL u huR (Or.inl hzx)
        have hzv : J.Adj z v :=
          hcrossExcept z hzL v hvR (Or.inl hzx)
        exact False.elim (setup.no_triangle ⟨{
          p := u
          q := v
          r := z
          p_ne_q := huv.ne
          p_ne_r := by
            intro huzEq
            exact Finset.disjoint_left.mp hLR
              (huzEq ▸ hzL) huR
          q_ne_r := by
            intro hvzEq
            exact Finset.disjoint_left.mp hLR
              (hvzEq ▸ hzL) hvR
          pq := huv
          qr := hzv.symm
          rp := hzu
        }⟩)
  · rintro ⟨(⟨huL, hvR⟩ | ⟨huR, hvL⟩),
      hnotMissing⟩
    · apply hcrossExcept u huL v hvR
      by_cases hux : u = xMissing
      · right
        intro hvy
        exact hnotMissing (Or.inl ⟨hux, hvy⟩)
      · exact Or.inl hux
    · apply (hcrossExcept v hvL u huR ?_).symm
      by_cases hvx : v = xMissing
      · right
        intro huy
        exact hnotMissing (Or.inr ⟨huy, hvx⟩)
      · exact Or.inl hvx

/--
An outside vertex cannot meet both sides of a complete bipartite pair in
the triangle-free standing graph.
-/
theorem outside_not_meet_both_complete_pair
    (setup : StandingSetup J B c D)
    (L R : Finset W)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (w x y : W)
    (hxL : x ∈ L) (hyR : y ∈ R)
    (hwx : J.Adj w x) (hwy : J.Adj w y) :
    False := by
  have hxy := hcross x hxL y hyR
  exact setup.no_triangle ⟨{
    p := w
    q := x
    r := y
    p_ne_q := hwx.ne
    p_ne_r := hwy.ne
    q_ne_r := hxy.ne
    pq := hwx
    qr := hxy
    rp := hwy.symm
  }⟩

/--
Final maximal-biclique stage of Lemma 6.4.  If a balanced `K_{s,s}` cannot
be extended by an outside vertex across either side, its induced core
satisfies the rank-minus-one outside-neighbor bound, contradicting Lemma
6.3.
-/
theorem balanced_complete_pair_contradiction_of_missed_vertices
    (setup : StandingSetup J B c D)
    (s : ℕ) (L R : Finset W)
    (hs : 2 ≤ s)
    (hLcard : L.card = s)
    (hRcard : R.card = s)
    (hLR : Disjoint L R)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (hmissL :
      ∀ w, w ∉ L ∪ R →
        ∃ x ∈ L, ¬ J.Adj w x)
    (hmissR :
      ∀ w, w ∉ L ∪ R →
        ∃ y ∈ R, ¬ J.Adj w y) :
    False := by
  classical
  have hLnonempty : L.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hRnonempty : R.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hadjExact :
      ∀ u v : W,
        u ∈ L ∪ R → v ∈ L ∪ R →
          (J.Adj u v ↔
            (u ∈ L ∧ v ∈ R) ∨
              (u ∈ R ∧ v ∈ L)) :=
    setup.complete_pair_adj_iff
      L R hLR hLnonempty hRnonempty hcross
  let C :=
    BipartiteCore.ofCompleteRaw J L R hLR
      (by omega) (by omega) hadjExact
  have hCrank : C.rank = s := by
    dsimp [C, BipartiteCore.rank,
      BipartiteCore.ofCompleteRaw]
    rw [BipartiteCore.card_rawSide,
      BipartiteCore.card_rawSide,
      hLcard, hRcard]
    simp
  have houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1 := by
    intro w hw
    change w ∉ L ∪ R at hw
    change
      finiteBoundaryDegree J (L ∪ R) w ≤
        C.rank - 1
    have hbound : finiteBoundaryDegree J (L ∪ R) w ≤ s - 1 := by
      by_cases hmeetL :
          ∃ x ∈ L, J.Adj w x
      · obtain ⟨x₀, hx₀L, hwx₀⟩ := hmeetL
        obtain ⟨xMiss, hxMissL, hwxMiss⟩ :=
          hmissL w hw
        have hsub :
            J.neighborSet w ∩
                (↑(L ∪ R) : Set W) ⊆
              (↑(L.erase xMiss) : Set W) := by
          intro z hz
          have hzUnion : z ∈ L ∪ R := hz.2
          rcases Finset.mem_union.mp hzUnion with hzL | hzR
          · exact Finset.mem_erase.mpr
              ⟨fun hzx => hwxMiss (hzx ▸ hz.1),
                hzL⟩
          · exact False.elim
              (setup.outside_not_meet_both_complete_pair
                L R hcross w x₀ z hx₀L hzR
                hwx₀ hz.1)
        unfold finiteBoundaryDegree
        calc
          (J.neighborSet w ∩
              (↑(L ∪ R) : Set W)).ncard
              ≤ (↑(L.erase xMiss) : Set W).ncard :=
            Set.ncard_le_ncard hsub
          _ = (L.erase xMiss).card :=
            Set.ncard_coe_finset _
          _ = s - 1 := by
            rw [Finset.card_erase_of_mem hxMissL,
              hLcard]
      · obtain ⟨yMiss, hyMissR, hwyMiss⟩ :=
          hmissR w hw
        have hsub :
            J.neighborSet w ∩
                (↑(L ∪ R) : Set W) ⊆
              (↑(R.erase yMiss) : Set W) := by
          intro z hz
          have hzUnion : z ∈ L ∪ R := hz.2
          rcases Finset.mem_union.mp hzUnion with hzL | hzR
          · exact False.elim
              (hmeetL ⟨z, hzL, hz.1⟩)
          · exact Finset.mem_erase.mpr
              ⟨fun hzy => hwyMiss (hzy ▸ hz.1),
                hzR⟩
        unfold finiteBoundaryDegree
        calc
          (J.neighborSet w ∩
              (↑(L ∪ R) : Set W)).ncard
              ≤ (↑(R.erase yMiss) : Set W).ncard :=
            Set.ncard_le_ncard hsub
          _ = (R.erase yMiss).card :=
            Set.ncard_coe_finset _
          _ = s - 1 := by
            rw [Finset.card_erase_of_mem hyMissR,
              hRcard]
    simpa [hCrank] using hbound
  exact setup.lifted_core_contradiction
    C houtside

/--
The last paragraph of Lemma 6.4 with the preceding “no `K_{s,s+1}`”
conclusion as an explicit premise.  A vertex meeting an entire side would
create that forbidden unbalanced biclique, so the missed-vertex hypotheses
above are derived rather than assumed.
-/
theorem balanced_complete_pair_contradiction_of_no_unbalanced_pair
    (setup : StandingSetup J B c D)
    (s : ℕ) (L R : Finset W)
    (hs : 2 ≤ s)
    (hLcard : L.card = s)
    (hRcard : R.card = s)
    (hLR : Disjoint L R)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (hnoUnbalanced :
      ∀ A E : Finset W,
        A.card = s → E.card = s + 1 →
        Disjoint A E →
        (∀ x ∈ A, ∀ y ∈ E, J.Adj x y) →
        False) :
    False := by
  classical
  have hmissL :
      ∀ w, w ∉ L ∪ R →
        ∃ x ∈ L, ¬ J.Adj w x := by
    intro w hw
    by_contra hnone
    simp only [not_exists, not_and,
      not_not] at hnone
    have hwL : w ∉ L := by
      intro hwL
      exact hw (Finset.mem_union_left R hwL)
    have hwR : w ∉ R := by
      intro hwR
      exact hw (Finset.mem_union_right L hwR)
    apply hnoUnbalanced L (insert w R)
      hLcard
    · rw [Finset.card_insert_of_notMem hwR,
        hRcard]
    · apply Finset.disjoint_left.mpr
      intro x hxL hxInsert
      simp only [Finset.mem_insert] at hxInsert
      rcases hxInsert with rfl | hxR
      · exact hwL hxL
      · exact Finset.disjoint_left.mp hLR
          hxL hxR
    · intro x hxL y hyInsert
      simp only [Finset.mem_insert] at hyInsert
      rcases hyInsert with rfl | hyR
      · exact (hnone x hxL).symm
      · exact hcross x hxL y hyR
  have hmissR :
      ∀ w, w ∉ L ∪ R →
        ∃ y ∈ R, ¬ J.Adj w y := by
    intro w hw
    by_contra hnone
    simp only [not_exists, not_and,
      not_not] at hnone
    have hwL : w ∉ L := by
      intro hwL
      exact hw (Finset.mem_union_left R hwL)
    have hwR : w ∉ R := by
      intro hwR
      exact hw (Finset.mem_union_right L hwR)
    apply hnoUnbalanced R (insert w L)
      hRcard
    · rw [Finset.card_insert_of_notMem hwL,
        hLcard]
    · apply Finset.disjoint_left.mpr
      intro y hyR hxInsert
      simp only [Finset.mem_insert] at hxInsert
      rcases hxInsert with rfl | hxL
      · exact hwR hyR
      · exact Finset.disjoint_left.mp hLR
          hxL hyR
    · intro y hyR x hxInsert
      simp only [Finset.mem_insert] at hxInsert
      rcases hxInsert with rfl | hxL
      · exact (hnone y hyR).symm
      · exact (hcross x hxL y hyR).symm
  exact setup.balanced_complete_pair_contradiction_of_missed_vertices
    s L R hs hLcard hRcard hLR hcross
    hmissL hmissR

/--
The degree-counting core of the middle paragraph of Lemma 6.4.  Here
`|L| = s < |R|`; maximality supplies a missed vertex of `L`, while exclusion
of `K_{s+1,s+1}^-` supplies the bound on neighbors in `R`.
-/
theorem unbalanced_complete_pair_contradiction_of_side_bounds
    (setup : StandingSetup J B c D)
    (s t : ℕ) (L R : Finset W)
    (hs : 2 ≤ s)
    (hst : s + 1 ≤ t)
    (hLcard : L.card = s)
    (hRcard : R.card = t)
    (hLR : Disjoint L R)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (hmissL :
      ∀ w, w ∉ L ∪ R →
        ∃ x ∈ L, ¬ J.Adj w x)
    (hsmallR :
      ∀ w, w ∉ L ∪ R →
        (¬∃ x ∈ L, J.Adj w x) →
        finiteBoundaryDegree J R w ≤ s - 1) :
    False := by
  classical
  have hLnonempty : L.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hRnonempty : R.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hadjExact :
      ∀ u v : W,
        u ∈ L ∪ R → v ∈ L ∪ R →
          (J.Adj u v ↔
            (u ∈ L ∧ v ∈ R) ∨
              (u ∈ R ∧ v ∈ L)) :=
    setup.complete_pair_adj_iff
      L R hLR hLnonempty hRnonempty hcross
  let C :=
    BipartiteCore.ofCompleteRaw J L R hLR
      (by omega) (by omega) hadjExact
  have hCrank : C.rank = s := by
    dsimp [C, BipartiteCore.rank,
      BipartiteCore.ofCompleteRaw]
    rw [BipartiteCore.card_rawSide,
      BipartiteCore.card_rawSide,
      hLcard, hRcard,
      Nat.min_eq_left (by omega)]
  have houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1 := by
    intro w hw
    change w ∉ L ∪ R at hw
    change
      finiteBoundaryDegree J (L ∪ R) w ≤
        C.rank - 1
    have hbound :
        finiteBoundaryDegree J (L ∪ R) w ≤
          s - 1 := by
      by_cases hmeetL :
          ∃ x ∈ L, J.Adj w x
      · obtain ⟨x₀, hx₀L, hwx₀⟩ := hmeetL
        obtain ⟨xMiss, hxMissL, hwxMiss⟩ :=
          hmissL w hw
        have hsub :
            J.neighborSet w ∩
                (↑(L ∪ R) : Set W) ⊆
              (↑(L.erase xMiss) : Set W) := by
          intro z hz
          rcases Finset.mem_union.mp hz.2 with hzL | hzR
          · exact Finset.mem_erase.mpr
              ⟨fun hzx => hwxMiss (hzx ▸ hz.1),
                hzL⟩
          · exact False.elim
              (setup.outside_not_meet_both_complete_pair
                L R hcross w x₀ z hx₀L hzR
                hwx₀ hz.1)
        unfold finiteBoundaryDegree
        calc
          (J.neighborSet w ∩
              (↑(L ∪ R) : Set W)).ncard
              ≤ (↑(L.erase xMiss) : Set W).ncard :=
            Set.ncard_le_ncard hsub
          _ = (L.erase xMiss).card :=
            Set.ncard_coe_finset _
          _ = s - 1 := by
            rw [Finset.card_erase_of_mem hxMissL,
              hLcard]
      · have hset :
            J.neighborSet w ∩
                (↑(L ∪ R) : Set W) =
              J.neighborSet w ∩ (↑R : Set W) := by
          ext z
          constructor
          · intro hz
            rcases Finset.mem_union.mp hz.2 with hzL | hzR
            · exact False.elim
                (hmeetL ⟨z, hzL, hz.1⟩)
            · exact ⟨hz.1, hzR⟩
          · rintro ⟨hwz, hzR⟩
            exact ⟨hwz,
              Finset.mem_union_right L hzR⟩
        unfold finiteBoundaryDegree at *
        rw [hset]
        exact hsmallR w hw hmeetL
    simpa [hCrank] using hbound
  exact setup.lifted_core_contradiction
    C houtside

/--
Maximality of the large side supplies the missed-left-vertex premise in the
preceding theorem.
-/
theorem unbalanced_complete_pair_contradiction_of_maximal_large_side
    (setup : StandingSetup J B c D)
    (s t : ℕ) (L R : Finset W)
    (hs : 2 ≤ s)
    (hst : s + 1 ≤ t)
    (hLcard : L.card = s)
    (hRcard : R.card = t)
    (hLR : Disjoint L R)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (hmax :
      ∀ E : Finset W,
        t < E.card →
        Disjoint L E →
        (∀ x ∈ L, ∀ y ∈ E, J.Adj x y) →
        False)
    (hsmallR :
      ∀ w, w ∉ L ∪ R →
        (¬∃ x ∈ L, J.Adj w x) →
        finiteBoundaryDegree J R w ≤ s - 1) :
    False := by
  classical
  have hmissL :
      ∀ w, w ∉ L ∪ R →
        ∃ x ∈ L, ¬ J.Adj w x := by
    intro w hw
    by_contra hnone
    simp only [not_exists, not_and,
      not_not] at hnone
    have hwL : w ∉ L := by
      intro hwL
      exact hw (Finset.mem_union_left R hwL)
    have hwR : w ∉ R := by
      intro hwR
      exact hw (Finset.mem_union_right L hwR)
    apply hmax (insert w R)
    · rw [Finset.card_insert_of_notMem hwR,
        hRcard]
      omega
    · apply Finset.disjoint_left.mpr
      intro x hxL hxInsert
      simp only [Finset.mem_insert] at hxInsert
      rcases hxInsert with rfl | hxR
      · exact hwL hxL
      · exact Finset.disjoint_left.mp hLR
          hxL hxR
    · intro x hxL y hyInsert
      simp only [Finset.mem_insert] at hyInsert
      rcases hyInsert with rfl | hyR
      · exact (hnone x hxL).symm
      · exact hcross x hxL y hyR
  exact setup.unbalanced_complete_pair_contradiction_of_side_bounds
    s t L R hs hst hLcard hRcard hLR
    hcross hmissL hsmallR

/--
The first paragraph of Lemma 6.4.  A near-balanced
`K_{s+1,s+1}^-` cannot occur when `s` is maximal among balanced complete
bipartite subgraphs.

The proof certifies the designated missing edge as genuinely absent,
constructs the exact induced one-missing-edge core, and proves its
rank-minus-one outside-neighbor bound before invoking Lemma 6.3.
-/
theorem almost_balanced_pair_contradiction_of_no_complete
    (setup : StandingSetup J B c D)
    (s : ℕ) (L R : Finset W)
    (xMissing yMissing : W)
    (hs : 2 ≤ s)
    (hLcard : L.card = s + 1)
    (hRcard : R.card = s + 1)
    (hLR : Disjoint L R)
    (hxMissing : xMissing ∈ L)
    (hyMissing : yMissing ∈ R)
    (hcrossExcept :
      ∀ x ∈ L, ∀ y ∈ R,
        x ≠ xMissing ∨ y ≠ yMissing →
          J.Adj x y)
    (hnoComplete :
      ∀ A E : Finset W,
        A.card = s + 1 →
        E.card = s + 1 →
        Disjoint A E →
        (∀ x ∈ A, ∀ y ∈ E, J.Adj x y) →
        False) :
    False := by
  classical
  have hmissing :
      ¬J.Adj xMissing yMissing := by
    intro hxy
    apply hnoComplete L R hLcard hRcard hLR
    intro x hxL y hyR
    by_cases hx : x = xMissing
    · by_cases hy : y = yMissing
      · simpa [hx, hy] using hxy
      · exact hcrossExcept x hxL y hyR
          (Or.inr hy)
    · exact hcrossExcept x hxL y hyR
        (Or.inl hx)
  have hadjExact :
      ∀ u v : W,
        u ∈ L ∪ R → v ∈ L ∪ R →
          (J.Adj u v ↔
            ((u ∈ L ∧ v ∈ R) ∨
              (u ∈ R ∧ v ∈ L)) ∧
            ¬((u = xMissing ∧ v = yMissing) ∨
              (u = yMissing ∧ v = xMissing))) :=
    setup.almost_pair_adj_iff L R
      xMissing yMissing hLR hxMissing hyMissing
      (by omega) (by omega) hcrossExcept hmissing
  let C :=
    BipartiteCore.ofMissingRaw J L R
      xMissing yMissing hLR hxMissing hyMissing
      (by omega) (by omega) (by omega) hadjExact
  have hCrank : C.rank = s + 1 := by
    dsimp [C, BipartiteCore.rank,
      BipartiteCore.ofMissingRaw]
    rw [BipartiteCore.card_rawSide,
      BipartiteCore.card_rawSide,
      hLcard, hRcard]
    simp
  have houtside :
      ∀ w, w ∉ C.carrier →
        finiteBoundaryDegree J C.carrier w ≤
          C.rank - 1 := by
    intro w hw
    change w ∉ L ∪ R at hw
    change
      finiteBoundaryDegree J (L ∪ R) w ≤
        C.rank - 1
    have hwL : w ∉ L := by
      intro hwL
      exact hw (Finset.mem_union_left R hwL)
    have hwR : w ∉ R := by
      intro hwR
      exact hw (Finset.mem_union_right L hwR)
    have hmissL :
        ∃ x ∈ L, ¬J.Adj w x := by
      by_contra hnone
      simp only [not_exists, not_and,
        not_not] at hnone
      apply hnoComplete L
        (insert w (R.erase yMissing))
        hLcard
      · rw [Finset.card_insert_of_notMem
          (fun hwErase =>
            hwR (Finset.mem_of_mem_erase hwErase)),
          Finset.card_erase_of_mem hyMissing,
          hRcard]
        omega
      · apply Finset.disjoint_left.mpr
        intro x hxL hxInsert
        rcases Finset.mem_insert.mp hxInsert with
          rfl | hxErase
        · exact hwL hxL
        · exact Finset.disjoint_left.mp hLR hxL
            (Finset.mem_of_mem_erase hxErase)
      · intro x hxL y hyInsert
        rcases Finset.mem_insert.mp hyInsert with
          rfl | hyErase
        · exact (hnone x hxL).symm
        · have hyData :=
            Finset.mem_erase.mp hyErase
          exact hcrossExcept x hxL y hyData.2
            (Or.inr hyData.1)
    have hmissR :
        ∃ y ∈ R, ¬J.Adj w y := by
      by_contra hnone
      simp only [not_exists, not_and,
        not_not] at hnone
      apply hnoComplete
        (insert w (L.erase xMissing)) R
      · rw [Finset.card_insert_of_notMem
          (fun hwErase =>
            hwL (Finset.mem_of_mem_erase hwErase)),
          Finset.card_erase_of_mem hxMissing,
          hLcard]
        omega
      · exact hRcard
      · apply Finset.disjoint_left.mpr
        intro x hxInsert hxR
        rcases Finset.mem_insert.mp hxInsert with
          rfl | hxErase
        · exact hwR hxR
        · exact Finset.disjoint_left.mp hLR
            (Finset.mem_of_mem_erase hxErase) hxR
      · intro x hxInsert y hyR
        rcases Finset.mem_insert.mp hxInsert with
          rfl | hxErase
        · exact hnone y hyR
        · have hxData :=
            Finset.mem_erase.mp hxErase
          exact hcrossExcept x hxData.2 y hyR
            (Or.inl hxData.1)
    obtain ⟨xMiss, hxMissL, hwxMiss⟩ := hmissL
    obtain ⟨yMiss, hyMissR, hwyMiss⟩ := hmissR
    have hbound :
        finiteBoundaryDegree J (L ∪ R) w ≤ s := by
      by_cases hmeetL :
          ∃ x ∈ L, J.Adj w x
      · by_cases hmeetR :
            ∃ y ∈ R, J.Adj w y
        · obtain ⟨x₀, hx₀L, hwx₀⟩ := hmeetL
          obtain ⟨y₀, hy₀R, hwy₀⟩ := hmeetR
          have hforced :
              ∀ x ∈ L, ∀ y ∈ R,
                J.Adj w x → J.Adj w y →
                  x = xMissing ∧ y = yMissing := by
            intro x hxL y hyR hwx hwy
            by_cases hxx : x = xMissing
            · by_cases hyy : y = yMissing
              · exact ⟨hxx, hyy⟩
              · have hxy :=
                  hcrossExcept x hxL y hyR
                    (Or.inr hyy)
                exact False.elim
                  (setup.no_triangle ⟨{
                    p := w
                    q := x
                    r := y
                    p_ne_q := hwx.ne
                    p_ne_r := hwy.ne
                    q_ne_r := hxy.ne
                    pq := hwx
                    qr := hxy
                    rp := hwy.symm
                  }⟩)
            · have hxy :=
                hcrossExcept x hxL y hyR
                  (Or.inl hxx)
              exact False.elim
                (setup.no_triangle ⟨{
                  p := w
                  q := x
                  r := y
                  p_ne_q := hwx.ne
                  p_ne_r := hwy.ne
                  q_ne_r := hxy.ne
                  pq := hwx
                  qr := hxy
                  rp := hwy.symm
                }⟩)
          have hsub :
              J.neighborSet w ∩
                  (↑(L ∪ R) : Set W) ⊆
                (↑({xMissing, yMissing} :
                  Finset W) : Set W) := by
            intro z hz
            rcases Finset.mem_union.mp hz.2 with
              hzL | hzR
            · have hzEq :=
                (hforced z hzL y₀ hy₀R
                  hz.1 hwy₀).1
              simp [hzEq]
            · have hzEq :=
                (hforced x₀ hx₀L z hzR
                  hwx₀ hz.1).2
              simp [hzEq]
          unfold finiteBoundaryDegree
          calc
            (J.neighborSet w ∩
                (↑(L ∪ R) : Set W)).ncard
                ≤ (↑({xMissing, yMissing} :
                    Finset W) : Set W).ncard :=
              Set.ncard_le_ncard hsub
            _ = ({xMissing, yMissing} :
                Finset W).card :=
              Set.ncard_coe_finset _
            _ ≤ 2 := Finset.card_le_two
            _ ≤ s := hs
        · have hsub :
              J.neighborSet w ∩
                  (↑(L ∪ R) : Set W) ⊆
                (↑(L.erase xMiss) : Set W) := by
            intro z hz
            rcases Finset.mem_union.mp hz.2 with
              hzL | hzR
            · exact Finset.mem_erase.mpr
                ⟨fun hzx =>
                  hwxMiss (hzx ▸ hz.1), hzL⟩
            · exact False.elim
                (hmeetR ⟨z, hzR, hz.1⟩)
          unfold finiteBoundaryDegree
          calc
            (J.neighborSet w ∩
                (↑(L ∪ R) : Set W)).ncard
                ≤ (↑(L.erase xMiss) : Set W).ncard :=
              Set.ncard_le_ncard hsub
            _ = (L.erase xMiss).card :=
              Set.ncard_coe_finset _
            _ = s := by
              rw [Finset.card_erase_of_mem hxMissL,
                hLcard]
              omega
      · by_cases hmeetR :
            ∃ y ∈ R, J.Adj w y
        · have hsub :
              J.neighborSet w ∩
                  (↑(L ∪ R) : Set W) ⊆
                (↑(R.erase yMiss) : Set W) := by
            intro z hz
            rcases Finset.mem_union.mp hz.2 with
              hzL | hzR
            · exact False.elim
                (hmeetL ⟨z, hzL, hz.1⟩)
            · exact Finset.mem_erase.mpr
                ⟨fun hzy =>
                  hwyMiss (hzy ▸ hz.1), hzR⟩
          unfold finiteBoundaryDegree
          calc
            (J.neighborSet w ∩
                (↑(L ∪ R) : Set W)).ncard
                ≤ (↑(R.erase yMiss) : Set W).ncard :=
              Set.ncard_le_ncard hsub
            _ = (R.erase yMiss).card :=
              Set.ncard_coe_finset _
            _ = s := by
              rw [Finset.card_erase_of_mem hyMissR,
                hRcard]
              omega
        · have hsub :
              J.neighborSet w ∩
                  (↑(L ∪ R) : Set W) ⊆
                (↑(∅ : Finset W) : Set W) := by
            intro z hz
            rcases Finset.mem_union.mp hz.2 with
              hzL | hzR
            · exact False.elim
                (hmeetL ⟨z, hzL, hz.1⟩)
            · exact False.elim
                (hmeetR ⟨z, hzR, hz.1⟩)
          unfold finiteBoundaryDegree
          calc
            (J.neighborSet w ∩
                (↑(L ∪ R) : Set W)).ncard
                ≤ (↑(∅ : Finset W) : Set W).ncard :=
              Set.ncard_le_ncard hsub
            _ = 0 := by simp
            _ ≤ s := Nat.zero_le _
    simpa [hCrank] using hbound
  exact setup.lifted_core_contradiction
    C houtside

omit [Fintype W] in
/--
Excluding a near-balanced `K_{s+1,s+1}^-` gives the large-side degree
bound used in the middle paragraph of Lemma 6.4.

Indeed, if an outside vertex `w` had `s` neighbors in `R`, choose exactly
`s` of them and one further vertex of `R`.  Together with `L`, these form
two sides of size `s+1`, and every cross-edge is present except possibly
the edge from `w` to the further vertex.
-/
theorem large_side_degree_bound_of_no_almost_balanced
    (s t : ℕ) (L R : Finset W)
    (hst : s + 1 ≤ t)
    (hLcard : L.card = s)
    (hRcard : R.card = t)
    (hLR : Disjoint L R)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (hnoAlmost :
      ∀ A E : Finset W, ∀ x y : W,
        A.card = s + 1 →
        E.card = s + 1 →
        Disjoint A E →
        x ∈ A →
        y ∈ E →
        (∀ a ∈ A, ∀ b ∈ E,
          a ≠ x ∨ b ≠ y → J.Adj a b) →
        False)
    (w : W) (hw : w ∉ L ∪ R) :
    finiteBoundaryDegree J R w ≤ s - 1 := by
  classical
  let N := R.filter (fun y => J.Adj w y)
  have hNcard :
      N.card = finiteBoundaryDegree J R w := by
    unfold finiteBoundaryDegree
    rw [← Set.ncard_coe_finset N]
    congr 1
    ext y
    simp [N, SimpleGraph.mem_neighborSet, and_comm]
  by_contra hbound
  have hsN : s ≤ N.card := by
    rw [hNcard]
    omega
  obtain ⟨Y, hYN, hYcard⟩ :=
    Finset.exists_subset_card_eq hsN
  have hYsubR : Y ⊆ R := by
    intro y hyY
    exact (Finset.mem_filter.mp (hYN hyY)).1
  have hYltR : Y.card < R.card := by
    rw [hYcard, hRcard]
    omega
  have hnotRY : ¬R ⊆ Y := by
    intro hRY
    exact (Nat.not_le_of_gt hYltR)
      (Finset.card_le_card hRY)
  obtain ⟨yExtra, hyExtraR, hyExtraY⟩ :=
    Finset.not_subset.mp hnotRY
  have hwL : w ∉ L := by
    intro hwL
    exact hw (Finset.mem_union_left R hwL)
  have hwR : w ∉ R := by
    intro hwR
    exact hw (Finset.mem_union_right L hwR)
  apply hnoAlmost (insert w L) (insert yExtra Y)
      w yExtra
  · rw [Finset.card_insert_of_notMem hwL,
      hLcard]
  · rw [Finset.card_insert_of_notMem hyExtraY,
      hYcard]
  · apply Finset.disjoint_left.mpr
    intro a haA haE
    have haER : a ∈ R := by
      rcases Finset.mem_insert.mp haE with rfl | haY
      · exact hyExtraR
      · exact hYsubR haY
    rcases Finset.mem_insert.mp haA with rfl | haL
    · exact hwR haER
    · exact Finset.disjoint_left.mp hLR haL haER
  · exact Finset.mem_insert_self w L
  · exact Finset.mem_insert_self yExtra Y
  · intro a haA b hbE hnotMissing
    rcases Finset.mem_insert.mp haA with rfl | haL
    · rcases Finset.mem_insert.mp hbE with rfl | hbY
      · simp at hnotMissing
      · exact (Finset.mem_filter.mp (hYN hbY)).2
    · rcases Finset.mem_insert.mp hbE with rfl | hbY
      · exact hcross a haL b hyExtraR
      · exact hcross a haL b (hYsubR hbY)

/--
The complete middle-paragraph contradiction of Lemma 6.4: maximality of
the large side and exclusion of `K_{s+1,s+1}^-` supply both hypotheses of
the unbalanced-core argument.
-/
theorem unbalanced_complete_pair_contradiction_of_maximal_and_no_almost
    (setup : StandingSetup J B c D)
    (s t : ℕ) (L R : Finset W)
    (hs : 2 ≤ s)
    (hst : s + 1 ≤ t)
    (hLcard : L.card = s)
    (hRcard : R.card = t)
    (hLR : Disjoint L R)
    (hcross :
      ∀ x ∈ L, ∀ y ∈ R, J.Adj x y)
    (hmax :
      ∀ E : Finset W,
        t < E.card →
        Disjoint L E →
        (∀ x ∈ L, ∀ y ∈ E, J.Adj x y) →
        False)
    (hnoAlmost :
      ∀ A E : Finset W, ∀ x y : W,
        A.card = s + 1 →
        E.card = s + 1 →
        Disjoint A E →
        x ∈ A →
        y ∈ E →
        (∀ a ∈ A, ∀ b ∈ E,
          a ≠ x ∨ b ≠ y → J.Adj a b) →
        False) :
    False := by
  apply setup.unbalanced_complete_pair_contradiction_of_maximal_large_side
    s t L R hs hst hLcard hRcard hLR hcross hmax
  intro w hw _
  exact large_side_degree_bound_of_no_almost_balanced
    s t L R hst hLcard hRcard hLR hcross
    hnoAlmost w hw

/--
Paper Lemma 6.4: the standing graph contains no simple four-cycle.

Starting from an actual `SimpleCycle` of length four, the proof extracts an
injective `K_{2,2}`, selects the two finite maxima used in the paper,
rules out the near-balanced and unbalanced cases, and finally applies the
balanced-core contradiction.
-/
theorem no_four_cycle
    (setup : StandingSetup J B c D) :
    ¬HasCycleLength J 4 := by
  intro hcycle
  have htwo :
      HasCompletePairSize J 2 :=
    four_cycle_has_complete_pair_size_two hcycle
  obtain ⟨s, hsPair, hs, hmaxBalanced⟩ :=
    exists_maximal_complete_pair_size htwo
  obtain ⟨L, R, hLcard, hRcard, hLR,
      hcross⟩ := hsPair
  have hnoCompleteSuccessor :
      ∀ A E : Finset W,
        A.card = s + 1 →
        E.card = s + 1 →
        Disjoint A E →
        (∀ x ∈ A, ∀ y ∈ E, J.Adj x y) →
        False := by
    intro A E hAcard hEcard hAE hcrossAE
    exact hmaxBalanced (s + 1) (by omega)
      ⟨A, E, hAcard, hEcard, hAE,
        hcrossAE⟩
  have hnoAlmost :
      ¬HasAlmostCompletePairSize J (s + 1) := by
    rintro ⟨A, E, xMissing, yMissing,
      hAcard, hEcard, hAE, hxA, hyE,
      hcrossExcept⟩
    exact
      setup.almost_balanced_pair_contradiction_of_no_complete
        s A E xMissing yMissing hs
        hAcard hEcard hAE hxA hyE
        hcrossExcept hnoCompleteSuccessor
  have hnoUnbalanced :
      ∀ A E : Finset W,
        A.card = s →
        E.card = s + 1 →
        Disjoint A E →
        (∀ x ∈ A, ∀ y ∈ E, J.Adj x y) →
        False := by
    intro A E hAcard hEcard hAE hcrossAE
    obtain ⟨t, T, hTcard, hAT, hcrossAT,
        hst, hmaxT⟩ :=
      exists_maximal_complete_right_side
        A E hEcard hAE hcrossAE
    apply
      setup.unbalanced_complete_pair_contradiction_of_maximal_and_no_almost
        s t A T hs hst hAcard hTcard
        hAT hcrossAT hmaxT
    intro A' E' xMissing yMissing
      hA'card hE'card hA'E' hxA' hyE'
      hcrossExcept
    apply hnoAlmost
    exact ⟨A', E', xMissing, yMissing,
      hA'card, hE'card, hA'E', hxA',
      hyE', hcrossExcept⟩
  exact
    setup.balanced_complete_pair_contradiction_of_no_unbalanced_pair
      s L R hs hLcard hRcard hLR hcross
      hnoUnbalanced

end StandingSetup

end DeanK5
