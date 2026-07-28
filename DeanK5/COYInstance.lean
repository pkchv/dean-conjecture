import DeanK5.COYSmallOrder

/-!
# Rooted instances for the bounded COY induction

The published theorem allows the exceptional vertex to coincide with a
root.  Although the final Dean-conjecture proof invokes only the
pairwise-distinct case, recursive calls in COY's proof use the stronger
invariant.  This file packages that invariant for `1 ≤ q ≤ 4`.
-/

namespace DeanK5

open SimpleGraph

universe u

namespace COY

/-- Three vertices suffice to find a vertex outside two distinct roots. -/
theorem exists_avoiding_two_of_three_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (x y : V) (hcard : 3 ≤ Fintype.card V) :
    ∃ v : V, v ≠ x ∧ v ≠ y := by
  by_contra h
  push Not at h
  have huniv :
      Finset.univ ⊆ ({x, y} : Finset V) := by
    intro v _
    by_cases hvx : v = x
    · simp [hvx]
    · simp [h v hvx]
  have hcardUpper : Fintype.card V ≤ 2 := by
    rw [← Finset.card_univ]
    calc
      Finset.univ.card ≤ ({x, y} : Finset V).card :=
        Finset.card_le_card huniv
      _ ≤ ({y} : Finset V).card + 1 :=
        Finset.card_insert_le x {y}
      _ = 2 := by simp
  omega

/-- The induction measure used in the proof of COY Theorem 3. -/
noncomputable def rootedComplexity
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  Fintype.card V + G.edgeSet.ncard

/-- Fewer vertices and no more edges strictly decrease the COY measure. -/
theorem rootedComplexity_lt_of_card_lt_of_edgeCount_le
    {V W : Type u} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hcard : Fintype.card W < Fintype.card V)
    (hedges : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    rootedComplexity H < rootedComplexity G := by
  unfold rootedComplexity
  omega

/-- No more vertices and fewer edges strictly decrease the COY measure. -/
theorem rootedComplexity_lt_of_card_le_of_edgeCount_lt
    {V W : Type u} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hcard : Fintype.card W ≤ Fintype.card V)
    (hedges : H.edgeSet.ncard < G.edgeSet.ncard) :
    rootedComplexity H < rootedComplexity G := by
  unfold rootedComplexity
  omega

/--
The source-faithful induction invariant for COY Theorem 3 in the bounded
range needed here.  No distinctness is imposed on the exceptional vertex.
-/
structure RootedInstance
    {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y z : V) : Prop where
  q_pos : 1 ≤ q
  q_le_four : q ≤ 4
  roots_ne : x ≠ y
  rooted_two_connected : IsTwoConnected (G ⊔ edge x y)
  ordinary_nonempty :
    ∃ v : V, v ≠ x ∧ v ≠ y ∧ v ≠ z
  degree_lower :
    ∀ v, v ≠ x → v ≠ y → v ≠ z →
      q + 1 ≤ finiteDegree G v

namespace RootedInstance

variable {V : Type u} [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The path-family conclusion associated with a rooted instance. -/
def Solvable (_I : RootedInstance q G x y z) : Prop :=
  Nonempty (AdmissiblePathFamily G x y q)

/-- Every bounded rooted instance with `q = 1` is solvable internally. -/
theorem solvable_of_q_eq_one
    (I : RootedInstance q G x y z)
    (hq : q = 1) :
    I.Solvable := by
  subst q
  exact one_exception_rooted_paths_one
    G x y z I.roots_ne I.rooted_two_connected I.degree_lower

/-- A nonsolvable bounded rooted instance necessarily has `q ≥ 2`. -/
theorem two_le_q_of_not_solvable
    (I : RootedInstance q G x y z)
    (hno : ¬I.Solvable) :
    2 ≤ q := by
  by_contra hq
  have hqOne : q = 1 := by
    have hqPos := I.q_pos
    omega
  exact hno (I.solvable_of_q_eq_one hqOne)

/--
In the nontrivial range `q ≥ 2`, the degree bound forces at least four
vertices.
-/
theorem four_le_card
    (I : RootedInstance q G x y z)
    (hqTwo : 2 ≤ q) :
    4 ≤ Fintype.card V := by
  obtain ⟨v, hvx, hvy, hvz⟩ := I.ordinary_nonempty
  have hneighborProper :
      G.neighborSet v ≠ Set.univ := by
    intro h
    have hvv : v ∈ G.neighborSet v := by
      rw [h]
      simp
    exact G.loopless.irrefl v hvv
  have hdegreeUpper :
      finiteDegree G v < Fintype.card V := by
    unfold finiteDegree
    simpa [Nat.card_eq_fintype_card] using
      Set.ncard_lt_card hneighborProper
  have hdegreeLower := I.degree_lower v hvx hvy hvz
  omega

/--
A nonsolvable bounded instance with `q ≥ 2` has at least five vertices.
This packages the internally proved order-four base case.
-/
theorem five_le_card
    (I : RootedInstance q G x y z)
    (hno : ¬I.Solvable) :
    5 ≤ Fintype.card V :=
  five_le_card_of_no_one_exception_rooted_paths
    q G x y z (I.two_le_q_of_not_solvable hno)
    (I.four_le_card (I.two_le_q_of_not_solvable hno))
    I.roots_ne I.rooted_two_connected I.degree_lower hno

/--
Package the exact final-use interface as the stronger induction invariant.
-/
theorem ofBoundedInterface
    (q : ℕ) (G : SimpleGraph V) (x y z : V)
    (hqTwo : 2 ≤ q) (hqFour : q ≤ 4)
    (horder : 4 ≤ Fintype.card V)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y → v ≠ z →
      q + 1 ≤ finiteDegree G v) :
    RootedInstance q G x y z where
  q_pos := by omega
  q_le_four := hqFour
  roots_ne := hxy
  rooted_two_connected := hconn
  ordinary_nonempty :=
    exists_avoiding_three_of_four_le x y z horder
  degree_lower := hdeg

/--
Package a recursive source call with no exceptional vertex in the smaller
graph.  COY permits its named exception to lie outside that graph; in the
typed finite interface we instead repeat the left root.  This excludes no
additional ordinary vertex and therefore expresses the same degree bound.
-/
theorem ofNoExtraException
    (q : ℕ) (G : SimpleGraph V) (x y : V)
    (hqPos : 1 ≤ q) (hqFour : q ≤ 4)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y →
      q + 1 ≤ finiteDegree G v) :
    RootedInstance q G x y x where
  q_pos := hqPos
  q_le_four := hqFour
  roots_ne := hxy
  rooted_two_connected := hconn
  ordinary_nonempty := by
    obtain ⟨v, hvx, hvy⟩ :=
      exists_avoiding_two_of_three_le x y hconn.1
    exact ⟨v, hvx, hvy, hvx⟩
  degree_lower := by
    intro v hvx hvy _
    exact hdeg v hvx hvy

end RootedInstance

/--
A counterexample minimal for `|V(G)| + |E(G)|`, with the induction
hypothesis available for every smaller bounded rooted instance.  The
recursive parameter `q'` may be smaller than the original `q`, as in COY's
core reductions.
-/
structure MinimalCounterexample
    {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y z : V) : Prop
    extends RootedInstance q G x y z where
  no_paths : ¬toRootedInstance.Solvable
  smaller_solvable :
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      {q' : ℕ} {H : SimpleGraph W} {a b e : W},
      (I : RootedInstance q' H a b e) →
      rootedComplexity H < rootedComplexity G →
      I.Solvable

namespace MinimalCounterexample

variable {V : Type u} [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- A minimal counterexample lies in the nontrivial range `q ≥ 2`. -/
theorem two_le_q
    (M : MinimalCounterexample q G x y z) :
    2 ≤ q :=
  M.toRootedInstance.two_le_q_of_not_solvable M.no_paths

/-- A minimal counterexample has at least five vertices. -/
theorem five_le_card
    (M : MinimalCounterexample q G x y z) :
    5 ≤ Fintype.card V :=
  M.toRootedInstance.five_le_card M.no_paths

end MinimalCounterexample

/--
It suffices to eliminate minimal counterexamples.  This theorem supplies
the nested cross-carrier induction on `rootedComplexity`; later COY claims
may therefore work only with the explicit `MinimalCounterexample` package.
-/
theorem all_solvable_of_minimal_counterexample_false
    (heliminate :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {q : ℕ} {H : SimpleGraph W} {a b e : W},
        MinimalCounterexample q H a b e → False) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {q : ℕ} {G : SimpleGraph V} {x y z : V},
      (I : RootedInstance q G x y z) → I.Solvable := by
  intro V _ _ q G x y z
  generalize hmeasure : rootedComplexity G = n
  induction n using Nat.strong_induction_on generalizing V q G x y z with
  | h n ih =>
      intro I
      by_contra hno
      apply heliminate
        (W := V) (q := q) (H := G)
        (a := x) (b := y) (e := z)
      exact {
        toRootedInstance := I
        no_paths := hno
        smaller_solvable := by
          intro W _ _ q' H a b e I' hsmaller
          apply ih (rootedComplexity H)
          · simpa [hmeasure] using hsmaller
          · rfl
      }

/--
The exact bounded interface theorem follows once the source claims eliminate
every bounded minimal counterexample.
-/
theorem bounded_interface_of_minimal_counterexample_false
    (heliminate :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        {q' : ℕ} {H : SimpleGraph W} {a b e : W},
        MinimalCounterexample q' H a b e → False)
    {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y z : V)
    (hqTwo : 2 ≤ q) (hqFour : q ≤ 4)
    (horder : 4 ≤ Fintype.card V)
    (hxy : x ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y → v ≠ z →
      q + 1 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y q) :=
  all_solvable_of_minimal_counterexample_false heliminate
    (RootedInstance.ofBoundedInterface
      q G x y z hqTwo hqFour horder hxy hconn hdeg)

end COY

end DeanK5
