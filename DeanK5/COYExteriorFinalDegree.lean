import DeanK5.COYExteriorClaimThreeFourteen
import DeanK5.COYExteriorTypeThreeStage

/-!
# The final degree ledger in the COY exterior argument

The last paragraph of the COY proof uses two logically separate facts.
First, condition (XY2) compares the root degrees once the selected working
core is type 3.  Together with one extra neighbour of the first root and a
small envelope for the second root's neighbourhood, this gives the exact
degree `|T| + 1`.

Second, after the ordered block-chain argument has reached `p < t - 1`,
the penultimate cut vertex has neighbours only among the second root, the
preceding cut vertex, and the unique `S`-vertex.  The resulting upper bound
three contradicts the ambient lower bound `q + 1 ≥ 4`.

This file packages both calculations.  It does not assume that a block
chain exists and does not hide the structural proof of the final
neighbourhood containment.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.TypeThreeStage

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/--
At the type-three stage, (XY1) forces the reverse optimal core also to
have type 3.  Condition (XY2) therefore compares the two root degrees.
-/
theorem chosenRoot_degree_le_otherRoot
    (D : P.TypeThreeStage) :
    finiteDegree G x ≤ finiteDegree G y := by
  have hWorkingType :
      P.working.rooted.core.typeNumber = 3 := by
    rw [D.core_eq]
    rfl
  have hChosenType :
      P.orientation.chosen.rooted.core.typeNumber = 3 := by
    rw [← P.working.typeNumber_eq_optimal]
    exact hWorkingType
  have hReverseUpper :
      P.orientation.reverse.rooted.core.typeNumber ≤ 3 := by
    cases P.orientation.reverse.rooted.core <;>
      simp [Core.typeNumber]
  have hReverseLower :
      3 ≤ P.orientation.reverse.rooted.core.typeNumber := by
    simpa [hChosenType] using
      P.orientation.preferred.type_le
  have hReverseType :
      P.orientation.reverse.rooted.core.typeNumber = 3 :=
    Nat.le_antisymm hReverseUpper hReverseLower
  have hAttains :
      P.orientation.OtherRootAttainsChosenType :=
    ⟨P.orientation.reverse.rank,
      P.orientation.reverse.rooted,
      hReverseType.trans hChosenType.symm⟩
  exact
    P.orientation.chosen_degree_le_other_of_otherRootAttainsChosenType
      hAttains

/-- A type-three terminal side always has at least two vertices. -/
theorem two_le_terminal_card
    (D : P.TypeThreeStage) :
    2 ≤ D.core.T.card :=
  (Nat.le_max_right (P.working.rank + 1) 2).trans
    D.core.card_T_lower

/-- Every terminal-side vertex is a neighbour of the chosen root. -/
theorem terminal_subset_chosenRoot_neighborSet
    (D : P.TypeThreeStage) :
    (↑D.core.T : Set V) ⊆ G.neighborSet x := by
  intro t ht
  exact D.core.root_adj_T t ht

/--
An `x`-neighbour outside the type-three terminal side gives the lower
degree bound `|T| + 1 ≤ d_G(x)`.
-/
theorem terminal_card_add_one_le_chosenRoot_degree
    (D : P.TypeThreeStage)
    {a : V}
    (hxa : G.Adj x a)
    (haT : a ∉ D.core.T) :
    D.core.T.card + 1 ≤ finiteDegree G x := by
  have hsubset :
      (↑(insert a D.core.T) : Set V) ⊆
        G.neighborSet x := by
    intro v hv
    change v ∈ insert a D.core.T at hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hvT
    · exact hxa
    · exact D.terminal_subset_chosenRoot_neighborSet hvT
  calc
    D.core.T.card + 1 =
        (insert a D.core.T).card := by
      symm
      exact Finset.card_insert_of_notMem haT
    _ = (↑(insert a D.core.T) : Set V).ncard := by
      symm
      exact Set.ncard_coe_finset _
    _ ≤ (G.neighborSet x).ncard :=
      Set.ncard_le_ncard hsubset
    _ = finiteDegree G x := rfl

/--
The reusable degree sandwich from the last page of the source proof.

One extra `x`-neighbour outside `T` gives the lower bound at `x`; (XY2)
passes it to `y`; and the displayed envelope bounds `y` from above.  Thus
both root degrees are exactly `|T| + 1`, and the envelope is the full
neighbourhood of `y`.
-/
theorem root_degree_sandwich
    (D : P.TypeThreeStage)
    {a last : V}
    (hxa : G.Adj x a)
    (haT : a ∉ D.core.T)
    (hySubset :
      G.neighborSet y ⊆
        (↑(insert last D.core.T) : Set V)) :
    finiteDegree G x = D.core.T.card + 1 ∧
      finiteDegree G y = D.core.T.card + 1 ∧
      G.neighborSet y =
        (↑(insert last D.core.T) : Set V) := by
  have hxLower :=
    D.terminal_card_add_one_le_chosenRoot_degree
      hxa haT
  have hxy :=
    D.chosenRoot_degree_le_otherRoot
  have hyUpper :
      finiteDegree G y ≤ D.core.T.card + 1 := by
    calc
      finiteDegree G y =
          (G.neighborSet y).ncard := rfl
      _ ≤
          (↑(insert last D.core.T) : Set V).ncard :=
        Set.ncard_le_ncard hySubset
      _ = (insert last D.core.T).card :=
        Set.ncard_coe_finset _
      _ ≤ D.core.T.card + 1 :=
        Finset.card_insert_le _ _
  have hxEq :
      finiteDegree G x = D.core.T.card + 1 := by
    omega
  have hyEq :
      finiteDegree G y = D.core.T.card + 1 := by
    omega
  have hEnvelopeLe :
      (↑(insert last D.core.T) : Set V).ncard ≤
        (G.neighborSet y).ncard := by
    have hNcard :
        (G.neighborSet y).ncard =
          D.core.T.card + 1 := by
      simpa [finiteDegree] using hyEq
    rw [hNcard, Set.ncard_coe_finset]
    exact Finset.card_insert_le _ _
  have hyEqEnvelope :
      G.neighborSet y =
        (↑(insert last D.core.T) : Set V) :=
    Set.eq_of_subset_of_ncard_le
      hySubset hEnvelopeLe
  exact ⟨hxEq, hyEq, hyEqEnvelope⟩

end PreferredWorkingCoreData.TypeThreeStage

/--
The exact local information used at the final penultimate cut vertex.

In the source proof, `bottleneck` is `b_{t-1}`, `predecessor` is
`b_{t-2}`, and `side` is the unique vertex `s₁` of the type-three
`S`-side.  The ordered block-chain construction is responsible for the
neighbourhood containment.
-/
structure ExteriorFinalDegreeCertificate
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y z : V) where
  /-- The penultimate cut vertex `b_{t-1}`. -/
  bottleneck : V
  /-- The preceding cut vertex `b_{t-2}`. -/
  predecessor : V
  /-- The unique type-three `S`-vertex. -/
  side : V
  /-- The bottleneck is ordinary for the ambient degree hypothesis. -/
  bottleneck_ne_x : bottleneck ≠ x
  bottleneck_ne_y : bottleneck ≠ y
  bottleneck_ne_z : bottleneck ≠ z
  /-- The final structural neighbourhood containment. -/
  neighborSet_subset :
    G.neighborSet bottleneck ⊆
      (↑({y, predecessor, side} : Finset V) : Set V)

namespace ExteriorFinalDegreeCertificate

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The three-candidate neighbourhood has cardinality at most three. -/
theorem finiteDegree_le_three
    (C : ExteriorFinalDegreeCertificate G x y z) :
    finiteDegree G C.bottleneck ≤ 3 := by
  calc
    finiteDegree G C.bottleneck =
        (G.neighborSet C.bottleneck).ncard := rfl
    _ ≤
        (↑({y, C.predecessor, C.side} : Finset V) :
          Set V).ncard :=
      Set.ncard_le_ncard C.neighborSet_subset
    _ = ({y, C.predecessor, C.side} : Finset V).card :=
      Set.ncard_coe_finset _
    _ ≤ ({C.predecessor, C.side} : Finset V).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ ({C.side} : Finset V).card + 2 := by
      have h :=
        Finset.card_insert_le C.predecessor {C.side}
      omega
    _ = 3 := by simp

/--
The final contradiction: the certificate gives degree at most three, while
the minimal-counterexample bound gives degree at least `q + 1 ≥ 4`.
-/
theorem false_of_three_le_q
    (M : MinimalCounterexample q G x y z)
    (C : ExteriorFinalDegreeCertificate G x y z)
    (hq : 3 ≤ q) :
    False := by
  have hupper := C.finiteDegree_le_three
  have hlower :=
    M.degree_lower C.bottleneck
      C.bottleneck_ne_x C.bottleneck_ne_y
        C.bottleneck_ne_z
  omega

/--
Claim 3.14(1) supplies `q ≥ 3`, so a final degree certificate closes the
type-three singleton-side branch immediately.
-/
theorem false_of_typeThree_singleton_side
    {P : PreferredWorkingCoreData G x y z}
    (M : MinimalCounterexample q G x y z)
    (D : P.TypeThreeStage)
    {s : V}
    (hS : D.core.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (C : ExteriorFinalDegreeCertificate G x y z) :
    False :=
  C.false_of_three_le_q M
    (P.three_le_q_of_typeThree_singleton_side
      M D.core D.core_eq hS hregion)

end ExteriorFinalDegreeCertificate

end COY

end DeanK5
