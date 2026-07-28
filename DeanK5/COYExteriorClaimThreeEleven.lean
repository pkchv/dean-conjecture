import DeanK5.COYExteriorClaimThreeElevenEndpoint
import DeanK5.COYExteriorClaimThreeNineBPrimeDegree
import DeanK5.Graph.TerminalMarkedBridge

/-!
# A feasible block in the selected COY exterior

This file proves COY Claim 3.11 in the form needed by the rooted
admissible-path argument.  The protected vertices of the selected exterior
are the two ambient vertices `y` and `z` that actually lie in that
component.

If no feasible block existed, the exterior would have exactly two distinct
protected vertices and at least one further vertex.  The block bounds would
then force a cut vertex.  The terminal-bridge argument applied on the
`z`-side of that cut produces the source's two-vertex `z`-end block.
Its cut vertex has exactly two exterior neighbours.  Claims 3.9 and 3.10
then force the second neighbour to have degree at least three, contradicting
the general degree bound under the no-feasible-block hypothesis.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/--
A connected graph of order at least three has a cut vertex whenever the
no-feasible-block bound makes every block have order at most two.
-/
private theorem exists_cut_of_no_feasibleBlock
    {D : SimpleGraph V}
    (hconnected : D.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock D,
        ¬IsFeasibleBlock D marked B)
    (horder : 3 ≤ Fintype.card V) :
    ∃ c : V, IsCutVertex D c := by
  by_contra hnoCutExists
  have hnoCut : HasNoCutVertex D := by
    intro c hcut
    exact hnoCutExists ⟨c, hcut⟩
  let B : GraphBlock D :=
    GraphBlock.ofConnectedHasNoCutVertex
      (by omega) hconnected hnoCut
  have hblockUpper :
      B.carrier.card ≤ 2 :=
    graphBlock_card_le_two_of_no_feasibleBlock
      hconnected marked hmarked hnoFeasible B
  have hblockCard :
      B.carrier.card = Fintype.card V := by
    simp [B]
  omega

/--
The exact protected-pair data forced by the negation of Claim 3.11.
-/
private theorem exterior_noFeasible_setup
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hnoFeasible :
      ∀ B : GraphBlock P.exteriorGraph,
        ¬IsFeasibleBlock
          P.exteriorGraph P.exteriorProtected B) :
    ∃ hz : z ∈ P.working.rooted.otherRegion,
      P.exteriorProtected =
          {P.exteriorY, P.exteriorZ hz} ∧
        ProtectedCutPair.Context
            P.exteriorGraph P.exteriorY
              (P.exteriorZ hz) ∧
          3 ≤ Fintype.card P.ExteriorVertex := by
  classical
  have horderTwo :
      2 ≤ Fintype.card P.ExteriorVertex := by
    have :=
      P.one_lt_exteriorVertex_card hregion
    omega
  have hprotectedNotSmall :
      ¬P.exteriorProtected.card ≤ 1 := by
    intro hsmall
    obtain ⟨B, hB⟩ :=
      exists_feasibleBlock_of_marked_card_le_one
        P.exteriorGraph_connected horderTwo
          P.exteriorProtected hsmall
    exact hnoFeasible B hB
  have hprotectedCard :
      P.exteriorProtected.card = 2 := by
    have hupper := P.exteriorProtected_card_le_two
    omega
  have hzRegion :
      z ∈ P.working.rooted.otherRegion := by
    by_contra hzRegion
    rw [
      P.exteriorProtected_eq_singleton_of_exception_not_mem
        hzRegion] at hprotectedCard
    simp at hprotectedCard
  have hyz :
      y ≠ z := by
    intro hyz
    have hyzSubtype :
        P.exteriorY = P.exteriorZ hzRegion := by
      apply Subtype.ext
      exact hyz
    rw [P.exteriorProtected_eq_pair hzRegion] at hprotectedCard
    simp [hyzSubtype] at hprotectedCard
  have hprotectedPair :
      P.exteriorProtected =
        {P.exteriorY, P.exteriorZ hzRegion} :=
    P.exteriorProtected_eq_pair hzRegion
  have C :
      ProtectedCutPair.Context
        P.exteriorGraph P.exteriorY
          (P.exteriorZ hzRegion) := {
    connected := P.exteriorGraph_connected
    distinct := by
      intro h
      exact hyz (congrArg Subtype.val h)
    noFeasible := by
      intro B
      rw [← hprotectedPair]
      exact hnoFeasible B
  }
  have horderThree :
      3 ≤ Fintype.card P.ExteriorVertex := by
    have hstrict :=
      P.exteriorProtected_card_lt_exteriorVertex_card
        M hregion
    omega
  exact
    ⟨hzRegion, hprotectedPair, C, horderThree⟩

/--
From any cut vertex, the terminal-bridge lemma produces a two-vertex
`z`-end block.  Its cut has a second neighbour on the `y`-side, while the
no-feasible-block degree bound gives the matching upper bound.
-/
private theorem exists_degreeTwo_terminalCertificate
    {D : SimpleGraph V} {a b : V}
    (C : ProtectedCutPair.Context D a b)
    (hexistsCut : ∃ c : V, IsCutVertex D c) :
    Nonempty (ZEndBlockCertificate D a b) := by
  classical
  obtain ⟨c, hcCut⟩ := hexistsCut
  have hcNeB :
      c ≠ b :=
    (C.cut_ne_marked hcCut).2
  let bDeleted :
      {v : V // v ∉ ({c} : Finset V)} :=
    ⟨b, by simpa using hcNeB.symm⟩
  let Qb :
      (deleteVertices D {c}).ConnectedComponent :=
    (deleteVertices D {c}).connectedComponentMk
      bDeleted
  have hbQ :
      b ∈ componentVertices D {c} Qb := by
    apply
      (mem_componentVertices_iff D {c} Qb b).2
    refine ⟨bDeleted.2, ?_⟩
    change
      (deleteVertices D {c}).connectedComponentMk
          bDeleted =
        Qb
    rfl
  obtain
      ⟨cut, hcutNeA, _hcutNeB, hcutCut,
        hbAdjCut, hleaf⟩ :=
    C.exists_terminalMarkedBridge hcCut Qb hbQ
  have hpairCard :
      ({a, b} : Finset V).card ≤ 2 := by
    simpa using
      (Finset.card_insert_le a ({b} : Finset V))
  have hcutDegreeUpper :
      finiteDegree D cut ≤ 2 :=
    finiteDegree_le_two_of_no_feasibleBlock
      C.connected ({a, b} : Finset V)
        hpairCard C.noFeasible cut
  let aDeleted :
      {v : V // v ∉ ({cut} : Finset V)} :=
    ⟨a, by simpa using hcutNeA.symm⟩
  let Qa :
      (deleteVertices D {cut}).ConnectedComponent :=
    (deleteVertices D {cut}).connectedComponentMk
      aDeleted
  have haQ :
      a ∈ componentVertices D {cut} Qa := by
    apply
      (mem_componentVertices_iff D {cut} Qa a).2
    refine ⟨aDeleted.2, ?_⟩
    change
      (deleteVertices D {cut}).connectedComponentMk
          aDeleted =
        Qa
    rfl
  have hbNotQ :
      b ∉ componentVertices D {cut} Qa := by
    rcases
        C.deletionComponent_contains_exactly_one
          hcutCut Qa with
      hcase | hcase
    · exact hcase.2
    · exact False.elim (hcase.2 haQ)
  obtain ⟨L, hLinner, hLcut⟩ :=
    LobeRegion.exists_ofComponent C.connected cut Qa
  obtain ⟨w, hwInner, hcutAdjW⟩ :=
    L.cut_adj_inner
  have hwQ :
      w ∈ componentVertices D {cut} Qa := by
    rw [← hLinner]
    exact hwInner
  have hwNeB :
      w ≠ b := by
    intro hwb
    apply hbNotQ
    simpa [hwb] using hwQ
  have hcutAdjW' :
      D.Adj cut w := by
    simpa [hLcut] using hcutAdjW
  have hpairSubset :
      ({b, w} : Set V) ⊆ D.neighborSet cut := by
    intro v hv
    simp only [
      Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hbAdjCut.symm
    · exact hcutAdjW'
  have hcutDegreeLower :
      2 ≤ finiteDegree D cut := by
    unfold finiteDegree
    calc
      2 = ({b, w} : Set V).ncard := by
        symm
        exact Set.ncard_pair hwNeB.symm
      _ ≤ (D.neighborSet cut).ncard :=
        Set.ncard_le_ncard hpairSubset
  have hcutDegree :
      finiteDegree D cut = 2 := by
    omega
  exact
    ⟨{
      connected := C.connected
      bz := cut
      y_ne_z := C.distinct
      y_ne_bz := hcutNeA.symm
      z_adj_bz := hbAdjCut
      leaf_component := hleaf
      bz_degree_two := hcutDegree
    }⟩

/--
COY Claim 3.11: every nonsingleton selected exterior contains a block
feasible relative to the protected vertices `y` and `z`.
-/
theorem exists_feasible_exterior_block
    (M : MinimalCounterexample q G x y z)
    (P : PreferredWorkingCoreData G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    ∃ B : GraphBlock P.exteriorGraph,
      IsFeasibleBlock
        P.exteriorGraph P.exteriorProtected B := by
  classical
  by_contra hnoFeasible
  push Not at hnoFeasible
  obtain
      ⟨hzRegion, _hprotectedPair, C, horderThree⟩ :=
    exterior_noFeasible_setup M P hregion hnoFeasible
  have hexistsCut :
      ∃ c : P.ExteriorVertex,
        IsCutVertex P.exteriorGraph c :=
    exists_cut_of_no_feasibleBlock
      P.exteriorGraph_connected P.exteriorProtected
        P.exteriorProtected_card_le_two hnoFeasible
        horderThree
  obtain ⟨certificate⟩ :=
    exists_degreeTwo_terminalCertificate C hexistsCut
  let E : P.ExteriorZEndBlock := {
    z_mem_otherRegion := hzRegion
    certificate := certificate
  }
  have hPrimeY :
      E.bPrime ≠ y :=
    E.bPrime_ne_y_of_no_feasibleBlock M hnoFeasible
  have hPrimeDegree :
      3 ≤ finiteDegree P.exteriorGraph
        E.certificate.bPrime :=
    E.three_le_exterior_degree_bPrime M hPrimeY
  obtain ⟨B, hB⟩ :=
    exists_feasibleBlock_of_three_le_finiteDegree
      P.exteriorGraph_connected P.exteriorProtected
        P.exteriorProtected_card_le_two
        E.certificate.bPrime hPrimeDegree
  exact hnoFeasible B hB

end PreferredWorkingCoreData

end COY

end DeanK5
