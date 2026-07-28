import DeanK5.COYExteriorBlockCandidates
import DeanK5.Graph.OrderedBlockChainNeighbors
import DeanK5.COYExteriorFinalRootNeighborhood

/-!
# From the exterior block chain to the final degree contradiction

The ordered block chain lives in the graph induced by the selected exterior
component, whereas the last degree comparison is made in the ambient graph.
This file supplies the missing bridge.

If the final block has two vertices, every ambient neighbour of `y` outside
the selected core is the final cut vertex.  If the final two blocks both have
two vertices, every ambient neighbour of that cut vertex lies either in the
selected core or is `y` or the preceding cut vertex.  Explicit exclusion of
the core root and the terminal side then leaves only the singleton `S`-side,
which is exactly the final degree certificate.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorOrderedBlockChain

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/-- The index of the cut vertex in the final two blocks of the chain. -/
def terminalCutIndex
    (O : P.ExteriorOrderedBlockChain) :
    Fin O.chain.cutCount :=
  ⟨O.chain.cutCount - 1, by
    have := O.chain.one_le_cutCount
    omega⟩

/-- The final cut vertex, viewed in the ambient graph. -/
abbrev terminalCut
    (O : P.ExteriorOrderedBlockChain) : V :=
  (O.chain.cuts O.terminalCutIndex).1.1

/-- The index of the cut immediately preceding the final cut. -/
def preterminalCutIndex
    (O : P.ExteriorOrderedBlockChain)
    (htwoCuts : 2 ≤ O.chain.cutCount) :
    Fin O.chain.cutCount :=
  ⟨O.chain.cutCount - 2, by omega⟩

/-- The cut immediately preceding the final cut, in the ambient graph. -/
abbrev preterminalCut
    (O : P.ExteriorOrderedBlockChain)
    (htwoCuts : 2 ≤ O.chain.cutCount) : V :=
  (O.chain.cuts (O.preterminalCutIndex htwoCuts)).1.1

/--
If the final exterior block has two vertices, every ambient neighbour of
`y` outside the selected core is the final cut vertex.

The component-region closure first puts the neighbour back in the exterior;
the induced-chain theorem then identifies it with the final cut.
-/
theorem ambient_neighbor_eq_terminalCut_of_not_mem_core
    (O : P.ExteriorOrderedBlockChain)
    (hlastCard :
      (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2)
    {v : V}
    (hyv : G.Adj y v)
    (hvCore : v ∉ P.working.rooted.core.carrier) :
    v = O.terminalCut := by
  have hvRegion :
      v ∈ P.working.rooted.otherRegion :=
    P.working.rooted.otherRegion_componentRegion.closed
      P.working.rooted.other_root_mem_otherRegion
      hyv hvCore
  let vE : P.ExteriorVertex := ⟨v, hvRegion⟩
  have hyvExterior :
      P.exteriorGraph.Adj P.exteriorY vE :=
    hyv
  have hvLastCut :=
    O.chain.lastBlock_neighborSet_subset_lastCut
      P.exteriorGraph_connected
      (by
        simpa [ExteriorOrderedBlockChain.lastIndex] using
          O.y_mem_last_block)
      O.y_not_cut hlastCard hyvExterior
  have hvEq :
      vE =
        (O.chain.cuts O.terminalCutIndex).1 := by
    simpa [terminalCutIndex] using hvLastCut
  exact congrArg Subtype.val hvEq

/--
The preceding theorem supplies the exterior-envelope premise of the final
root-degree sandwich.
-/
theorem root_degree_sandwich_of_terminal_block
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    {s a : V}
    (hS : D.core.S = {s})
    (hxa : G.Adj x a)
    (haT : a ∉ D.core.T)
    (hlastCard :
      (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2) :
    finiteDegree G x = D.core.T.card + 1 ∧
      finiteDegree G y = D.core.T.card + 1 ∧
      G.neighborSet y =
        (↑(insert O.terminalCut D.core.T) : Set V) := by
  apply D.root_degree_sandwich_of_core_envelope
    M hS hxa haT
  intro v hyv hvCore
  exact
    O.ambient_neighbor_eq_terminalCut_of_not_mem_core
      hlastCard hyv hvCore

/--
If the last feasible block occurs before the terminal block, maximality makes
the terminal block a two-vertex block.
-/
theorem terminal_block_card_eq_two_of_lastFeasible_before
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 <
        O.chain.cutCount) :
    (O.chain.blocks
      ⟨O.chain.cutCount, by omega⟩).carrier.card = 2 := by
  let K := O.toCandidateChain
  have hbeforeK :
      (K.lastFeasibleIndex M hregion).1 <
        K.chain.cutCount := by
    simpa [K, toCandidateChain] using hbefore
  have hlater :
      K.lastFeasibleIndex M hregion <
        (⟨K.chain.cutCount, by omega⟩ :
          Fin (K.chain.cutCount + 1)) := by
    exact hbeforeK
  have hcard :=
    K.later_block_card_eq_two
      M hregion hall
      (⟨K.chain.cutCount, by omega⟩ :
        Fin (K.chain.cutCount + 1))
      hlater
  simpa [K, toCandidateChain] using hcard

/--
Candidate maximality and the final-block bridge together give the root-degree
sandwich as soon as the last feasible block is nonterminal.
-/
theorem root_degree_sandwich_of_lastFeasible_before
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    {s a : V}
    (hS : D.core.S = {s})
    (hxa : G.Adj x a)
    (haT : a ∉ D.core.T)
    (hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 <
        O.chain.cutCount) :
    finiteDegree G x = D.core.T.card + 1 ∧
      finiteDegree G y = D.core.T.card + 1 ∧
      G.neighborSet y =
        (↑(insert O.terminalCut D.core.T) : Set V) :=
  O.root_degree_sandwich_of_terminal_block
    M D hS hxa haT
    (O.terminal_block_card_eq_two_of_lastFeasible_before
      M hregion hall hbefore)

/--
If the last feasible block occurs before the penultimate block, the final two
blocks both have order two.
-/
theorem terminal_two_blocks_card_eq_two_of_lastFeasible_before
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (htwoCuts : 2 ≤ O.chain.cutCount)
    (hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 + 1 <
        O.chain.cutCount) :
    (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2 ∧
      (O.chain.blocks
        ⟨O.chain.cutCount - 1, by omega⟩).carrier.card = 2 := by
  let K := O.toCandidateChain
  have hbeforeK :
      (K.lastFeasibleIndex M hregion).1 + 1 <
        K.chain.cutCount := by
    simpa [K, toCandidateChain] using hbefore
  have hlast :
      (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2 :=
    O.terminal_block_card_eq_two_of_lastFeasible_before
      M hregion hall (by omega)
  have hpreviousLater :
      K.lastFeasibleIndex M hregion <
        (⟨K.chain.cutCount - 1, by omega⟩ :
          Fin (K.chain.cutCount + 1)) := by
    change
      (K.lastFeasibleIndex M hregion).1 <
        K.chain.cutCount - 1
    omega
  have hprevious :=
    K.later_block_card_eq_two
      M hregion hall
      (⟨K.chain.cutCount - 1, by omega⟩ :
        Fin (K.chain.cutCount + 1))
      hpreviousLater
  exact ⟨hlast, by
    simpa [K, toCandidateChain] using hprevious⟩

/--
If the final two exterior blocks have order two, every ambient neighbour of
the final cut is either `y`, the preceding cut, or a selected-core vertex.
-/
theorem terminalCut_neighborSet_subset_pair_union_core
    (O : P.ExteriorOrderedBlockChain)
    (htwoCuts : 2 ≤ O.chain.cutCount)
    (hlastCard :
      (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2)
    (hpreviousCard :
      (O.chain.blocks
        ⟨O.chain.cutCount - 1, by omega⟩).carrier.card = 2) :
    G.neighborSet O.terminalCut ⊆
      ({y, O.preterminalCut htwoCuts} : Set V) ∪
        (↑P.working.rooted.core.carrier : Set V) := by
  intro v hbv
  by_cases hvCore : v ∈ P.working.rooted.core.carrier
  · exact Or.inr hvCore
  · have hbRegion :
        O.terminalCut ∈ P.working.rooted.otherRegion :=
      (O.chain.cuts O.terminalCutIndex).1.2
    have hvRegion :
        v ∈ P.working.rooted.otherRegion :=
      P.working.rooted.otherRegion_componentRegion.closed
        hbRegion hbv hvCore
    let vE : P.ExteriorVertex := ⟨v, hvRegion⟩
    have hbvExterior :
        P.exteriorGraph.Adj
          (O.chain.cuts O.terminalCutIndex).1 vE :=
      hbv
    have hvPair :=
      O.chain.penultimateCut_neighborSet_subset
        O.incidence_degree_le_two htwoCuts
        (by
          simpa [ExteriorOrderedBlockChain.lastIndex] using
            O.y_mem_last_block)
        O.y_not_cut hlastCard hpreviousCard hbvExterior
    apply Or.inl
    rcases
        (show
          vE = P.exteriorY ∨
            vE =
              (O.chain.cuts
                (O.preterminalCutIndex htwoCuts)).1 by
          simpa [terminalCutIndex, preterminalCutIndex] using
            hvPair) with
      hvy | hvPrevious
    · exact Or.inl (congrArg Subtype.val hvy)
    · exact Or.inr (congrArg Subtype.val hvPrevious)

/--
After excluding adjacency from the final cut to the core root and to the
terminal side, a singleton `S`-side is the only possible remaining core
neighbour.
-/
theorem terminalCut_neighborSet_subset_three
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    {s : V}
    (hS : D.core.S = {s})
    (htwoCuts : 2 ≤ O.chain.cutCount)
    (hlastCard :
      (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2)
    (hpreviousCard :
      (O.chain.blocks
        ⟨O.chain.cutCount - 1, by omega⟩).carrier.card = 2)
    (hnoRoot : ¬G.Adj O.terminalCut x)
    (hnoTerminal :
      ∀ t ∈ D.core.T, ¬G.Adj O.terminalCut t) :
    G.neighborSet O.terminalCut ⊆
      (↑({y, O.preterminalCut htwoCuts, s} : Finset V) :
        Set V) := by
  intro v hbv
  have hvEnvelope :=
    O.terminalCut_neighborSet_subset_pair_union_core
      htwoCuts hlastCard hpreviousCard hbv
  rcases hvEnvelope with hvPair | hvCore
  · rcases hvPair with hvy | hvPrevious
    · simp [hvy]
    · have hvPreviousEq :
          v = O.preterminalCut htwoCuts := by
        simpa only [Set.mem_singleton_iff] using hvPrevious
      simp [hvPreviousEq]
  · by_cases hvx : v = x
    · subst v
      exact False.elim (hnoRoot hbv)
    · have hvParts :
          v ∈ D.core.S ∨ v ∈ D.core.T := by
        simpa [D.core_eq, Core.S, Core.T] using
          (P.working.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
            hvCore hvx)
      rcases hvParts with hvS | hvT
      · have hvs : v = s := by
          rw [hS] at hvS
          simpa using hvS
        simp [hvs]
      · exact False.elim (hnoTerminal v hvT hbv)

/-- The final cut lies outside the selected core, hence is not the root. -/
theorem terminalCut_ne_root
    (O : P.ExteriorOrderedBlockChain) :
    O.terminalCut ≠ x := by
  intro h
  have hbRegion :
      O.terminalCut ∈ P.working.rooted.otherRegion :=
    (O.chain.cuts O.terminalCutIndex).1.2
  have hbNotCore :=
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      hbRegion
  apply hbNotCore
  simp [h]

/-- The final cut is distinct from the non-cut exterior endpoint `y`. -/
theorem terminalCut_ne_y
    (O : P.ExteriorOrderedBlockChain) :
    O.terminalCut ≠ y := by
  intro h
  apply O.y_not_cut
  have hbCut :
      IsCutVertex P.exteriorGraph
        (O.chain.cuts O.terminalCutIndex).1 :=
    (O.chain.cuts O.terminalCutIndex).2
  have hbEq :
      (O.chain.cuts O.terminalCutIndex).1 =
        P.exteriorY :=
    Subtype.ext h
  exact hbEq ▸ hbCut

/-- The final cut is distinct from the non-cut exterior endpoint `z`. -/
theorem terminalCut_ne_exception
    (O : P.ExteriorOrderedBlockChain) :
    O.terminalCut ≠ z := by
  intro h
  apply O.z_not_cut
  have hbCut :
      IsCutVertex P.exteriorGraph
        (O.chain.cuts O.terminalCutIndex).1 :=
    (O.chain.cuts O.terminalCutIndex).2
  have hbEq :
      (O.chain.cuts O.terminalCutIndex).1 =
        P.exteriorZ O.endpoints.z_mem_otherRegion :=
    Subtype.ext h
  exact hbEq ▸ hbCut

/--
Package the two terminal two-vertex blocks and the explicit core-neighbour
exclusions as the certificate consumed by the final degree contradiction.
-/
def finalDegreeCertificate
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    {s : V}
    (hS : D.core.S = {s})
    (htwoCuts : 2 ≤ O.chain.cutCount)
    (hlastCard :
      (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2)
    (hpreviousCard :
      (O.chain.blocks
        ⟨O.chain.cutCount - 1, by omega⟩).carrier.card = 2)
    (hnoRoot : ¬G.Adj O.terminalCut x)
    (hnoTerminal :
      ∀ t ∈ D.core.T, ¬G.Adj O.terminalCut t) :
    ExteriorFinalDegreeCertificate G x y z where
  bottleneck := O.terminalCut
  predecessor := O.preterminalCut htwoCuts
  side := s
  bottleneck_ne_x := O.terminalCut_ne_root
  bottleneck_ne_y := O.terminalCut_ne_y
  bottleneck_ne_z := O.terminalCut_ne_exception
  neighborSet_subset :=
    O.terminalCut_neighborSet_subset_three
      D hS htwoCuts hlastCard hpreviousCard
        hnoRoot hnoTerminal

/--
High-level certificate constructor using the last-feasible-block index.
The strict inequality is the source condition `p < t - 1`.
-/
def finalDegreeCertificateOfLastFeasibleBefore
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    {s : V}
    (hS : D.core.S = {s})
    (htwoCuts : 2 ≤ O.chain.cutCount)
    (hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 + 1 <
        O.chain.cutCount)
    (hnoRoot : ¬G.Adj O.terminalCut x)
    (hnoTerminal :
      ∀ t ∈ D.core.T, ¬G.Adj O.terminalCut t) :
    ExteriorFinalDegreeCertificate G x y z := by
  obtain ⟨hlastCard, hpreviousCard⟩ :=
    O.terminal_two_blocks_card_eq_two_of_lastFeasible_before
      M hregion hall htwoCuts hbefore
  exact
    O.finalDegreeCertificate D hS htwoCuts
      hlastCard hpreviousCard hnoRoot hnoTerminal

/--
The terminal two-block configuration is impossible once Claim 3.16 has
excluded the core root and terminal side from the final cut's neighbourhood.
-/
theorem false_of_terminal_two_blocks
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    {s : V}
    (hS : D.core.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (htwoCuts : 2 ≤ O.chain.cutCount)
    (hlastCard :
      (O.chain.blocks
        ⟨O.chain.cutCount, by omega⟩).carrier.card = 2)
    (hpreviousCard :
      (O.chain.blocks
        ⟨O.chain.cutCount - 1, by omega⟩).carrier.card = 2)
    (hnoRoot : ¬G.Adj O.terminalCut x)
    (hnoTerminal :
      ∀ t ∈ D.core.T, ¬G.Adj O.terminalCut t) :
    False :=
  ExteriorFinalDegreeCertificate.false_of_typeThree_singleton_side
    M D hS hregion
    (O.finalDegreeCertificate D hS htwoCuts hlastCard
      hpreviousCard hnoRoot hnoTerminal)

/--
High-level final contradiction from the source inequality `p < t - 1`.
-/
theorem false_of_lastFeasible_before_preterminal
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    {s : V}
    (hS : D.core.S = {s})
    (htwoCuts : 2 ≤ O.chain.cutCount)
    (hbefore :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 + 1 <
        O.chain.cutCount)
    (hnoRoot : ¬G.Adj O.terminalCut x)
    (hnoTerminal :
      ∀ t ∈ D.core.T, ¬G.Adj O.terminalCut t) :
    False :=
  ExteriorFinalDegreeCertificate.false_of_typeThree_singleton_side
    M D hS hregion
    (O.finalDegreeCertificateOfLastFeasibleBefore
      M D hregion hall hS htwoCuts hbefore
        hnoRoot hnoTerminal)

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
