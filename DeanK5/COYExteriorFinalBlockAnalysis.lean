import DeanK5.COYExteriorFinalNonterminal
import DeanK5.COYExteriorFinalTerminal

/-!
# Final last-feasible-block analysis

The last feasible exterior block is either the terminal block or occurs
strictly before it.  The two branch closures therefore eliminate the
selected minimal counterexample.
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

/--
The terminal and nonterminal last-feasible-block branches are both
impossible.
-/
theorem false_of_lastFeasible_analysis
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior) :
    False := by
  by_cases hterminal :
      (O.toCandidateChain.lastFeasibleIndex M hregion).1 =
        O.chain.cutCount
  · let L :=
      O.terminalFeasibleAnchor
        M hregion hterminal
    exact
      O.false_of_terminal_lastFeasible
        M D hregion hall L
  · have hbefore :
        (O.toCandidateChain.lastFeasibleIndex M hregion).1 <
          O.chain.cutCount := by
      have hbound :=
        (O.toCandidateChain.lastFeasibleIndex
          M hregion).2
      have hbound' :
          (O.toCandidateChain.lastFeasibleIndex
            M hregion).1 <
              O.chain.cutCount + 1 := by
        simpa [ExteriorOrderedBlockChain.toCandidateChain] using
          hbound
      omega
    let L :=
      O.lastFeasibleAnchor
        M hregion hbefore
    exact
      O.false_of_nonterminal_lastFeasible
        M D hregion hall L

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
