import DeanK5.COYExteriorClaimThreeSixteenBlock
import DeanK5.COYExteriorTerminalFeasibleAnchor

/-!
# Terminal selected-block geometry in COY Claim 3.16

When the last feasible block is the final block of the ordered exterior
chain, the recursive interfaces are the final cut on the left and `y` on
the right.  Cut-node exhaustiveness shows that the final cut is the only cut
vertex in this block.  Endpoint uniqueness excludes `z` from every other
block vertex, while the terminal version of equation (3.4) excludes
attachments from the `T`-side away from `y`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

namespace ExteriorTerminalFeasibleAnchor

variable
  {M : MinimalCounterexample q G x y z}
  {P : PreferredWorkingCoreData G x y z}
  {O : P.ExteriorOrderedBlockChain}
  {hregion : P.working.rooted.otherRegion ≠ {y}}

/--
The final cut is the only exterior cut vertex contained in the terminal
chain block.
-/
theorem cut_eq_finalCut_of_mem_terminalBlock
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    {d : P.ExteriorVertex}
    (hdmem :
      d ∈ (O.chain.blocks O.lastIndex).carrier)
    (hdcut : IsCutVertex P.exteriorGraph d) :
    d =
      (O.chain.cuts
        ⟨O.chain.cutCount - 1, by
          rw [← L.index_eq_cutCount]
          omega⟩).1 := by
  let c :
      {v : P.ExteriorVertex //
        IsCutVertex P.exteriorGraph v} :=
    ⟨d, hdcut⟩
  obtain ⟨k, hk⟩ :=
    O.chain.cuts_exhaustive c
  have hcutMem :
      (O.chain.cuts k).1 ∈
        (O.chain.blocks O.lastIndex).carrier := by
    rw [hk]
    exact hdmem
  have hblockCases :=
    O.chain.block_eq_left_or_right_of_cut_mem
      O.incidence_degree_le_two k
      (O.chain.blocks O.lastIndex) hcutMem
  rcases hblockCases with hleft | hright
  · have hindex :
        O.lastIndex =
          (⟨k.1, by omega⟩ :
            Fin (O.chain.cutCount + 1)) :=
      O.chain.blocks_injective hleft
    have hvalues :
        O.chain.cutCount = k.1 :=
      congrArg
        (fun i : Fin (O.chain.cutCount + 1) => i.1)
        hindex
    have hkBound := k.2
    omega
  · have hindex :
        O.lastIndex =
          (⟨k.1 + 1, by omega⟩ :
            Fin (O.chain.cutCount + 1)) :=
      O.chain.blocks_injective hright
    have hvalues :
        O.chain.cutCount = k.1 + 1 :=
      congrArg
        (fun i : Fin (O.chain.cutCount + 1) => i.1)
        hindex
    have hkFinal :
        k =
          (⟨O.chain.cutCount - 1, by
            rw [← L.index_eq_cutCount]
            omega⟩ :
            Fin O.chain.cutCount) := by
      apply Fin.ext
      change k.1 = O.chain.cutCount - 1
      omega
    have hvalue :
        (O.chain.cuts k).1 = d :=
      congrArg Subtype.val hk
    simpa [hkFinal] using hvalue.symm

/--
No vertex of the terminal block represents the exceptional endpoint `z`.
-/
theorem ambient_ne_z_of_mem_terminalBlock
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    {d : P.ExteriorVertex}
    (hdmem :
      d ∈ (O.chain.blocks O.lastIndex).carrier) :
    d.1 ≠ z := by
  intro hdz
  have hdZ :
      d =
        P.exteriorZ O.endpoints.z_mem_otherRegion :=
    Subtype.ext hdz
  have hzMem :
      P.exteriorZ O.endpoints.z_mem_otherRegion ∈
        (O.chain.blocks O.lastIndex).carrier := by
    simpa [hdZ] using hdmem
  have hindex :
      O.lastIndex = O.firstIndex :=
    O.chain.block_index_eq_of_noncut_mem
      P.exteriorGraph_connected O.z_not_cut
      O.lastIndex O.firstIndex
      hzMem O.z_mem_first_block
  have hvalues :
      O.chain.cutCount = 0 :=
    congrArg
      (fun i : Fin (O.chain.cutCount + 1) => i.1)
      hindex
  have hcutPositive :
      0 < O.chain.cutCount := by
    rw [← L.index_eq_cutCount]
    exact hpositive
  omega

/--
The terminal block, with final cut and `y` as its two recursive interfaces,
supplies the selected-block data used in Claim 3.16.
-/
noncomputable def claimThreeSixteenTerminalBlockData
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    P.ClaimThreeSixteenBlockData D := by
  let leftIndex : Fin O.chain.cutCount :=
    ⟨O.chain.cutCount - 1, by
      rw [← L.index_eq_cutCount]
      omega⟩
  let left : P.ExteriorVertex :=
    (O.chain.cuts leftIndex).1
  let right : P.ExteriorVertex :=
    P.exteriorY
  have hleftMem :
      left ∈
        (O.chain.blocks O.lastIndex).carrier := by
    have hmem :=
      O.chain.cut_mem_right leftIndex
    have hindex :
        (⟨leftIndex.1 + 1, by omega⟩ :
          Fin (O.chain.cutCount + 1)) =
        O.lastIndex := by
      apply Fin.ext
      dsimp [leftIndex,
        ExteriorOrderedBlockChain.lastIndex]
      have hcutPositive :
          0 < O.chain.cutCount := by
        rw [← L.index_eq_cutCount]
        exact hpositive
      omega
    rw [hindex] at hmem
    exact hmem
  have hrightMem :
      right ∈
        (O.chain.blocks O.lastIndex).carrier := by
    simpa [right] using O.y_mem_last_block
  have hrootsNe :
      left ≠ right := by
    intro heq
    apply O.y_not_cut
    have hleftCut :
        IsCutVertex P.exteriorGraph left :=
      (O.chain.cuts leftIndex).2
    simpa [heq, right] using hleftCut
  have hlarge :
      3 ≤
        (O.chain.blocks O.lastIndex).carrier.card := by
    have hchoiceLarge :=
      L.choice.three_le_carrier_card_of_meetsProtectedInterior
        (hall L.choice)
    rw [L.block_eq_last] at hchoiceLarge
    exact hchoiceLarge
  refine {
    block := O.chain.blocks O.lastIndex
    left := left
    right := right
    left_mem := hleftMem
    right_mem := hrightMem
    left_isCut := (O.chain.cuts leftIndex).2
    roots_ne := hrootsNe
    three_le_card := hlarge
    ordinary_not_cut := ?_
    ordinary_ne_y := ?_
    ordinary_ne_z := ?_
    no_terminal_attachment := ?_
  }
  · intro d hdmem hdleft _ hdcut
    have hdfinal :=
      L.cut_eq_finalCut_of_mem_terminalBlock
        hpositive hdmem hdcut
    exact hdleft (by
      simpa [left, leftIndex] using hdfinal)
  · intro d _ _ hdright hdy
    apply hdright
    apply Subtype.ext
    exact hdy
  · intro d hdmem _ _ hdz
    exact
      L.ambient_ne_z_of_mem_terminalBlock
        hpositive hdmem hdz
  · intro d hdmem hdright t ht
    have hdAmbient :
        d.1 ∈ L.choice.ambientCarrier := by
      apply L.choice.mem_ambientCarrier.mpr
      refine ⟨d, ?_, rfl⟩
      simpa [L.block_eq_last] using hdmem
    have hdNeY :
        d.1 ≠ y := by
      intro hdy
      apply hdright
      apply Subtype.ext
      exact hdy
    have htWorking :
        t ∈ P.working.rooted.core.T := by
      simpa [D.core_eq, Core.T] using ht
    exact
      L.equation_three_four
        t htWorking d.1 hdAmbient hdNeY

@[simp] theorem claimThreeSixteenTerminalBlockData_block
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    (L.claimThreeSixteenTerminalBlockData
      D hall hpositive).block =
      O.chain.blocks O.lastIndex :=
  rfl

@[simp] theorem claimThreeSixteenTerminalBlockData_left
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    (L.claimThreeSixteenTerminalBlockData
      D hall hpositive).left =
      (O.chain.cuts
        ⟨O.chain.cutCount - 1, by
          rw [← L.index_eq_cutCount]
          omega⟩).1 :=
  rfl

@[simp] theorem claimThreeSixteenTerminalBlockData_right
    (L : P.ExteriorTerminalFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    (L.claimThreeSixteenTerminalBlockData
      D hall hpositive).right =
      P.exteriorY :=
  rfl

end ExteriorTerminalFeasibleAnchor

end PreferredWorkingCoreData

end COY

end DeanK5
