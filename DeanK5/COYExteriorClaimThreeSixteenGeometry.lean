import DeanK5.COYExteriorClaimThreeSixteenBlock
import DeanK5.COYExteriorLastFeasibleAnchor

/-!
# The selected block geometry in COY Claim 3.16

In the interior branch of the last-feasible-block argument, the selected
block `B_p` has precisely the two consecutive chain cuts as its interfaces.
This file derives the concrete `ClaimThreeSixteenBlockData` package from the
ordered exterior chain and the source-oriented last-feasible anchor.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

namespace ExteriorLastFeasibleAnchor

variable
  {M : MinimalCounterexample q G x y z}
  {P : PreferredWorkingCoreData G x y z}
  {O : P.ExteriorOrderedBlockChain}
  {hregion : P.working.rooted.otherRegion ≠ {y}}

/--
Every exterior cut vertex in the selected interior block is one of its two
displayed chain interfaces.
-/
theorem cut_eq_left_or_right_of_mem_selected
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    {d : P.ExteriorVertex}
    (hdmem :
      d ∈ (O.chain.blocks L.index).carrier)
    (hdcut : IsCutVertex P.exteriorGraph d) :
    d =
        (O.chain.cuts
          ⟨L.index.1 - 1, by omega⟩).1 ∨
      d =
        (O.chain.cuts
          ⟨L.index.1, L.index_lt_cutCount⟩).1 := by
  let c :
      {v : P.ExteriorVertex //
        IsCutVertex P.exteriorGraph v} :=
    ⟨d, hdcut⟩
  obtain ⟨k, hk⟩ :=
    O.chain.cuts_exhaustive c
  have hcutMem :
      (O.chain.cuts k).1 ∈
        (O.chain.blocks L.index).carrier := by
    rw [hk]
    exact hdmem
  have hblockCases :=
    O.chain.block_eq_left_or_right_of_cut_mem
      O.incidence_degree_le_two k
      (O.chain.blocks L.index) hcutMem
  rcases hblockCases with hleft | hright
  · have hindex :
        L.index =
          (⟨k.1, by omega⟩ :
            Fin (O.chain.cutCount + 1)) :=
      O.chain.blocks_injective hleft
    have hvalues :
        L.index.1 = k.1 :=
      congrArg
        (fun i : Fin (O.chain.cutCount + 1) => i.1)
        hindex
    have hkRight :
        k =
          (⟨L.index.1, L.index_lt_cutCount⟩ :
            Fin O.chain.cutCount) := by
      apply Fin.ext
      exact hvalues.symm
    right
    have hvalue :
        (O.chain.cuts k).1 = d :=
      congrArg Subtype.val hk
    simpa [hkRight] using hvalue.symm
  · have hindex :
        L.index =
          (⟨k.1 + 1, by omega⟩ :
            Fin (O.chain.cutCount + 1)) :=
      O.chain.blocks_injective hright
    have hvalues :
        L.index.1 = k.1 + 1 :=
      congrArg
        (fun i : Fin (O.chain.cutCount + 1) => i.1)
        hindex
    have hkLeft :
        k =
          (⟨L.index.1 - 1, by omega⟩ :
            Fin O.chain.cutCount) := by
      apply Fin.ext
      change k.1 = L.index.1 - 1
      omega
    left
    have hvalue :
        (O.chain.cuts k).1 = d :=
      congrArg Subtype.val hk
    simpa [hkLeft] using hvalue.symm

/--
The selected interior block contains no exterior vertex representing the
ambient second root `y`.
-/
theorem ambient_ne_y_of_mem_selected
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    {d : P.ExteriorVertex}
    (hdmem :
      d ∈ (O.chain.blocks L.index).carrier) :
    d.1 ≠ y := by
  intro hdy
  have hdY :
      d = P.exteriorY :=
    Subtype.ext hdy
  have hyMem :
      P.exteriorY ∈
        (O.chain.blocks L.index).carrier := by
    simpa [hdY] using hdmem
  have hindex :
      L.index = O.lastIndex :=
    O.chain.block_index_eq_of_noncut_mem
      P.exteriorGraph_connected O.y_not_cut
      L.index O.lastIndex hyMem O.y_mem_last_block
  have hvalues :
      L.index.1 = O.chain.cutCount :=
    congrArg
      (fun i : Fin (O.chain.cutCount + 1) => i.1)
      hindex
  exact (Nat.ne_of_lt L.index_lt_cutCount) hvalues

/--
At a positive index, the selected block contains no exterior vertex
representing the ambient exceptional vertex `z`.
-/
theorem ambient_ne_z_of_mem_selected
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (hpositive : 0 < L.index.1)
    {d : P.ExteriorVertex}
    (hdmem :
      d ∈ (O.chain.blocks L.index).carrier) :
    d.1 ≠ z := by
  intro hdz
  have hdZ :
      d =
        P.exteriorZ O.endpoints.z_mem_otherRegion :=
    Subtype.ext hdz
  have hzMem :
      P.exteriorZ O.endpoints.z_mem_otherRegion ∈
        (O.chain.blocks L.index).carrier := by
    simpa [hdZ] using hdmem
  have hindex :
      L.index = O.firstIndex :=
    O.chain.block_index_eq_of_noncut_mem
      P.exteriorGraph_connected O.z_not_cut
      L.index O.firstIndex hzMem O.z_mem_first_block
  have hvalues :
      L.index.1 = 0 :=
    congrArg
      (fun i : Fin (O.chain.cutCount + 1) => i.1)
      hindex
  omega

/--
The exact selected-block package used by the recursive stage of Claim 3.16.

The hypothesis `0 < L.index.1` places `B_p` strictly after the first block;
the defining data of `L` already place it strictly before the last block.
-/
noncomputable def claimThreeSixteenBlockData
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    P.ClaimThreeSixteenBlockData D := by
  let leftIndex : Fin O.chain.cutCount :=
    ⟨L.index.1 - 1, by omega⟩
  let rightIndex : Fin O.chain.cutCount :=
    ⟨L.index.1, L.index_lt_cutCount⟩
  let left : P.ExteriorVertex :=
    (O.chain.cuts leftIndex).1
  let right : P.ExteriorVertex :=
    (O.chain.cuts rightIndex).1
  have hleftMem :
      left ∈
        (O.chain.blocks L.index).carrier := by
    have hmem :=
      O.chain.cut_mem_right leftIndex
    have hindex :
        (⟨leftIndex.1 + 1, by omega⟩ :
          Fin (O.chain.cutCount + 1)) =
        L.index := by
      apply Fin.ext
      dsimp [leftIndex]
      omega
    rw [hindex] at hmem
    exact hmem
  have hrightMem :
      right ∈
        (O.chain.blocks L.index).carrier := by
    simpa [right, rightIndex] using
      O.chain.cut_mem_left rightIndex
  have hrootsNe :
      left ≠ right := by
    intro heq
    have hcuts :
        O.chain.cuts leftIndex =
          O.chain.cuts rightIndex :=
      Subtype.ext heq
    have hindices :
        leftIndex = rightIndex :=
      O.chain.cuts_injective hcuts
    have hvalues :
        leftIndex.1 = rightIndex.1 :=
      congrArg
        (fun i : Fin O.chain.cutCount => i.1)
        hindices
    dsimp [leftIndex, rightIndex] at hvalues
    omega
  have hlarge :
      3 ≤
        (O.chain.blocks L.index).carrier.card := by
    have hchoiceLarge :=
      L.choice.three_le_carrier_card_of_meetsProtectedInterior
        (hall L.choice)
    simpa [L.block_eq] using hchoiceLarge
  refine {
    block := O.chain.blocks L.index
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
  · intro d hdmem hdleft hdright hdcut
    rcases
        L.cut_eq_left_or_right_of_mem_selected
          hpositive hdmem hdcut with
      hdl | hdr
    · exact hdleft (by simpa [left, leftIndex] using hdl)
    · exact hdright (by simpa [right, rightIndex] using hdr)
  · intro d hdmem _ _
    exact L.ambient_ne_y_of_mem_selected hdmem
  · intro d hdmem _ _
    exact L.ambient_ne_z_of_mem_selected hpositive hdmem
  · intro d hdmem hdright t ht
    have hdAmbient :
        d.1 ∈ L.choice.ambientCarrier := by
      apply L.choice.mem_ambientCarrier.mpr
      refine ⟨d, ?_, rfl⟩
      simpa [L.block_eq] using hdmem
    have hdAnchor :
        d.1 ≠ L.choice.b := by
      intro h
      apply hdright
      apply Subtype.ext
      have hb :=
        L.b_eq_rightCut
      simpa [right, rightIndex] using h.trans hb
    have htWorking :
        t ∈ P.working.rooted.core.T := by
      simpa [D.core_eq, Core.T] using ht
    exact
      L.equation_three_four
        t htWorking d.1 hdAmbient hdAnchor

@[simp] theorem claimThreeSixteenBlockData_block
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    (L.claimThreeSixteenBlockData D hall hpositive).block =
      O.chain.blocks L.index :=
  rfl

@[simp] theorem claimThreeSixteenBlockData_left
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    (L.claimThreeSixteenBlockData D hall hpositive).left =
      (O.chain.cuts
        ⟨L.index.1 - 1, by omega⟩).1 :=
  rfl

@[simp] theorem claimThreeSixteenBlockData_right
    (L : P.ExteriorLastFeasibleAnchor M O hregion)
    (D : P.TypeThreeStage)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (hpositive : 0 < L.index.1) :
    (L.claimThreeSixteenBlockData D hall hpositive).right =
      (O.chain.cuts
        ⟨L.index.1, L.index_lt_cutCount⟩).1 :=
  rfl

end ExteriorLastFeasibleAnchor

end PreferredWorkingCoreData

end COY

end DeanK5
