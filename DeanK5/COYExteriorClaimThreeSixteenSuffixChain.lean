import DeanK5.COYExteriorOrderedBlockChain
import DeanK5.Graph.OrderedBlockChainPaths

/-!
# The fixed suffix in COY Claim 3.16

For a selected block strictly before the final exterior block, the ordered
chain supplies a path from its right cut vertex to `y`, supported entirely
on the blocks to its right.  Hence it meets the selected block only at its
initial vertex.  This is exactly the separation needed to append the suffix
to every recursively obtained path inside the selected block.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorOrderedBlockChain

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/-- A block index strictly before the final block also names its right cut. -/
def rightCutIndex
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : p.1 < O.chain.cutCount) :
    Fin O.chain.cutCount :=
  ⟨p.1, hp⟩

/-- Choose the exterior suffix from the selected right cut to `y`. -/
noncomputable def suffixExteriorPath
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : p.1 < O.chain.cutCount) :
    SimplePath P.exteriorGraph
      (O.chain.cuts (O.rightCutIndex p hp)).1
      P.exteriorY := by
  exact Classical.choose
    (O.chain.exists_cut_to_lastBlock_path
      (O.rightCutIndex p hp)
      (by
        simpa [ExteriorOrderedBlockChain.lastIndex] using
          O.y_mem_last_block))

/-- Every suffix vertex lies in the blocks strictly to the right of `p`. -/
theorem suffixExteriorPath_support
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : p.1 < O.chain.cutCount)
    (v : P.ExteriorVertex)
    (hv : v ∈ (O.suffixExteriorPath p hp).walk.support) :
    v ∈ O.chain.intervalCarrier
      (p.1 + 1)
      (O.chain.cutCount - (p.1 + 1)) := by
  have hchosen :=
    Classical.choose_spec
      (O.chain.exists_cut_to_lastBlock_path
        (O.rightCutIndex p hp)
        (by
          simpa [ExteriorOrderedBlockChain.lastIndex] using
            O.y_mem_last_block))
  exact hchosen v
    (by simpa [suffixExteriorPath] using hv)

/-- The selected exterior suffix mapped to the ambient graph. -/
noncomputable def suffixAmbientPath
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : p.1 < O.chain.cutCount) :
    SimplePath G
      (O.chain.cuts (O.rightCutIndex p hp)).1.1 y :=
  (O.suffixExteriorPath p hp).mapInjectiveHom
    P.exteriorEmbedding.toHom Subtype.val_injective

/-- Every ambient suffix vertex belongs to the selected exterior. -/
theorem suffixAmbientPath_support_mem_otherRegion
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : p.1 < O.chain.cutCount)
    {v : V}
    (hv : v ∈ (O.suffixAmbientPath p hp).walk.support) :
    v ∈ P.working.rooted.otherRegion := by
  have hvRange :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := O.suffixExteriorPath p hp)
      (f := P.exteriorEmbedding.toHom)
      (hinj := Subtype.val_injective)
      (by
        unfold suffixAmbientPath at hv
        exact hv)
  obtain ⟨w, rfl⟩ := hvRange
  exact w.2

/--
The exterior suffix meets the selected block only at its right cut vertex.
-/
theorem suffixExteriorPath_meets_selectedBlock_only_at_rightCut
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : p.1 < O.chain.cutCount)
    {v : P.ExteriorVertex}
    (hvSuffix :
      v ∈ (O.suffixExteriorPath p hp).walk.support)
    (hvBlock :
      v ∈ (O.chain.blocks p).carrier) :
    v = (O.chain.cuts (O.rightCutIndex p hp)).1 := by
  let start := p.1 + 1
  let len := O.chain.cutCount - start
  have hstart : 0 < start := by
    dsimp [start]
    omega
  have hbound :
      start + len ≤ O.chain.cutCount := by
    dsimp [start, len]
    omega
  have hvInterval :
      v ∈ O.chain.intervalCarrier start len := by
    simpa [start, len] using
      O.suffixExteriorPath_support p hp v hvSuffix
  have hmeet :=
    O.chain.path_meets_previousBlock_only_at_cut
      P.exteriorGraph_connected
      O.incidence_degree_le_two
      hstart hbound
      (O.suffixExteriorPath p hp)
      (fun w hw =>
        O.suffixExteriorPath_support p hp w hw)
      hvSuffix
      (by
        have hprevious :
            (⟨start - 1, by omega⟩ :
              Fin (O.chain.cutCount + 1)) = p := by
          apply Fin.ext
          dsimp [start]
        simpa [hprevious] using hvBlock)
  have hcutIndex :
      (⟨start - 1, by omega⟩ :
        Fin O.chain.cutCount) =
        O.rightCutIndex p hp := by
    apply Fin.ext
    dsimp [start, rightCutIndex]
  simpa [hcutIndex] using hmeet

/--
Any ambient path supported in the selected exterior block is disjoint from
the suffix after the common right cut.
-/
theorem pathInSelectedBlock_disjoint_suffix_tail
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : p.1 < O.chain.cutCount)
    {a : V}
    (Q : SimplePath G a
      (O.chain.cuts (O.rightCutIndex p hp)).1.1)
    (hQ :
      ∀ v ∈ Q.walk.support,
        ∃ w ∈ (O.chain.blocks p).carrier,
          w.1 = v) :
    Q.walk.support.Disjoint
      (O.suffixAmbientPath p hp).walk.support.tail := by
  apply List.disjoint_left.mpr
  intro v hvQ hvSuffixTail
  obtain ⟨w, hwBlock, hwValue⟩ :=
    hQ v hvQ
  have hvSuffix :
      v ∈ (O.suffixAmbientPath p hp).walk.support :=
    List.mem_of_mem_tail hvSuffixTail
  have hwSuffix :
      w ∈ (O.suffixExteriorPath p hp).walk.support := by
    have hvRange :
        v ∈
          ((O.suffixExteriorPath p hp).walk.map
            P.exteriorEmbedding.toHom).support := by
      unfold suffixAmbientPath at hvSuffix
      exact hvSuffix
    rw [SimpleGraph.Walk.support_map] at hvRange
    obtain ⟨u, hu, huv⟩ :=
      List.mem_map.mp hvRange
    have huw : u = w := by
      apply Subtype.ext
      exact huv.trans hwValue.symm
    simpa [huw] using hu
  have hwRight :
      w =
        (O.chain.cuts
          (O.rightCutIndex p hp)).1 :=
    O.suffixExteriorPath_meets_selectedBlock_only_at_rightCut
      p hp hwSuffix hwBlock
  have hvStart :
      v =
        (O.chain.cuts
          (O.rightCutIndex p hp)).1.1 := by
    exact hwValue.symm.trans
      (congrArg Subtype.val hwRight)
  exact
    (O.suffixAmbientPath p hp).start_not_mem_tail
      (by simpa [hvStart] using hvSuffixTail)

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
