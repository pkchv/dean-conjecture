import DeanK5.COYExteriorOrderedBlockChain
import DeanK5.COYExteriorClaimThreeSixteenPrefix
import DeanK5.Graph.OrderedBlockChainPaths

/-!
# Building the Claim 3.16 prefix from the exterior block chain

If a terminal-side core vertex is adjacent to an exterior vertex in a
block strictly before the selected block, the ordered block chain gives a
path from that attachment to the selected block's left cut vertex.  After
prepending the attachment edge, the connector leaves the core immediately
and never returns.  Fact 2(2) can therefore append it to its two
semi-admissible core paths.
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

/-- The cut immediately to the left of a positive block index. -/
def leftCutIndex
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1) :
    Fin O.chain.cutCount :=
  ⟨p.1 - 1, by
    have hpBound := p.2
    omega⟩

/--
Choose an exterior path from an earlier attachment block to the cut
immediately left of block `p`.
-/
noncomputable def prefixExteriorPath
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier) :
    SimplePath P.exteriorGraph a
      (O.chain.cuts (O.leftCutIndex p hp)).1 := by
  let j := O.leftCutIndex p hp
  have hij : i.1 ≤ j.1 := by
    dsimp [j, leftCutIndex]
    omega
  exact Classical.choose
    (O.chain.exists_prefix_path_to_cut i j hij ha)

/-- Every vertex of the chosen prefix path lies in the preceding blocks. -/
theorem prefixExteriorPath_support
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    (v : P.ExteriorVertex)
    (hv : v ∈
      (O.prefixExteriorPath p hp i hip a ha).walk.support) :
    v ∈ O.chain.intervalCarrier 0 (p.1 - 1) := by
  let j := O.leftCutIndex p hp
  have hij : i.1 ≤ j.1 := by
    dsimp [j, leftCutIndex]
    omega
  have hchosen :=
    Classical.choose_spec
      (O.chain.exists_prefix_path_to_cut i j hij ha)
  exact
    hchosen v (by
      simpa [prefixExteriorPath, j] using hv)

/-- The chosen exterior prefix path mapped back to the ambient graph. -/
noncomputable def prefixAmbientPath
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier) :
    SimplePath G a.1
      (O.chain.cuts (O.leftCutIndex p hp)).1.1 :=
  (O.prefixExteriorPath p hp i hip a ha).mapInjectiveHom
    P.exteriorEmbedding.toHom Subtype.val_injective

/-- Every mapped prefix-path vertex belongs to the selected exterior. -/
theorem prefixAmbientPath_support_mem_otherRegion
    (O : P.ExteriorOrderedBlockChain)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {v : V}
    (hv : v ∈
      (O.prefixAmbientPath p hp i hip a ha).walk.support) :
    v ∈ P.working.rooted.otherRegion := by
  have hvRange :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := O.prefixExteriorPath p hp i hip a ha)
      (f := P.exteriorEmbedding.toHom)
      (hinj := Subtype.val_injective)
      (by
        unfold prefixAmbientPath at hv
        exact hv)
  obtain ⟨w, rfl⟩ := hvRange
  exact w.2

/--
The attachment edge and the remainder of the exterior prefix path have
disjoint supports.
-/
theorem attachmentEdge_disjoint_prefixAmbientPath_tail
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    (SimplePath.ofAdj hta).walk.support.Disjoint
      (O.prefixAmbientPath p hp i hip a ha).walk.support.tail := by
  apply List.disjoint_left.mpr
  intro v hvEdge hvTail
  simp at hvEdge
  rcases hvEdge with hvTarget | hvA
  · have hvRegion :
        v ∈ P.working.rooted.otherRegion :=
      O.prefixAmbientPath_support_mem_otherRegion
        p hp i hip a ha
        (List.mem_of_mem_tail hvTail)
    have hvCore :
        v ∈ P.working.rooted.core.carrier := by
      rw [hvTarget]
      rw [D.core_eq]
      exact
        (Core.typeThree D.core).T_subset_carrier
          (by simpa [Core.T] using htarget)
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        hvRegion hvCore
  · exact
      (O.prefixAmbientPath p hp i hip a ha).start_not_mem_tail
        (by simpa [hvA] using hvTail)

/-- The fixed connector from a terminal core vertex to the selected left cut. -/
noncomputable def claimThreeSixteenPrefixConnector
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    SimplePath G target
      (O.chain.cuts (O.leftCutIndex p hp)).1.1 :=
  (SimplePath.ofAdj hta).appendDisjoint
    (O.prefixAmbientPath p hp i hip a ha)
    (O.attachmentEdge_disjoint_prefixAmbientPath_tail
      D p hp i hip a ha htarget hta)

/-- The Claim 3.16 prefix connector is nontrivial. -/
theorem one_le_claimThreeSixteenPrefixConnector_length
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    1 ≤
      (O.claimThreeSixteenPrefixConnector
        D p hp i hip a ha htarget hta).length := by
  rw [claimThreeSixteenPrefixConnector,
    SimplePath.appendDisjoint_length]
  simp

/--
After its initial core vertex, the Claim 3.16 connector stays outside the
selected core.
-/
theorem claimThreeSixteenPrefixConnector_tail_outside
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1)
    {v : V}
    (hv : v ∈
      (O.claimThreeSixteenPrefixConnector
        D p hp i hip a ha htarget hta).walk.support.tail) :
    v ∉ insert x (D.core.S ∪ D.core.T) := by
  intro hvCore
  have hvParts :
      v ∈ (SimplePath.ofAdj hta).walk.support.tail ∨
        v ∈
          (O.prefixAmbientPath
            p hp i hip a ha).walk.support.tail := by
    exact
      (SimpleGraph.Walk.mem_tail_support_append_iff
        (SimplePath.ofAdj hta).walk
        (O.prefixAmbientPath p hp i hip a ha).walk).1
        (by
          simpa [claimThreeSixteenPrefixConnector,
            SimplePath.appendDisjoint] using hv)
  have hvRegion :
      v ∈ P.working.rooted.otherRegion := by
    rcases hvParts with hvEdge | hvPath
    · have hva : v = a.1 := by
        simpa using hvEdge
      exact hva ▸ a.2
    · exact
        O.prefixAmbientPath_support_mem_otherRegion
          p hp i hip a ha
          (List.mem_of_mem_tail hvPath)
  have hvCarrier :
      v ∈ P.working.rooted.core.carrier := by
    rw [D.core_eq]
    simpa [Core.carrier, Core.S, Core.T] using hvCore
  exact
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      hvRegion hvCarrier

/--
An earlier `T`-attachment produces the two admissible prefix paths in
Claim 3.16.
-/
noncomputable def claimThreeSixteenPrefixFamilyFromEarlierAttachment
    (M : MinimalCounterexample q G x y z)
    (O : P.ExteriorOrderedBlockChain)
    (D : P.TypeThreeStage)
    (p : Fin (O.chain.cutCount + 1))
    (hp : 0 < p.1)
    (i : Fin (O.chain.cutCount + 1))
    (hip : i.1 < p.1)
    (a : P.ExteriorVertex)
    (ha : a ∈ (O.chain.blocks i).carrier)
    {target : V}
    (htarget : target ∈ D.core.T)
    (hta : G.Adj target a.1) :
    AdmissiblePathFamily G x
      (O.chain.cuts (O.leftCutIndex p hp)).1.1 2 := by
  let connector :=
    O.claimThreeSixteenPrefixConnector
      D p hp i hip a ha htarget hta
  apply
    D.core.claimThreeSixteenPrefixFamilyOfTailOutside
      htarget connector
      (O.one_le_claimThreeSixteenPrefixConnector_length
        D p hp i hip a ha htarget hta)
      (by
        have hrank := D.rank_eq_one M
        omega)
  intro v hv
  exact
    O.claimThreeSixteenPrefixConnector_tail_outside
      D p hp i hip a ha htarget hta hv

end PreferredWorkingCoreData.ExteriorOrderedBlockChain

end COY

end DeanK5
