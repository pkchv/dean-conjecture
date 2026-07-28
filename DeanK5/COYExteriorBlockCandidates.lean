import DeanK5.COYExteriorOrderedBlockChain

/-!
# The last feasible block of the COY exterior chain

Once the block--cut tree of the selected exterior has been oriented from the
`z`-block to the `y`-block, its blocks form a finite linear order.  This file
packages the elementary bookkeeping used at the end of the COY proof:

* a block of order at least three is feasible;
* after Claim 3.15, feasibility is equivalent to having order at least three;
* hence there is a last feasible block, and every later block is a
  two-vertex block.

The generic chain lemmas take the endpoint membership and non-cut conditions
explicitly.  The exterior-specific wrapper can therefore use any oriented
chain construction without relying on definitional properties of that
construction.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace BlockCutIncidence

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Finiteness of block--cut nodes used in the generic candidate-block arguments. -/
noncomputable local instance exteriorCandidateNodeFintype
    (G : SimpleGraph V) :
    Fintype (BlockCutNode G) :=
  Fintype.ofFinite _

/-- Decidable equality for block--cut nodes in the candidate-block arguments. -/
noncomputable local instance exteriorCandidateNodeDecidableEq
    (G : SimpleGraph V) :
    DecidableEq (BlockCutNode G) :=
  Classical.decEq _

/-- Decidable incidence adjacency used in the generic candidate-block arguments. -/
noncomputable local instance exteriorCandidateAdjDecidable
    (G : SimpleGraph V) :
    DecidableRel (blockCutIncidence G).Adj :=
  Classical.decRel _

/--
The cut vertices contained in a block inject into the cut-node neighbors of
that block in the block--cut incidence graph.
-/
theorem block_cutVertices_card_le_degree
    (B : GraphBlock G) :
    (B.carrier ∩ cutVertices G).card ≤
      (blockCutIncidence G).degree
        (.inl B : BlockCutNode G) := by
  classical
  let f :
      ↑(B.carrier ∩ cutVertices G) →
        ↑((blockCutIncidence G).neighborFinset
          (.inl B : BlockCutNode G)) :=
    fun c =>
      ⟨.inr
          ⟨c.1, by
            simpa using
              (Finset.mem_inter.mp c.2).2⟩,
        by
          simp
          exact (Finset.mem_inter.mp c.2).1⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    have hnodes :
        (Sum.inr
            ⟨c.1, by
              simpa using
                (Finset.mem_inter.mp c.2).2⟩ :
              BlockCutNode G) =
          .inr
            ⟨d.1, by
              simpa using
                (Finset.mem_inter.mp d.2).2⟩ :=
      congrArg Subtype.val hcd
    have hvalues :=
      congrArg
        (fun n : BlockCutNode G =>
          match n with
          | .inl _ => none
          | .inr e => some e.1)
        hnodes
    simpa using hvalues
  rw [SimpleGraph.degree]
  simpa only [Fintype.card_coe] using
    (Fintype.card_le_of_injective f hf)

namespace OrderedBlockChain

/--
A non-cut vertex in one chain block cannot occur in any other chain block.
-/
theorem block_index_eq_of_noncut_mem
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    {v : V} (hvNotCut : ¬IsCutVertex G v)
    (i j : Fin (chain.cutCount + 1))
    (hvi : v ∈ (chain.blocks i).carrier)
    (hvj : v ∈ (chain.blocks j).carrier) :
    i = j := by
  by_contra hij
  apply hvNotCut
  exact
    GraphBlock.isCutVertex_of_mem_inter
      hconnected
      (chain.blocks i) (chain.blocks j)
      (fun hblocks => hij (chain.blocks_injective hblocks))
      hvi hvj

/--
An internal chain block contains neither of the two non-cut endpoint
vertices.
-/
theorem marked_inter_eq_empty_of_internal
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    {a b : V}
    (haNotCut : ¬IsCutVertex G a)
    (hbNotCut : ¬IsCutVertex G b)
    (haFirst :
      a ∈ (chain.blocks 0).carrier)
    (hbLast :
      b ∈
        (chain.blocks
          (Fin.last chain.cutCount)).carrier)
    (i : Fin (chain.cutCount + 1))
    (hiPositive : 0 < i.1)
    (hiBeforeLast : i.1 < chain.cutCount) :
    (chain.blocks i).carrier ∩ {a, b} = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hvCarrier :=
    (Finset.mem_inter.mp hv).1
  have hvMarked :=
    (Finset.mem_inter.mp hv).2
  simp only [Finset.mem_insert,
    Finset.mem_singleton] at hvMarked
  rcases hvMarked with rfl | rfl
  · have hiZero :
        i = (0 : Fin (chain.cutCount + 1)) :=
      chain.block_index_eq_of_noncut_mem
        hconnected haNotCut i 0 hvCarrier haFirst
    have := congrArg
      (fun k : Fin (chain.cutCount + 1) => k.1) hiZero
    change i.1 = 0 at this
    omega
  · have hiLast :
        i = Fin.last chain.cutCount :=
      chain.block_index_eq_of_noncut_mem
        hconnected hbNotCut i
        (Fin.last chain.cutCount) hvCarrier hbLast
    have := congrArg
      (fun k : Fin (chain.cutCount + 1) => k.1) hiLast
    simp at this
    omega

/--
At the first chain block, only the first endpoint can occur among the two
non-cut marked vertices.
-/
theorem first_marked_inter_subset
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    {a b : V}
    (hbNotCut : ¬IsCutVertex G b)
    (hbLast :
      b ∈
        (chain.blocks
          (Fin.last chain.cutCount)).carrier) :
    (chain.blocks 0).carrier ∩ {a, b} ⊆ {a} := by
  classical
  intro v hv
  have hvCarrier :=
    (Finset.mem_inter.mp hv).1
  have hvMarked :=
    (Finset.mem_inter.mp hv).2
  simp only [Finset.mem_insert,
    Finset.mem_singleton] at hvMarked
  rcases hvMarked with rfl | rfl
  · simp
  · have hzeroLast :
        (0 : Fin (chain.cutCount + 1)) =
          Fin.last chain.cutCount :=
      chain.block_index_eq_of_noncut_mem
        hconnected hbNotCut 0
        (Fin.last chain.cutCount)
        hvCarrier hbLast
    have hvalues :=
      congrArg
        (fun k : Fin (chain.cutCount + 1) => k.1)
        hzeroLast
    change 0 = chain.cutCount at hvalues
    have hpositive := chain.one_le_cutCount
    omega

/--
At the last chain block, only the last endpoint can occur among the two
non-cut marked vertices.
-/
theorem last_marked_inter_subset
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    {a b : V}
    (haNotCut : ¬IsCutVertex G a)
    (haFirst :
      a ∈ (chain.blocks 0).carrier) :
    (chain.blocks (Fin.last chain.cutCount)).carrier ∩
        {a, b} ⊆ {b} := by
  classical
  intro v hv
  have hvCarrier :=
    (Finset.mem_inter.mp hv).1
  have hvMarked :=
    (Finset.mem_inter.mp hv).2
  simp only [Finset.mem_insert,
    Finset.mem_singleton] at hvMarked
  rcases hvMarked with rfl | rfl
  · have hlastZero :
        Fin.last chain.cutCount =
          (0 : Fin (chain.cutCount + 1)) :=
      chain.block_index_eq_of_noncut_mem
        hconnected haNotCut
        (Fin.last chain.cutCount) 0
        hvCarrier haFirst
    have hvalues :=
      congrArg
        (fun k : Fin (chain.cutCount + 1) => k.1)
        hlastZero
    change chain.cutCount = 0 at hvalues
    have hpositive := chain.one_le_cutCount
    omega
  · simp

/--
Every block of order at least three in a chain with two non-cut marked
endpoints is feasible relative to those endpoints.
-/
theorem isFeasibleBlock_of_three_le_card
    (hconnected : G.Connected)
    (chain : OrderedBlockChain G)
    (hdegree :
      ∀ n : BlockCutNode G,
        (blockCutIncidence G).degree n ≤ 2)
    {a b : V}
    (haNotCut : ¬IsCutVertex G a)
    (hbNotCut : ¬IsCutVertex G b)
    (haFirst :
      a ∈ (chain.blocks 0).carrier)
    (hbLast :
      b ∈
        (chain.blocks
          (Fin.last chain.cutCount)).carrier)
    (hfirstDegree :
      (blockCutIncidence G).degree
        (.inl (chain.blocks 0) : BlockCutNode G) = 1)
    (hlastDegree :
      (blockCutIncidence G).degree
        (.inl
          (chain.blocks
            (Fin.last chain.cutCount)) :
          BlockCutNode G) = 1)
    (i : Fin (chain.cutCount + 1))
    (hlarge : 3 ≤ (chain.blocks i).carrier.card) :
    IsFeasibleBlock G {a, b} (chain.blocks i) := by
  classical
  let B := chain.blocks i
  have hcutCard :
      (B.carrier ∩ cutVertices G).card ≤
        (blockCutIncidence G).degree
          (.inl B : BlockCutNode G) :=
    block_cutVertices_card_le_degree B
  have hspecialRewrite :
      B.carrier ∩ (cutVertices G ∪ {a, b}) =
        (B.carrier ∩ cutVertices G) ∪
          (B.carrier ∩ {a, b}) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hspecialCard :
      (B.carrier ∩ (cutVertices G ∪ {a, b})).card ≤ 2 := by
    rw [hspecialRewrite]
    calc
      ((B.carrier ∩ cutVertices G) ∪
          (B.carrier ∩ {a, b})).card
          ≤ (B.carrier ∩ cutVertices G).card +
              (B.carrier ∩ {a, b}).card :=
        Finset.card_union_le _ _
      _ ≤ 2 := by
        by_cases hiZero : i.1 = 0
        · have hi : i = 0 := Fin.ext hiZero
          subst i
          have hmarkedCard :
              ((chain.blocks 0).carrier ∩
                {a, b}).card ≤ 1 := by
            calc
              ((chain.blocks 0).carrier ∩
                  {a, b}).card ≤ ({a} : Finset V).card :=
                Finset.card_le_card
                  (chain.first_marked_inter_subset
                    hconnected hbNotCut hbLast)
              _ = 1 := by simp
          dsimp [B] at hcutCard ⊢
          rw [hfirstDegree] at hcutCard
          omega
        · by_cases hiLast :
            i.1 = chain.cutCount
          · have hi :
                i = Fin.last chain.cutCount :=
              Fin.ext (by simpa using hiLast)
            subst i
            have hmarkedCard :
                ((chain.blocks
                    (Fin.last chain.cutCount)).carrier ∩
                  {a, b}).card ≤ 1 := by
              calc
                ((chain.blocks
                    (Fin.last chain.cutCount)).carrier ∩
                    {a, b}).card ≤ ({b} : Finset V).card :=
                  Finset.card_le_card
                    (chain.last_marked_inter_subset
                      hconnected haNotCut haFirst)
                _ = 1 := by simp
            dsimp [B] at hcutCard ⊢
            rw [hlastDegree] at hcutCard
            omega
          · have hiPositive : 0 < i.1 := by omega
            have hiBeforeLast :
                i.1 < chain.cutCount := by
              have hiUpper : i.1 < chain.cutCount + 1 :=
                i.2
              omega
            have hmarkedEmpty :
                (chain.blocks i).carrier ∩ {a, b} = ∅ :=
              chain.marked_inter_eq_empty_of_internal
                hconnected haNotCut hbNotCut
                haFirst hbLast i hiPositive hiBeforeLast
            dsimp [B] at hcutCard ⊢
            rw [hmarkedEmpty]
            simp only [Finset.card_empty, Nat.add_zero]
            exact hcutCard.trans
              (hdegree
                (.inl (chain.blocks i) :
                  BlockCutNode G))
  constructor
  · exact hspecialCard
  · apply Finset.sdiff_nonempty.mpr
    intro hsubset
    have hinterEq :
        B.carrier ∩ (cutVertices G ∪ {a, b}) =
          B.carrier :=
      Finset.inter_eq_left.mpr hsubset
    have hcarrierCard :
        B.carrier.card ≤ 2 := by
      rw [← hinterEq]
      exact hspecialCard
    dsimp [B] at hcarrierCard
    omega

end OrderedBlockChain

end BlockCutIncidence

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- Finiteness of the selected exterior's block--cut nodes. -/
noncomputable local instance exteriorCandidateCOYNodeFintype
    (P : PreferredWorkingCoreData G x y z) :
    Fintype (BlockCutNode P.exteriorGraph) :=
  Fintype.ofFinite _

/-- Decidable adjacency in the selected exterior's block--cut incidence graph. -/
noncomputable local instance exteriorCandidateCOYAdjDecidable
    (P : PreferredWorkingCoreData G x y z) :
    DecidableRel (blockCutIncidence P.exteriorGraph).Adj :=
  Classical.decRel _

namespace ExteriorFeasibleBlockChoice

variable {P : PreferredWorkingCoreData G x y z}

/--
Claim 3.15(1) exhibits, besides the anchor and the ordinary vertex, a third
distinct vertex of every feasible block.
-/
theorem three_le_carrier_card_of_meetsProtectedInterior
    (C : P.ExteriorFeasibleBlockChoice)
    (hmeets : C.MeetsProtectedInterior) :
    3 ≤ C.block.carrier.card := by
  have hthreeAmbient :
      3 ≤ C.ambientCarrier.card := by
    rcases hmeets with hy | hzPrime
    · have hyNeB : y ≠ C.b :=
        (Finset.mem_erase.mp hy).1
      have hordinaryNeY : C.ordinary ≠ y :=
        C.ordinary_block_vertex_ne_y
          C.ordinary_mem_ambientCarrier
          C.ordinary_ne_b C.ordinary_ne_zPrime
      have hcard :
          ({C.ordinary, C.b, y} : Finset V).card = 3 := by
        simp [C.ordinary_ne_b, hordinaryNeY, hyNeB.symm]
      rw [← hcard]
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact C.ordinary_mem_ambientCarrier
      · exact C.b_mem_ambientCarrier
      · exact Finset.mem_of_mem_erase hy
    · have hzNeB : C.zPrime ≠ C.b :=
        (Finset.mem_erase.mp hzPrime).1
      have hcard :
          ({C.ordinary, C.b, C.zPrime} :
            Finset V).card = 3 := by
        simp [C.ordinary_ne_b, C.ordinary_ne_zPrime,
          hzNeB.symm]
      rw [← hcard]
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact C.ordinary_mem_ambientCarrier
      · exact C.b_mem_ambientCarrier
      · exact C.zPrime_mem_ambientCarrier
  rw [ExteriorFeasibleBlockChoice.ambientCarrier,
    Finset.card_image_of_injective
      C.block.carrier P.exteriorEmbedding.injective] at hthreeAmbient
  exact hthreeAmbient

end ExteriorFeasibleBlockChoice

/--
The explicit hypotheses required of an oriented exterior chain before the
last-feasible-block bookkeeping can be applied.
-/
structure ExteriorCandidateChain
    (P : PreferredWorkingCoreData G x y z)
    (hz : z ∈ P.working.rooted.otherRegion) where
  /-- The block chain, oriented from `z` to `y`. -/
  chain :
    BlockCutIncidence.OrderedBlockChain P.exteriorGraph
  /-- The exterior copy of `z` belongs to the first block. -/
  z_mem_first :
    P.exteriorZ hz ∈ (chain.blocks 0).carrier
  /-- The exterior copy of `y` belongs to the last block. -/
  y_mem_last :
    P.exteriorY ∈
      (chain.blocks (Fin.last chain.cutCount)).carrier
  /-- The exterior copy of `z` is not a cut vertex. -/
  z_not_cut :
    ¬IsCutVertex P.exteriorGraph (P.exteriorZ hz)
  /-- The exterior copy of `y` is not a cut vertex. -/
  y_not_cut :
    ¬IsCutVertex P.exteriorGraph P.exteriorY
  /-- Every block--cut node has degree at most two. -/
  degree_le_two :
    ∀ n : BlockCutNode P.exteriorGraph,
      (blockCutIncidence P.exteriorGraph).degree n ≤ 2
  /-- The first block is an incidence leaf. -/
  first_degree_eq_one :
    (blockCutIncidence P.exteriorGraph).degree
      (.inl (chain.blocks 0) :
        BlockCutNode P.exteriorGraph) = 1
  /-- The last block is an incidence leaf. -/
  last_degree_eq_one :
    (blockCutIncidence P.exteriorGraph).degree
      (.inl
        (chain.blocks (Fin.last chain.cutCount)) :
        BlockCutNode P.exteriorGraph) = 1

namespace ExteriorCandidateChain

variable {P : PreferredWorkingCoreData G x y z}
  {hz : z ∈ P.working.rooted.otherRegion}

/-- A large block of an oriented exterior chain is feasible. -/
theorem feasible_of_three_le_card
    (K : P.ExteriorCandidateChain hz)
    (i : Fin (K.chain.cutCount + 1))
    (hlarge : 3 ≤ (K.chain.blocks i).carrier.card) :
    IsFeasibleBlock P.exteriorGraph
      P.exteriorProtected (K.chain.blocks i) := by
  have hprotected :
      P.exteriorProtected =
        {P.exteriorZ hz, P.exteriorY} := by
    rw [P.exteriorProtected_eq_pair hz]
    exact Finset.pair_comm _ _
  rw [hprotected]
  exact
    K.chain.isFeasibleBlock_of_three_le_card
      P.exteriorGraph_connected K.degree_le_two
      K.z_not_cut K.y_not_cut
      K.z_mem_first K.y_mem_last
      K.first_degree_eq_one K.last_degree_eq_one
      i hlarge

/--
Under the uniform conclusion of Claim 3.15, a chain block is feasible if
and only if it has at least three vertices.
-/
theorem feasible_iff_three_le_card
    (K : P.ExteriorCandidateChain hz)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (i : Fin (K.chain.cutCount + 1)) :
    IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected (K.chain.blocks i) ↔
      3 ≤ (K.chain.blocks i).carrier.card := by
  constructor
  · intro hfeasible
    obtain ⟨anchor⟩ :=
      (K.chain.blocks i).exists_feasibleBlockAnchor
        P.exteriorGraph_connected
        P.exteriorProtected P.exteriorY
        P.exteriorY_mem_exteriorProtected hfeasible
    let C : P.ExteriorFeasibleBlockChoice := {
      block := K.chain.blocks i
      feasible := hfeasible
      anchor := anchor
    }
    exact C.three_le_carrier_card_of_meetsProtectedInterior
      (hall C)
  · exact K.feasible_of_three_le_card i

/-- The feasible/large block indices of an oriented chain. -/
noncomputable def feasibleIndices
    (K : P.ExteriorCandidateChain hz) :
    Finset (Fin (K.chain.cutCount + 1)) := by
  classical
  exact Finset.univ.filter fun i =>
      IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected (K.chain.blocks i)

@[simp] theorem mem_feasibleIndices
    (K : P.ExteriorCandidateChain hz)
    (i : Fin (K.chain.cutCount + 1)) :
    i ∈ K.feasibleIndices ↔
      IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected (K.chain.blocks i) := by
  classical
  simp [feasibleIndices]

/-- Claim 3.11 ensures that the chain has a feasible index. -/
theorem feasibleIndices_nonempty
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (K : P.ExteriorCandidateChain hz) :
    K.feasibleIndices.Nonempty := by
  classical
  obtain ⟨C⟩ :=
    P.exists_exteriorFeasibleBlockChoice M hregion
  obtain ⟨i, hi⟩ :=
    K.chain.blocks_exhaustive C.block
  refine ⟨i, (mem_feasibleIndices K i).2 ?_⟩
  simpa [hi] using C.feasible

/--
There is an index whose block is simultaneously feasible and has at least
three vertices.
-/
theorem exists_feasible_index_with_three_le_card
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (K : P.ExteriorCandidateChain hz) :
    ∃ i : Fin (K.chain.cutCount + 1),
      IsFeasibleBlock P.exteriorGraph
          P.exteriorProtected (K.chain.blocks i) ∧
        3 ≤ (K.chain.blocks i).carrier.card := by
  obtain ⟨i, hi⟩ :=
    K.feasibleIndices_nonempty M hregion
  have hfeasible :=
    (mem_feasibleIndices K i).1 hi
  exact
    ⟨i, hfeasible,
      (K.feasible_iff_three_le_card hall i).1
        hfeasible⟩

/--
After Claim 3.15, every non-feasible chain block is a two-vertex block.
-/
theorem card_eq_two_of_not_feasible
    (K : P.ExteriorCandidateChain hz)
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (i : Fin (K.chain.cutCount + 1))
    (hnot :
      ¬IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected (K.chain.blocks i)) :
    (K.chain.blocks i).carrier.card = 2 := by
  have hnotLarge :
      ¬3 ≤ (K.chain.blocks i).carrier.card :=
    (K.feasible_iff_three_le_card hall i).not.mp hnot
  exact Nat.le_antisymm (by omega)
    (K.chain.blocks i).card_ge_two

/-- The last feasible block index in the oriented exterior chain. -/
noncomputable def lastFeasibleIndex
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (K : P.ExteriorCandidateChain hz) :
    Fin (K.chain.cutCount + 1) :=
  K.feasibleIndices.max'
    (K.feasibleIndices_nonempty M hregion)

/-- The selected last index is feasible. -/
theorem lastFeasibleIndex_mem
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (K : P.ExteriorCandidateChain hz) :
    K.lastFeasibleIndex M hregion ∈
      K.feasibleIndices := by
  classical
  exact
    Finset.max'_mem K.feasibleIndices
      (K.feasibleIndices_nonempty M hregion)

/-- The block selected by `lastFeasibleIndex` is feasible. -/
theorem lastFeasibleIndex_feasible
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (K : P.ExteriorCandidateChain hz) :
    IsFeasibleBlock P.exteriorGraph
      P.exteriorProtected
      (K.chain.blocks
        (K.lastFeasibleIndex M hregion)) :=
  (mem_feasibleIndices K
    (K.lastFeasibleIndex M hregion)).1
      (K.lastFeasibleIndex_mem M hregion)

/--
Under Claim 3.15, the selected last feasible block has at least three
vertices.
-/
theorem three_le_lastFeasibleIndex_card
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (K : P.ExteriorCandidateChain hz) :
    3 ≤
      (K.chain.blocks
        (K.lastFeasibleIndex M hregion)).carrier.card :=
  (K.feasible_iff_three_le_card hall
    (K.lastFeasibleIndex M hregion)).1
      (K.lastFeasibleIndex_feasible M hregion)

/-- Every feasible index is at most the selected last feasible index. -/
theorem le_lastFeasibleIndex
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (K : P.ExteriorCandidateChain hz)
    {i : Fin (K.chain.cutCount + 1)}
    (hi : i ∈ K.feasibleIndices) :
    i ≤ K.lastFeasibleIndex M hregion := by
  classical
  exact
    Finset.le_max'
      K.feasibleIndices i hi

/--
Every block strictly after the last feasible block has exactly two
vertices.
-/
theorem later_block_card_eq_two
    (M : MinimalCounterexample q G x y z)
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (hall : P.AllFeasibleBlocksMeetProtectedInterior)
    (K : P.ExteriorCandidateChain hz)
    (i : Fin (K.chain.cutCount + 1))
    (hlater :
      K.lastFeasibleIndex M hregion < i) :
    (K.chain.blocks i).carrier.card = 2 := by
  have hnotFeasible :
      ¬IsFeasibleBlock P.exteriorGraph
        P.exteriorProtected (K.chain.blocks i) := by
    intro hfeasible
    have hiMem :
        i ∈ K.feasibleIndices :=
      (mem_feasibleIndices K i).2 hfeasible
    have hle :=
      K.le_lastFeasibleIndex M hregion hiMem
    exact (not_le_of_gt hlater) hle
  exact K.card_eq_two_of_not_feasible hall i hnotFeasible

end ExteriorCandidateChain

namespace ExteriorOrderedBlockChain

variable {P : PreferredWorkingCoreData G x y z}

/--
Forget an exterior ordered chain down to exactly the endpoint and incidence
data needed by the last-feasible-block argument.
-/
def toCandidateChain
    (O : P.ExteriorOrderedBlockChain) :
    P.ExteriorCandidateChain
      O.endpoints.z_mem_otherRegion where
  chain := O.chain
  z_mem_first := by
    simpa [ExteriorOrderedBlockChain.firstIndex] using
      O.z_mem_first_block
  y_mem_last := by
    have hlast :
        Fin.last O.chain.cutCount = O.lastIndex :=
      Fin.ext rfl
    rw [hlast]
    exact O.y_mem_last_block
  z_not_cut := O.z_not_cut
  y_not_cut := O.y_not_cut
  degree_le_two := O.incidence_degree_le_two
  first_degree_eq_one := by
    have hfirst :
        (0 : Fin (O.chain.cutCount + 1)) =
          O.firstIndex :=
      Fin.ext rfl
    rw [hfirst]
    change
      (blockCutIncidence P.exteriorGraph).degree
        (.inl
          (O.chain.blocks
            ⟨0, Nat.zero_lt_succ O.chain.cutCount⟩) :
          BlockCutNode P.exteriorGraph) = 1
    rw [O.first_block_eq_z]
    exact O.endpoints.zBlock_degree_eq_one
  last_degree_eq_one := by
    have hlast :
        Fin.last O.chain.cutCount = O.lastIndex :=
      Fin.ext rfl
    rw [hlast]
    change
      (blockCutIncidence P.exteriorGraph).degree
        (.inl
          (O.chain.blocks
            ⟨O.chain.cutCount,
              Nat.lt_succ_self O.chain.cutCount⟩) :
          BlockCutNode P.exteriorGraph) = 1
    rw [O.last_block_eq_y]
    exact O.endpoints.yBlock_degree_eq_one

end ExteriorOrderedBlockChain

end PreferredWorkingCoreData

end COY

end DeanK5
