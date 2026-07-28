import DeanK5.Graph.EndBlocks

/-!
# Blocks feasible relative to protected vertices

COY Claim 3.11 singles out two protected vertices, but the underlying
block argument is cleaner for an arbitrary finite protected set.  A block
is feasible when it contains at most two vertices that are either globally
cut or protected, and also contains an ordinary vertex outside that union.

The main result of this file is the local end-block consequence: if one
component behind a deleted vertex avoids every protected vertex, then that
component contains a feasible block.  Consequently, under the assumption
that no feasible block exists, every deletion component meets the protected
set.  This is the precise replacement for the leaf-label bookkeeping in the
informal block-tree argument.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
A graph block is feasible relative to `protected` when at most two of its
vertices are cut or protected, and at least one of its vertices is neither.
-/
def IsFeasibleBlock
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (marked : Finset V)
    (B : GraphBlock G) : Prop :=
  (B.carrier ∩ (cutVertices G ∪ marked)).card ≤ 2 ∧
    (B.carrier \ (cutVertices G ∪ marked)).Nonempty

namespace EndBlock.Certificate

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {initial : LobeRegion G}

/--
An end block selected inside a lobe whose interior avoids the protected set
is feasible.  Its certified interior vertices are not global cut vertices,
so the distinguished lobe cut is the only possible exceptional vertex.
-/
theorem isFeasibleBlock_of_initial_disjoint
    (C : EndBlock.Certificate G initial)
    (marked : Finset V)
    (hdisjoint : Disjoint initial.inner marked) :
    IsFeasibleBlock G marked C.block := by
  have hregionSubset :
      C.region.inner ⊆ initial.inner :=
    C.withinInitial.1
  have hinnerNotProtected :
      ∀ ⦃v : V⦄, v ∈ C.region.inner →
        v ∉ marked := by
    intro v hvInner hvProtected
    exact Finset.disjoint_left.mp hdisjoint
      (hregionSubset hvInner) hvProtected
  have hspecialSubset :
      C.block.carrier ∩
          (cutVertices G ∪ marked) ⊆
        {C.region.cut} := by
    intro v hv
    have hvCarrier : v ∈ C.block.carrier :=
      (Finset.mem_inter.mp hv).1
    have hvSpecial :
        v ∈ cutVertices G ∪ marked :=
      (Finset.mem_inter.mp hv).2
    rw [C.carrier_eq_insert] at hvCarrier
    rcases Finset.mem_insert.mp hvCarrier with
        hvCut | hvInner
    · simp [hvCut]
    · rcases Finset.mem_union.mp hvSpecial with
        hvGlobalCut | hvProtected
      · have hcut : IsCutVertex G v := by
          simpa using hvGlobalCut
        exact False.elim
          (C.inner_not_cut hvInner hcut)
      · exact False.elim
          (hinnerNotProtected hvInner hvProtected)
  constructor
  · calc
      (C.block.carrier ∩
          (cutVertices G ∪ marked)).card
          ≤ ({C.region.cut} : Finset V).card :=
        Finset.card_le_card hspecialSubset
      _ ≤ 2 := by simp
  · obtain ⟨v, hvInner⟩ := C.inner_nonempty
    refine ⟨v, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · rw [C.carrier_eq_insert]
      exact Finset.mem_insert.mpr (Or.inr hvInner)
    · intro hvSpecial
      rcases Finset.mem_union.mp hvSpecial with
          hvGlobalCut | hvProtected
      · have hcut : IsCutVertex G v := by
          simpa using hvGlobalCut
        exact C.inner_not_cut hvInner hcut
      · exact hinnerNotProtected hvInner hvProtected

/--
Under the no-feasible-block hypothesis, every inner vertex of a certified
two-vertex end block must be marked.
-/
theorem inner_mem_marked_of_no_feasibleBlock_of_card_le_two
    (C : EndBlock.Certificate G initial)
    (marked : Finset V)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (hcard : C.block.carrier.card ≤ 2)
    {v : V} (hvInner : v ∈ C.region.inner) :
    v ∈ marked := by
  by_contra hvMarked
  apply hnoFeasible C.block
  constructor
  · exact
      (Finset.card_le_card
        (Finset.inter_subset_left :
          C.block.carrier ∩
              (cutVertices G ∪ marked) ⊆
            C.block.carrier)).trans hcard
  · refine ⟨v, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · rw [C.carrier_eq_insert]
      exact Finset.mem_insert.mpr (Or.inr hvInner)
    · intro hvSpecial
      rcases Finset.mem_union.mp hvSpecial with
          hvCut | hvProtected
      · have hcut : IsCutVertex G v := by
          simpa using hvCut
        exact C.inner_not_cut hvInner hcut
      · exact hvMarked hvProtected

end EndBlock.Certificate

/--
Every deletion component whose original-carrier vertex set avoids the
protected set contains a feasible block.
-/
theorem exists_feasibleBlock_in_deletionComponent
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V) (c : V)
    (Q : (deleteVertices G {c}).ConnectedComponent)
    (hdisjoint :
      Disjoint (componentVertices G {c} Q) marked) :
    ∃ B : GraphBlock G,
      IsFeasibleBlock G marked B := by
  obtain ⟨L, hinner, -⟩ :=
    LobeRegion.exists_ofComponent hconnected c Q
  obtain ⟨C⟩ :=
    EndBlock.exists_certificate hconnected L
  refine ⟨C.block, ?_⟩
  apply C.isFeasibleBlock_of_initial_disjoint
  rw [hinner]
  exact hdisjoint

/--
If no feasible block exists, every component after deleting one vertex
contains at least one protected vertex.
-/
theorem deletionComponent_meets_protected_of_no_feasibleBlock
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    (c : V)
    (Q : (deleteVertices G {c}).ConnectedComponent) :
    ∃ r ∈ marked,
      r ∈ componentVertices G {c} Q := by
  by_contra hnot
  push Not at hnot
  have hdisjoint :
      Disjoint (componentVertices G {c} Q) marked := by
    apply Finset.disjoint_left.mpr
    intro r hrQ hrProtected
    exact hnot r hrProtected hrQ
  obtain ⟨B, hfeasible⟩ :=
    exists_feasibleBlock_in_deletionComponent
      hconnected marked c Q hdisjoint
  exact hnoFeasible B hfeasible

/--
When at most two vertices are marked and no feasible block exists, a marked
vertex cannot be a cut vertex.

Indeed, every deletion component would have to contain a marked vertex.
After deleting the marked cut itself, at most one marked vertex remains, so
two distinct components would contain the same surviving vertex.
-/
theorem not_isCutVertex_of_mem_marked_of_no_feasibleBlock
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (marked : Finset V)
    (hmarked : marked.card ≤ 2)
    (hnoFeasible :
      ∀ B : GraphBlock G,
        ¬IsFeasibleBlock G marked B)
    {c : V} (hcMarked : c ∈ marked) :
    ¬IsCutVertex G c := by
  intro hcut
  have hvertexCut :
      IsVertexCut G {c} :=
    (isCutVertex_iff_isVertexCut
      G c hconnected.preconnected).1 hcut
  obtain ⟨Q, R, hQR⟩ := hvertexCut
  obtain ⟨q, hqMarked, hqQ⟩ :=
    deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible c Q
  obtain ⟨r, hrMarked, hrR⟩ :=
    deletionComponent_meets_protected_of_no_feasibleBlock
      hconnected marked hnoFeasible c R
  have hqNeC : q ≠ c := by
    obtain ⟨hqNot, -⟩ :=
      (mem_componentVertices_iff G {c} Q q).1 hqQ
    simpa using hqNot
  have hrNeC : r ≠ c := by
    obtain ⟨hrNot, -⟩ :=
      (mem_componentVertices_iff G {c} R r).1 hrR
    simpa using hrNot
  have hqErase : q ∈ marked.erase c :=
    Finset.mem_erase.mpr ⟨hqNeC, hqMarked⟩
  have hrErase : r ∈ marked.erase c :=
    Finset.mem_erase.mpr ⟨hrNeC, hrMarked⟩
  have hmarkedErase :
      (marked.erase c).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hcMarked]
    omega
  have hqr : q = r :=
    Finset.card_le_one.mp hmarkedErase
      q hqErase r hrErase
  exact Finset.disjoint_left.mp
    (componentVertices_disjoint_of_ne
      G {c} hQR)
    hqQ (hqr ▸ hrR)

/--
A connected graph of order at least two always has a feasible block
relative to at most one marked vertex.

If a cut vertex existed, two distinct deletion components would both have
to contain the sole possible marked vertex, contradicting their disjointness.
Thus the whole graph has no cut vertex and is itself a block; its order bound
then supplies an unmarked vertex.
-/
theorem exists_feasibleBlock_of_marked_card_le_one
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hconnected : G.Connected)
    (horder : 2 ≤ Fintype.card V)
    (marked : Finset V)
    (hmarked : marked.card ≤ 1) :
    ∃ B : GraphBlock G,
      IsFeasibleBlock G marked B := by
  by_contra hnot
  push Not at hnot
  have hnoCut : HasNoCutVertex G := by
    intro c hcut
    have hvertexCut :
        IsVertexCut G {c} :=
      (isCutVertex_iff_isVertexCut
        G c hconnected.preconnected).1 hcut
    obtain ⟨Q, R, hQR⟩ := hvertexCut
    obtain ⟨q, hqMarked, hqQ⟩ :=
      deletionComponent_meets_protected_of_no_feasibleBlock
        hconnected marked hnot c Q
    obtain ⟨r, hrMarked, hrR⟩ :=
      deletionComponent_meets_protected_of_no_feasibleBlock
        hconnected marked hnot c R
    have hqr : q = r := by
      exact
        Finset.card_le_one.mp hmarked
          q hqMarked r hrMarked
    exact Finset.disjoint_left.mp
      (componentVertices_disjoint_of_ne
        G {c} hQR)
      hqQ (hqr ▸ hrR)
  let B : GraphBlock G :=
    GraphBlock.ofConnectedHasNoCutVertex
      horder hconnected hnoCut
  have hcutVertices :
      cutVertices G = ∅ :=
    (hasNoCutVertex_iff_cutVertices_eq_empty G).1
      hnoCut
  apply hnot B
  constructor
  · simpa [B, IsFeasibleBlock, hcutVertices] using
      hmarked.trans (by omega : 1 ≤ 2)
  · have hmarkedLt :
        marked.card <
          (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]
      omega
    have hdiff :
        ((Finset.univ : Finset V) \ marked).Nonempty :=
      Finset.sdiff_nonempty_of_card_lt_card hmarkedLt
    simpa [B, IsFeasibleBlock, hcutVertices] using
      hdiff

end DeanK5
