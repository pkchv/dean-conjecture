import DeanK5.Graph.BlockCutIncidence
import DeanK5.Graph.FeasibleBlockAnchor
import DeanK5.Graph.TreePath

/-!
# Leaves of the block--cut incidence graph

Cut-vertex nodes of the block--cut incidence graph have degree at least
two.  Consequently every leaf is a block node.  This file also packages
the marked-leaf argument used after COY Claim 3.15: if the local anchored
block conclusion holds, every leaf block contains a marked vertex which is
not a cut vertex.  Distinct leaf blocks receive distinct such vertices.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace BlockCutIncidence

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Finiteness of block--cut nodes used in the leaf arguments. -/
noncomputable local instance blockCutNodeFintype
    (G : SimpleGraph V) :
    Fintype (BlockCutNode G) :=
  Fintype.ofFinite _

/-- Decidable incidence adjacency used in the leaf arguments. -/
noncomputable local instance blockCutAdjDecidable
    (G : SimpleGraph V) :
    DecidableRel (blockCutIncidence G).Adj :=
  Classical.decRel _

/-- A cut node is incident with at least two distinct block nodes. -/
theorem two_le_degree_cut
    (hconnected : G.Connected)
    (c : {c : V // IsCutVertex G c}) :
    2 ≤ (blockCutIncidence G).degree (.inr c) := by
  classical
  obtain ⟨B, C, hBC, hcB, hcC⟩ :=
    GraphBlock.exists_two_distinct_of_isCutVertex
      hconnected c.2
  have hpair :
      ({(.inl B : BlockCutNode G), .inl C} :
          Finset (BlockCutNode G)) ⊆
        (blockCutIncidence G).neighborFinset (.inr c) := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · simpa using hcB
    · simpa using hcC
  rw [SimpleGraph.degree]
  calc
    2 =
        ({(.inl B : BlockCutNode G), .inl C} :
          Finset (BlockCutNode G)).card := by
      symm
      simp [hBC]
    _ ≤
        ((blockCutIncidence G).neighborFinset
          (.inr c)).card :=
      Finset.card_le_card hpair

/-- Every degree-one incidence node is a block node. -/
theorem exists_block_of_degree_eq_one
    (hconnected : G.Connected)
    {n : BlockCutNode G}
    (hdegree : (blockCutIncidence G).degree n = 1) :
    ∃ B : GraphBlock G, n = .inl B := by
  cases n with
  | inl B =>
      exact ⟨B, rfl⟩
  | inr c =>
      exfalso
      have := two_le_degree_cut hconnected c
      omega

/--
All cut vertices in a leaf block coincide.  This is the carrier form of
the fact that a leaf block has a unique incident cut node.
-/
theorem cut_eq_of_mem_leaf_block
    (B : GraphBlock G)
    (hdegree :
      (blockCutIncidence G).degree
        (.inl B : BlockCutNode G) = 1)
    {c d : V}
    (hcB : c ∈ B.carrier)
    (hdB : d ∈ B.carrier)
    (hcCut : IsCutVertex G c)
    (hdCut : IsCutVertex G d) :
    c = d := by
  classical
  let cNode : {c : V // IsCutVertex G c} := ⟨c, hcCut⟩
  let dNode : {c : V // IsCutVertex G c} := ⟨d, hdCut⟩
  have hcAdj :
      (blockCutIncidence G).Adj
        (.inl B) (.inr cNode) :=
    hcB
  have hdAdj :
      (blockCutIncidence G).Adj
        (.inl B) (.inr dNode) :=
    hdB
  obtain ⟨only, hOnlyAdj, hOnly⟩ :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
      hdegree)
  have hcOnly :
      (.inr cNode : BlockCutNode G) = only :=
    hOnly _ hcAdj
  have hdOnly :
      (.inr dNode : BlockCutNode G) = only :=
    hOnly _ hdAdj
  have hnodes :
      (.inr cNode : BlockCutNode G) = .inr dNode :=
    hcOnly.trans hdOnly.symm
  exact congrArg (fun e =>
    match e with
    | Sum.inl _ => c
    | Sum.inr v => v.1) hnodes

/-- A leaf block contains at least one ambient cut vertex. -/
theorem exists_cut_mem_of_block_degree_eq_one
    (B : GraphBlock G)
    (hdegree :
      (blockCutIncidence G).degree
        (.inl B : BlockCutNode G) = 1) :
    ∃ c ∈ B.carrier, IsCutVertex G c := by
  classical
  obtain ⟨n, hnAdj, -⟩ :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
      hdegree)
  cases n with
  | inl C =>
      simp at hnAdj
  | inr c =>
      exact ⟨c.1, hnAdj, c.2⟩

/--
The local conclusion required of every feasible anchored block: after
removing the anchor, the block still contains either the marked target or
the anchor's possible second exceptional vertex.
-/
def AnchoredBlockMeetsExceptions
    (G : SimpleGraph V) (marked : Finset V) (target : V) : Prop :=
  ∀ (B : GraphBlock G)
    (_hfeasible : IsFeasibleBlock G marked B)
    (A : FeasibleBlockAnchor G marked B target),
    ∃ v ∈ B.carrier.erase A.b,
      v = target ∨ v = A.zPrime

/--
If the anchored-block conclusion holds, every leaf block contains a marked
vertex which is not a cut vertex.

The proof is useful in contrapositive form.  If all marked carrier vertices
were cut vertices, the unique cut vertex of a leaf block would be the only
special carrier vertex.  The block would therefore be feasible, while the
anchored conclusion would produce a second special vertex after deleting
the unique cut.
-/
theorem exists_marked_noncut_of_block_degree_eq_one
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target)
    (B : GraphBlock G)
    (hdegree :
      (blockCutIncidence G).degree
        (.inl B : BlockCutNode G) = 1) :
    ∃ r ∈ B.carrier,
      r ∈ marked ∧ ¬IsCutVertex G r := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨c, hcB, hcCut⟩ :=
    exists_cut_mem_of_block_degree_eq_one B hdegree
  have hmarkedCut :
      ∀ {r : V}, r ∈ B.carrier →
        r ∈ marked → IsCutVertex G r := by
    intro r hrB hrMarked
    exact hno r hrB hrMarked
  have hspecialSubset :
      B.carrier ∩ (cutVertices G ∪ marked) ⊆ {c} := by
    intro r hr
    have hrB : r ∈ B.carrier :=
      (Finset.mem_inter.mp hr).1
    have hrSpecial :
        r ∈ cutVertices G ∪ marked :=
      (Finset.mem_inter.mp hr).2
    have hrCut : IsCutVertex G r := by
      rcases Finset.mem_union.mp hrSpecial with
        hrCut | hrMarked
      · simpa using hrCut
      · exact hmarkedCut hrB hrMarked
    have hrc :
        r = c :=
      cut_eq_of_mem_leaf_block B hdegree
        hrB hcB hrCut hcCut
    exact Finset.mem_singleton.mpr hrc
  have hspecialCard :
      (B.carrier ∩
        (cutVertices G ∪ marked)).card ≤ 1 := by
    calc
      (B.carrier ∩
          (cutVertices G ∪ marked)).card
          ≤ ({c} : Finset V).card :=
        Finset.card_le_card hspecialSubset
      _ = 1 := by simp
  have hcarrierMore :
      1 < B.carrier.card := by
    have := B.card_ge_two
    omega
  obtain ⟨ordinary, hordinaryB, hordinaryNe⟩ :=
    Finset.exists_mem_ne hcarrierMore c
  have hordinaryNotSpecial :
      ordinary ∉ cutVertices G ∪ marked := by
    intro hspecial
    have hordinaryCut : IsCutVertex G ordinary := by
      rcases Finset.mem_union.mp hspecial with
        hcut | hmarked
      · simpa using hcut
      · exact hmarkedCut hordinaryB hmarked
    have hoc :
        ordinary = c :=
      cut_eq_of_mem_leaf_block B hdegree
        hordinaryB hcB hordinaryCut hcCut
    exact hordinaryNe hoc
  have hfeasible :
      IsFeasibleBlock G marked B := by
    constructor
    · exact hspecialCard.trans (by omega)
    · exact
        ⟨ordinary,
          Finset.mem_sdiff.mpr
            ⟨hordinaryB, hordinaryNotSpecial⟩⟩
  obtain ⟨A⟩ :=
    B.exists_feasibleBlockAnchor
      hconnected marked target htarget hfeasible
  obtain ⟨r, hrErase, hrCase⟩ :=
    hanchored B hfeasible A
  have hrB : r ∈ B.carrier :=
    Finset.mem_of_mem_erase hrErase
  have hbCut : IsCutVertex G A.b := by
    rcases A.b_eq_target_or_cut with
      hbTarget | hbCut
    · have hbMarked : A.b ∈ marked := by
        rw [hbTarget]
        exact htarget
      exact hmarkedCut A.b_mem hbMarked
    · exact hbCut
  have hrCut : IsCutVertex G r := by
    rcases hrCase with hrTarget | hrPrime
    · subst r
      exact hmarkedCut hrB htarget
    · subst r
      rcases Finset.mem_union.mp A.zPrime_special with
        hzCut | hzMarked
      · simpa using hzCut
      · exact hmarkedCut A.zPrime_mem hzMarked
  have hrb :
      r = A.b :=
    cut_eq_of_mem_leaf_block B hdegree
      hrB A.b_mem hrCut hbCut
  exact (Finset.mem_erase.mp hrErase).1 hrb

/-- Degree-one nodes of the block--cut incidence graph. -/
abbrev IncidenceLeaf (G : SimpleGraph V) :=
  {n : BlockCutNode G //
    (blockCutIncidence G).degree n = 1}

/-- The block represented by an incidence leaf. -/
noncomputable def blockOfLeaf
    (hconnected : G.Connected)
    (n : IncidenceLeaf G) :
    GraphBlock G :=
  Classical.choose
    (exists_block_of_degree_eq_one
      hconnected n.2)

/-- The underlying incidence leaf is its selected block node. -/
theorem leaf_eq_inl_blockOfLeaf
    (hconnected : G.Connected)
    (n : IncidenceLeaf G) :
    n.1 = .inl (blockOfLeaf hconnected n) :=
  Classical.choose_spec
    (exists_block_of_degree_eq_one
      hconnected n.2)

/-- The selected block of an incidence leaf has degree one. -/
theorem blockOfLeaf_degree_eq_one
    (hconnected : G.Connected)
    (n : IncidenceLeaf G) :
    (blockCutIncidence G).degree
      (.inl (blockOfLeaf hconnected n) :
        BlockCutNode G) = 1 := by
  rw [← leaf_eq_inl_blockOfLeaf hconnected n]
  exact n.2

/-- A marked non-cut vertex selected from the block represented by a leaf. -/
noncomputable def markedVertexOfLeaf
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target)
    (n : IncidenceLeaf G) :
    {r : V // r ∈ marked} :=
  ⟨Classical.choose
      (exists_marked_noncut_of_block_degree_eq_one
        hconnected marked target htarget hanchored
        (blockOfLeaf hconnected n)
        (blockOfLeaf_degree_eq_one hconnected n)),
    (Classical.choose_spec
      (exists_marked_noncut_of_block_degree_eq_one
        hconnected marked target htarget hanchored
        (blockOfLeaf hconnected n)
        (blockOfLeaf_degree_eq_one hconnected n))).2.1⟩

/-- The selected marked vertex belongs to the corresponding leaf block. -/
theorem markedVertexOfLeaf_mem_block
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target)
    (n : IncidenceLeaf G) :
    (markedVertexOfLeaf
      hconnected marked target htarget hanchored n).1 ∈
        (blockOfLeaf hconnected n).carrier :=
  (Classical.choose_spec
    (exists_marked_noncut_of_block_degree_eq_one
      hconnected marked target htarget hanchored
      (blockOfLeaf hconnected n)
      (blockOfLeaf_degree_eq_one hconnected n))).1

/-- The selected marked vertex is not an ambient cut vertex. -/
theorem markedVertexOfLeaf_not_cut
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target)
    (n : IncidenceLeaf G) :
    ¬IsCutVertex G
      (markedVertexOfLeaf
        hconnected marked target htarget hanchored n).1 :=
  (Classical.choose_spec
    (exists_marked_noncut_of_block_degree_eq_one
      hconnected marked target htarget hanchored
      (blockOfLeaf hconnected n)
      (blockOfLeaf_degree_eq_one hconnected n))).2.2

/-- Distinct incidence leaves select distinct marked non-cut vertices. -/
theorem markedVertexOfLeaf_injective
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target) :
    Function.Injective
      (markedVertexOfLeaf
        hconnected marked target htarget hanchored) := by
  classical
  intro a b hab
  have hvalue :
      (markedVertexOfLeaf
          hconnected marked target htarget hanchored a).1 =
        (markedVertexOfLeaf
          hconnected marked target htarget hanchored b).1 :=
    congrArg Subtype.val hab
  have hblocks :
      blockOfLeaf hconnected a =
        blockOfLeaf hconnected b := by
    by_contra hne
    let r :=
      (markedVertexOfLeaf
        hconnected marked target htarget hanchored a).1
    have hrA :
        r ∈ (blockOfLeaf hconnected a).carrier :=
      markedVertexOfLeaf_mem_block
        hconnected marked target htarget hanchored a
    have hrB :
        r ∈ (blockOfLeaf hconnected b).carrier := by
      change
        (markedVertexOfLeaf
          hconnected marked target htarget hanchored a).1 ∈
            (blockOfLeaf hconnected b).carrier
      rw [hvalue]
      exact
        markedVertexOfLeaf_mem_block
          hconnected marked target htarget hanchored b
    have hrCut :
        IsCutVertex G r :=
      GraphBlock.isCutVertex_of_mem_inter
        hconnected
        (blockOfLeaf hconnected a)
        (blockOfLeaf hconnected b)
        hne hrA hrB
    exact
      (markedVertexOfLeaf_not_cut
        hconnected marked target htarget hanchored a)
        hrCut
  apply Subtype.ext
  calc
    a.1 =
        .inl (blockOfLeaf hconnected a) :=
      leaf_eq_inl_blockOfLeaf hconnected a
    _ =
        .inl (blockOfLeaf hconnected b) := by
      rw [hblocks]
    _ = b.1 :=
      (leaf_eq_inl_blockOfLeaf hconnected b).symm

/--
The local anchored-block conclusion bounds the number of incidence leaves
by the number of marked vertices.
-/
theorem leafVertices_card_le_marked
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target) :
    (TreePath.leafVertices (blockCutIncidence G)).card ≤
      marked.card := by
  classical
  have hcard :
      Fintype.card (IncidenceLeaf G) ≤
        Fintype.card {r : V // r ∈ marked} :=
    Fintype.card_le_of_injective
      (markedVertexOfLeaf
        hconnected marked target htarget hanchored)
      (markedVertexOfLeaf_injective
        hconnected marked target htarget hanchored)
  rw [Fintype.card_subtype,
    Fintype.card_subtype] at hcard
  simpa [IncidenceLeaf,
    TreePath.leafVertices] using hcard

/--
If at most two vertices are marked, every node of the block--cut tree has
degree at most two.
-/
theorem incidence_degree_le_two
    [Nontrivial (BlockCutNode G)]
    (htree : (blockCutIncidence G).IsTree)
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hmarked : marked.card ≤ 2)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target)
    (n : BlockCutNode G) :
    (blockCutIncidence G).degree n ≤ 2 := by
  apply
    TreePath.degree_le_two_of_leafVertices_card_le_two
      htree
  exact
    (leafVertices_card_le_marked
      hconnected marked target htarget hanchored).trans
        hmarked

/--
Under the same hypotheses, the block--cut tree has exactly two leaves.
-/
theorem incidence_leafVertices_card_eq_two
    [Nontrivial (BlockCutNode G)]
    (htree : (blockCutIncidence G).IsTree)
    (hconnected : G.Connected)
    (marked : Finset V) (target : V)
    (htarget : target ∈ marked)
    (hmarked : marked.card ≤ 2)
    (hanchored :
      AnchoredBlockMeetsExceptions G marked target) :
    (TreePath.leafVertices
      (blockCutIncidence G)).card = 2 := by
  apply
    TreePath.leafVertices_card_eq_two_of_card_le_two
      htree
  exact
    (leafVertices_card_le_marked
      hconnected marked target htarget hanchored).trans
        hmarked

end BlockCutIncidence

end DeanK5
