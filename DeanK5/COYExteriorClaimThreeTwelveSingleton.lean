import DeanK5.COYExteriorClaimThreeTwelveBoundary
import DeanK5.Graph.NonseparableRootAdjunction

/-!
# The singleton-boundary recursive graph in COY Claim 3.12

When the initial boundary of `B - b` is `{v}`, the source recurses in the
induced graph on `B ∪ {v}` rooted at `(v,b)`.  We represent that graph as
an induced copy of `B` with `v` adjoined at precisely its genuine block
neighbours.  The artificial root edge `vb` is added only in the
2-connectivity premise, not to the recursive graph itself.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace SingletonInitialBoundary

variable {C : P.ExteriorFeasibleBlockChoice}

/-- The genuine neighbours of the singleton boundary vertex in the block. -/
noncomputable def blockAttachments
    (D : SingletonInitialBoundary C) :
    Finset (↑C.ambientCarrier : Set V) :=
  by
    classical
    exact Finset.univ.filter fun d => G.Adj D.vertex d.1

@[simp] theorem mem_blockAttachments
    (D : SingletonInitialBoundary C)
    (d : (↑C.ambientCarrier : Set V)) :
    d ∈ D.blockAttachments ↔ G.Adj D.vertex d.1 := by
  classical
  simp [blockAttachments]

/-- The source graph induced by `B ∪ {v}`, with no artificial root edge. -/
noncomputable abbrev recursiveGraph
    (D : SingletonInitialBoundary C) :
    SimpleGraph (Option (↑C.ambientCarrier : Set V)) :=
  adjoinRoot
    (G.induce (↑C.ambientCarrier : Set V))
    D.blockAttachments

/-- The singleton boundary vertex is the left recursive root. -/
abbrev recursiveLeftRoot
    (_D : SingletonInitialBoundary C) :
    Option (↑C.ambientCarrier : Set V) :=
  none

/-- The block anchor is the right recursive root. -/
def recursiveBlockRoot
    (_D : SingletonInitialBoundary C) :
    Option (↑C.ambientCarrier : Set V) :=
  some ⟨C.b, C.b_mem_ambientCarrier⟩

/-- The possible second special block vertex is the recursive exception. -/
def recursiveException
    (_D : SingletonInitialBoundary C) :
    Option (↑C.ambientCarrier : Set V) :=
  some ⟨C.zPrime, C.zPrime_mem_ambientCarrier⟩

/--
The adjoined-root representation is exactly the ambient graph induced on
`B ∪ {v}`.
-/
noncomputable def recursiveEmbedding
    (D : SingletonInitialBoundary C) :
    D.recursiveGraph ↪g G where
  toFun
    | none => D.vertex
    | some d => d.1
  inj' := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some d =>
            exfalso
            apply D.vertex_not_mem_ambientCarrier
            change D.vertex = d.1 at hab
            rw [hab]
            exact d.2
    | some d =>
        cases b with
        | none =>
            exfalso
            apply D.vertex_not_mem_ambientCarrier
            change d.1 = D.vertex at hab
            rw [← hab]
            exact d.2
        | some e =>
            congr
            exact Subtype.ext hab
  map_rel_iff' := by
    intro a b
    cases a with
    | none =>
        cases b with
        | none => simp
        | some d =>
            exact D.mem_blockAttachments d |>.symm
    | some d =>
        cases b with
        | none =>
            rw [G.adj_comm]
            exact D.mem_blockAttachments d |>.symm
        | some e =>
            rfl

@[simp] theorem recursiveEmbedding_none
    (D : SingletonInitialBoundary C) :
    D.recursiveEmbedding none = D.vertex :=
  rfl

@[simp] theorem recursiveEmbedding_some
    (D : SingletonInitialBoundary C)
    (d : (↑C.ambientCarrier : Set V)) :
    D.recursiveEmbedding (some d) = d.1 :=
  rfl

/-- The two recursive roots are distinct. -/
theorem recursiveRoots_ne
    (D : SingletonInitialBoundary C) :
    D.recursiveLeftRoot ≠ D.recursiveBlockRoot := by
  simp [recursiveBlockRoot]

/--
The unique boundary vertex has an actual neighbour in the nonanchor part
of the block.
-/
theorem exists_nonanchor_blockAttachment
    (D : SingletonInitialBoundary C) :
    ∃ d : (↑C.ambientCarrier : Set V),
      d ∈ D.blockAttachments ∧
        d ≠ ⟨C.b, C.b_mem_ambientCarrier⟩ := by
  obtain ⟨d, hdInterior, hvd⟩ :=
    D.exists_adjacent_in_compressionInterior
  let dB : (↑C.ambientCarrier : Set V) :=
    ⟨d, Finset.mem_of_mem_erase hdInterior⟩
  refine ⟨dB, ?_, ?_⟩
  · exact D.mem_blockAttachments dB |>.2 hvd
  · intro h
    exact (Finset.mem_erase.mp hdInterior).1
      (congrArg Subtype.val h)

/-- Adding the artificial root edge is the same as adding `b` to the
attachment set. -/
theorem recursiveRootedGraph_eq
    (D : SingletonInitialBoundary C) :
    D.recursiveGraph ⊔
        edge D.recursiveLeftRoot D.recursiveBlockRoot =
      adjoinRoot
        (G.induce (↑C.ambientCarrier : Set V))
        (insert
          ⟨C.b, C.b_mem_ambientCarrier⟩
          D.blockAttachments) := by
  classical
  ext a b
  cases a with
  | none =>
      cases b with
      | none => simp [recursiveGraph, recursiveBlockRoot]
      | some d =>
          simp [recursiveGraph, recursiveBlockRoot, edge]
          exact or_comm
  | some d =>
      cases b with
      | none =>
          simp [recursiveGraph, recursiveBlockRoot, edge]
          exact or_comm
      | some e =>
          simp [recursiveGraph, recursiveBlockRoot, edge]

/-- The attachment set used in the rooted graph has at least two vertices. -/
theorem two_le_card_insert_blockRoot
    (D : SingletonInitialBoundary C) :
    2 ≤
      (insert
        ⟨C.b, C.b_mem_ambientCarrier⟩
        D.blockAttachments).card := by
  obtain ⟨d, hdAttachment, hdb⟩ :=
    D.exists_nonanchor_blockAttachment
  have hpair :
      ({⟨C.b, C.b_mem_ambientCarrier⟩, d} :
        Finset (↑C.ambientCarrier : Set V)).card = 2 := by
    simp [hdb.symm]
  have hsubset :
      ({⟨C.b, C.b_mem_ambientCarrier⟩, d} :
        Finset (↑C.ambientCarrier : Set V)) ⊆
        insert
          ⟨C.b, C.b_mem_ambientCarrier⟩
          D.blockAttachments := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hdAttachment
  rw [← hpair]
  exact Finset.card_le_card hsubset

/-- The singleton-boundary recursive graph satisfies rooted 2-connectivity. -/
theorem recursiveRootedGraph_twoConnected
    (D : SingletonInitialBoundary C) :
    IsTwoConnected
      (D.recursiveGraph ⊔
        edge D.recursiveLeftRoot D.recursiveBlockRoot) := by
  rw [D.recursiveRootedGraph_eq]
  exact C.ambientCarrier_nonseparable.isTwoConnected_adjoinRoot
    (insert
      ⟨C.b, C.b_mem_ambientCarrier⟩
      D.blockAttachments)
    D.two_le_card_insert_blockRoot

/-- The recursive graph has no more edges than the ambient graph. -/
theorem recursiveGraph_edgeSet_ncard_le
    (D : SingletonInitialBoundary C) :
    D.recursiveGraph.edgeSet.ncard ≤ G.edgeSet.ncard := by
  let e := D.recursiveEmbedding
  have hsubset :
      Sym2.map e '' D.recursiveGraph.edgeSet ⊆ G.edgeSet :=
    e.toHom.image_edgeSet_subset
  calc
    D.recursiveGraph.edgeSet.ncard =
        (Sym2.map e '' D.recursiveGraph.edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective e.injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/-- The singleton-boundary recursive vertex type is strictly smaller. -/
theorem recursiveVertex_card_lt
    (_D : SingletonInitialBoundary C) :
    Fintype.card (Option (↑C.ambientCarrier : Set V)) <
      Fintype.card V := by
  have hunion :
      (C.ambientCarrier ∪
        P.working.rooted.core.carrier).card ≤
          (Finset.univ : Finset V).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint
      C.ambientCarrier_disjoint_core,
    Finset.card_univ] at hunion
  have hcore :
      3 ≤ P.working.rooted.core.carrier.card :=
    P.working.rooted.core.three_le_card_carrier
  have hambientCard :
      Fintype.card (↑C.ambientCarrier : Set V) =
        C.ambientCarrier.card := by
    rw [Set.fintypeCard_eq_ncard,
      Set.ncard_coe_finset]
  rw [Fintype.card_option, hambientCard]
  omega

/-- The singleton-boundary recursive graph is strictly smaller in the
COY induction measure. -/
theorem recursiveComplexity_lt
    (D : SingletonInitialBoundary C) :
    rootedComplexity D.recursiveGraph <
      rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    D.recursiveVertex_card_lt
    D.recursiveGraph_edgeSet_ncard_le

end SingletonInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
