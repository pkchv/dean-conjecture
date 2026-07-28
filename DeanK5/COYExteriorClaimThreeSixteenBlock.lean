import DeanK5.COYExteriorClaimThreeFourteen
import DeanK5.COYExteriorClaimThreeThirteenAttachment
import DeanK5.COYExteriorClaimThreeSixteen
import DeanK5.Graph.NonseparableRootAdjunction

/-!
# The selected-block recursion in COY Claim 3.16

Claim 3.16 applies the induction hypothesis inside a block of the ordered
exterior block chain.  This file isolates that recursive side of the
argument.  The chain construction supplies two distinct interface vertices,
with a cut vertex on the left, shows that every other block vertex is
ordinary, and establishes equation (3.4), excluding a `T`-attachment away
from the right interface.

The recursive graph is the graph induced by the selected block.  Its
parameter is `q - 1`, and the left root is reused as the permitted
exceptional vertex.  Equation (3.3) shows that an ordinary block vertex
loses at most one neighbor when the working core is removed, so the ambient
degree lower bound `q + 1` becomes the required block degree lower bound
`q = (q - 1) + 1`.
-/

namespace DeanK5

open SimpleGraph
open scoped Sym2

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z s : V}
  {P : PreferredWorkingCoreData G x y z}

/--
The exact chain geometry required for the selected-block recursive call in
Claim 3.16.

The first three ordinary-vertex fields are deliberately explicit: in the
ordered chain they follow from the facts that `left` and `right` are the
only cut vertices of the selected block and that the protected vertices
occur only at the ends of the chain.  The last field is equation (3.4).
-/
structure ClaimThreeSixteenBlockData
    (P : PreferredWorkingCoreData G x y z)
    (D : P.TypeThreeStage) where
  /-- The selected exterior block. -/
  block : GraphBlock P.exteriorGraph
  /-- The cut vertex at which the prefix enters the selected block. -/
  left : P.ExteriorVertex
  /-- The right interface, either a cut vertex or the terminal endpoint. -/
  right : P.ExteriorVertex
  /-- The left cut vertex belongs to the block. -/
  left_mem : left ∈ block.carrier
  /-- The right cut vertex belongs to the block. -/
  right_mem : right ∈ block.carrier
  /-- The left interface is a cut vertex of the exterior graph. -/
  left_isCut : IsCutVertex P.exteriorGraph left
  /-- The two displayed interface vertices are distinct. -/
  roots_ne : left ≠ right
  /-- The selected block is not a two-vertex bridge block. -/
  three_le_card : 3 ≤ block.carrier.card
  /-- Every nonroot block vertex is not a cut vertex of the exterior. -/
  ordinary_not_cut :
    ∀ d ∈ block.carrier, d ≠ left → d ≠ right →
      ¬IsCutVertex P.exteriorGraph d
  /-- Every nonroot block vertex is distinct from the second ambient root. -/
  ordinary_ne_y :
    ∀ d ∈ block.carrier, d ≠ left → d ≠ right →
      d.1 ≠ y
  /-- Every nonroot block vertex is distinct from the ambient exception. -/
  ordinary_ne_z :
    ∀ d ∈ block.carrier, d ≠ left → d ≠ right →
      d.1 ≠ z
  /--
  Equation (3.4): no vertex of the terminal side `T` is adjacent to a
  selected-block vertex before the right cut.
  -/
  no_terminal_attachment :
    ∀ d ∈ block.carrier, d ≠ right →
      ∀ t ∈ D.core.T, ¬G.Adj t d.1

namespace ClaimThreeSixteenBlockData

variable {D : P.TypeThreeStage}

/-- The vertex type of the graph induced by the selected block. -/
abbrev BlockVertex
    (C : ClaimThreeSixteenBlockData P D) :=
  (↑C.block.carrier : Set P.ExteriorVertex)

/-- The selected block, with its own finite vertex type. -/
abbrev recursiveGraph
    (C : ClaimThreeSixteenBlockData P D) :
    SimpleGraph C.BlockVertex :=
  P.exteriorGraph.induce
    (↑C.block.carrier : Set P.ExteriorVertex)

/-- The left cut vertex as a vertex of the induced block. -/
def recursiveLeftRoot
    (C : ClaimThreeSixteenBlockData P D) :
    C.BlockVertex :=
  ⟨C.left, C.left_mem⟩

/-- The right cut vertex as a vertex of the induced block. -/
def recursiveRightRoot
    (C : ClaimThreeSixteenBlockData P D) :
    C.BlockVertex :=
  ⟨C.right, C.right_mem⟩

/--
There is no additional exceptional block vertex in this recursion, so the
left root is reused as the typed exception.
-/
abbrev recursiveException
    (C : ClaimThreeSixteenBlockData P D) :
    C.BlockVertex :=
  C.recursiveLeftRoot

/-- The induced selected block embeds canonically in the ambient graph. -/
def recursiveEmbedding
    (C : ClaimThreeSixteenBlockData P D) :
    C.recursiveGraph ↪g G :=
  P.exteriorEmbedding.comp
    (Embedding.induce
      (↑C.block.carrier : Set P.ExteriorVertex))

@[simp] theorem recursiveEmbedding_apply
    (C : ClaimThreeSixteenBlockData P D)
    (d : C.BlockVertex) :
    C.recursiveEmbedding d = d.1.1 :=
  rfl

@[simp] theorem recursiveEmbedding_leftRoot
    (C : ClaimThreeSixteenBlockData P D) :
    C.recursiveEmbedding C.recursiveLeftRoot = C.left.1 :=
  rfl

@[simp] theorem recursiveEmbedding_rightRoot
    (C : ClaimThreeSixteenBlockData P D) :
    C.recursiveEmbedding C.recursiveRightRoot = C.right.1 :=
  rfl

/-- The typed recursive roots remain distinct. -/
theorem recursiveRoots_ne
    (C : ClaimThreeSixteenBlockData P D) :
    C.recursiveLeftRoot ≠ C.recursiveRightRoot := by
  intro h
  apply C.roots_ne
  exact congrArg Subtype.val h

/--
A nonroot selected-block vertex, packaged as the ordinary exterior vertex
to which equation (3.3) applies.
-/
def ordinaryExteriorVertex
    (C : ClaimThreeSixteenBlockData P D)
    (d : C.BlockVertex)
    (hdLeft : d ≠ C.recursiveLeftRoot)
    (hdRight : d ≠ C.recursiveRightRoot) :
    P.ExteriorOrdinaryVertex := by
  have hdLeft' : d.1 ≠ C.left := by
    intro h
    apply hdLeft
    apply Subtype.ext
    exact h
  have hdRight' : d.1 ≠ C.right := by
    intro h
    apply hdRight
    apply Subtype.ext
    exact h
  exact {
    vertex := d.1
    ne_y := C.ordinary_ne_y d.1 d.2 hdLeft' hdRight'
    ne_z := C.ordinary_ne_z d.1 d.2 hdLeft' hdRight'
    not_cut :=
      C.ordinary_not_cut d.1 d.2 hdLeft' hdRight'
  }

/-- Equation (3.3) for an ordinary vertex of the selected block. -/
theorem coreNeighbor_ncard_le_one
    (C : ClaimThreeSixteenBlockData P D)
    (M : MinimalCounterexample q G x y z)
    (d : C.BlockVertex)
    (hdLeft : d ≠ C.recursiveLeftRoot)
    (hdRight : d ≠ C.recursiveRightRoot) :
    (G.neighborSet d.1.1 ∩
      (↑P.working.rooted.core.carrier : Set V)).ncard ≤ 1 :=
  D.coreNeighbor_ncard_le_one M
    (C.ordinaryExteriorVertex d hdLeft hdRight)

/-- Equation (3.4), restated on the typed block vertex. -/
theorem not_adj_terminal_of_ne_right
    (C : ClaimThreeSixteenBlockData P D)
    (d : C.BlockVertex)
    (hdRight : d ≠ C.recursiveRightRoot)
    {t : V} (ht : t ∈ D.core.T) :
    ¬G.Adj t d.1.1 := by
  apply C.no_terminal_attachment d.1 d.2
  · intro h
    apply hdRight
    apply Subtype.ext
    exact h
  · exact ht

/--
An exterior neighbor of a nonroot block vertex cannot leave the selected
block, because such an edge would make that vertex an exterior cut vertex.
-/
theorem exterior_neighbor_mem_block
    (C : ClaimThreeSixteenBlockData P D)
    (d : C.BlockVertex)
    (hdLeft : d ≠ C.recursiveLeftRoot)
    (hdRight : d ≠ C.recursiveRightRoot)
    {w : P.ExteriorVertex}
    (hdw : P.exteriorGraph.Adj d.1 w) :
    w ∈ C.block.carrier := by
  by_contra hw
  exact
    (C.ordinaryExteriorVertex d hdLeft hdRight).not_cut
      (C.block.isCutVertex_of_adj_outside
        P.exteriorGraph_connected d.2 hdw hw)

/--
For an ordinary block vertex, the induced-block neighbor set maps onto its
entire exterior neighbor set.
-/
theorem recursive_neighborSet_image
    (C : ClaimThreeSixteenBlockData P D)
    (d : C.BlockVertex)
    (hdLeft : d ≠ C.recursiveLeftRoot)
    (hdRight : d ≠ C.recursiveRightRoot) :
    Subtype.val ''
        C.recursiveGraph.neighborSet d =
      P.exteriorGraph.neighborSet d.1 := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hdw
    exact
      ⟨⟨w,
          C.exterior_neighbor_mem_block d hdLeft hdRight hdw⟩,
        hdw, rfl⟩

/-- Ordinary selected-block vertices retain their full exterior degree. -/
theorem finiteDegree_recursiveGraph_eq_exterior
    (C : ClaimThreeSixteenBlockData P D)
    (d : C.BlockVertex)
    (hdLeft : d ≠ C.recursiveLeftRoot)
    (hdRight : d ≠ C.recursiveRightRoot) :
    finiteDegree C.recursiveGraph d =
      finiteDegree P.exteriorGraph d.1 := by
  unfold finiteDegree
  rw [← C.recursive_neighborSet_image d hdLeft hdRight,
    Set.ncard_image_of_injective _ Subtype.val_injective]

/--
The ambient degree of an ordinary block vertex exceeds its induced-block
degree by at most one.  This is the exact combination of the component
degree decomposition and equation (3.3).
-/
theorem finiteDegree_ambient_le_recursive_add_one
    (C : ClaimThreeSixteenBlockData P D)
    (M : MinimalCounterexample q G x y z)
    (d : C.BlockVertex)
    (hdLeft : d ≠ C.recursiveLeftRoot)
    (hdRight : d ≠ C.recursiveRightRoot) :
    finiteDegree G d.1.1 ≤
      finiteDegree C.recursiveGraph d + 1 := by
  have hsplit :
      finiteDegree G d.1.1 =
        finiteDegree P.exteriorGraph d.1 +
          (G.neighborSet d.1.1 ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard := by
    simpa using
      (ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
        P.working.rooted.otherRegion_componentRegion d.1.2)
  rw [C.finiteDegree_recursiveGraph_eq_exterior
    d hdLeft hdRight]
  have hcore :=
    C.coreNeighbor_ncard_le_one M d hdLeft hdRight
  omega

/--
The selected block itself is 2-connected, and therefore so is the rooted
graph obtained by adjoining the artificial edge between its cut roots.
-/
theorem recursiveRootedGraph_twoConnected
    (C : ClaimThreeSixteenBlockData P D) :
    IsTwoConnected
      (C.recursiveGraph ⊔
        edge C.recursiveLeftRoot C.recursiveRightRoot) := by
  apply IsKConnected.mono
    (C.block.nonseparable.isTwoConnected_induce
      C.three_le_card)
  exact le_sup_left

/-- The recursive graph has no more edges than the ambient graph. -/
theorem recursiveGraph_edgeSet_ncard_le
    (C : ClaimThreeSixteenBlockData P D) :
    C.recursiveGraph.edgeSet.ncard ≤ G.edgeSet.ncard := by
  let e := C.recursiveEmbedding
  have hsubset :
      Sym2.map e '' C.recursiveGraph.edgeSet ⊆ G.edgeSet :=
    e.toHom.image_edgeSet_subset
  calc
    C.recursiveGraph.edgeSet.ncard =
        (Sym2.map e '' C.recursiveGraph.edgeSet).ncard := by
      rw [Set.ncard_image_of_injective _
        (Sym2.map.injective e.injective)]
    _ ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard hsubset

/--
The selected block has strictly fewer vertices than the ambient graph:
the ambient root belongs to the working core and hence cannot lie in the
exterior image of the block.
-/
theorem recursiveVertex_card_lt
    (C : ClaimThreeSixteenBlockData P D) :
    Fintype.card C.BlockVertex < Fintype.card V := by
  have hxNotRegion :
      x ∉ P.working.rooted.otherRegion := by
    intro hxRegion
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        hxRegion
        P.working.rooted.core.root_mem_carrier
  calc
    Fintype.card C.BlockVertex ≤
        Fintype.card P.ExteriorVertex :=
      Fintype.card_subtype_le _
    _ < Fintype.card V :=
      Fintype.card_subtype_lt hxNotRegion

/-- The selected-block recursion strictly decreases COY's complexity. -/
theorem recursiveComplexity_lt
    (C : ClaimThreeSixteenBlockData P D) :
    rootedComplexity C.recursiveGraph <
      rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    C.recursiveVertex_card_lt
    C.recursiveGraph_edgeSet_ncard_le

/--
Every ordinary recursive vertex has the degree required at parameter
`q - 1`.
-/
theorem recursive_degree_lower
    (C : ClaimThreeSixteenBlockData P D)
    (M : MinimalCounterexample q G x y z)
    (d : C.BlockVertex)
    (hdLeft : d ≠ C.recursiveLeftRoot)
    (hdRight : d ≠ C.recursiveRightRoot) :
    (q - 1) + 1 ≤ finiteDegree C.recursiveGraph d := by
  have hdx : d.1.1 ≠ x := by
    intro h
    have hxCore :
        d.1.1 ∈ P.working.rooted.core.carrier := by
      rw [h]
      exact P.working.rooted.core.root_mem_carrier
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        d.1.2 hxCore
  have hdy :=
    (C.ordinaryExteriorVertex d hdLeft hdRight).ne_y
  have hdz :=
    (C.ordinaryExteriorVertex d hdLeft hdRight).ne_z
  have hambient :=
    M.degree_lower d.1.1 hdx hdy hdz
  have hloss :=
    C.finiteDegree_ambient_le_recursive_add_one
      M d hdLeft hdRight
  have hq := M.q_pos
  omega

/--
The selected block is a valid recursive rooted instance with parameter
`q - 1`.  Reusing the left root as the exception expresses the source
case in which there is no additional exceptional block vertex.
-/
theorem recursiveInstance
    (C : ClaimThreeSixteenBlockData P D)
    (M : MinimalCounterexample q G x y z)
    (hS : D.core.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y}) :
    RootedInstance (q - 1) C.recursiveGraph
      C.recursiveLeftRoot C.recursiveRightRoot
      C.recursiveException :=
  RootedInstance.ofNoExtraException
    (q - 1) C.recursiveGraph
    C.recursiveLeftRoot C.recursiveRightRoot
    (by
      have hq :=
        P.three_le_q_of_typeThree_singleton_side
          M D.core D.core_eq hS hregion
      omega)
    (by
      have hq := M.q_le_four
      omega)
    C.recursiveRoots_ne
    C.recursiveRootedGraph_twoConnected
    (by
      intro d hdLeft hdRight
      exact C.recursive_degree_lower M d hdLeft hdRight)

/--
Package the selected-block construction as the recursive layer expected by
the Claim 3.16 path assembly.
-/
def recursiveStage
    (C : ClaimThreeSixteenBlockData P D)
    (M : MinimalCounterexample q G x y z)
    (hS : D.core.S = {s})
    (hregion : P.working.rooted.otherRegion ≠ {y})
    (assemble :
      ∀ middle :
        AdmissiblePathFamily C.recursiveGraph
          C.recursiveLeftRoot C.recursiveRightRoot (q - 1),
        ClaimThreeSixteenAssembly G x y
          C.recursiveGraph C.recursiveLeftRoot
          C.recursiveRightRoot middle) :
    ClaimThreeSixteenRecursiveStage
      (q := q) G x y C.recursiveGraph
        C.recursiveLeftRoot C.recursiveRightRoot
        C.recursiveException where
  recursiveInstance :=
    C.recursiveInstance M hS hregion
  complexity_lt := C.recursiveComplexity_lt
  assemble := assemble

end ClaimThreeSixteenBlockData

end PreferredWorkingCoreData

end COY

end DeanK5
