import DeanK5.COYExteriorClaimThreeTwelveEmpty
import DeanK5.Graph.NonseparableRootAdjunction

/-!
# The empty-boundary recursive graph in COY Claim 3.12

Once the initial boundary is empty, the recursive graph is simply the
graph induced by the selected block.  Its roots are `zPrime` and `b`;
`zPrime` is also reused as the permitted exceptional vertex.
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

namespace EmptyInitialBoundary

variable {C : P.ExteriorFeasibleBlockChoice}

/-- The source graph `B` in the empty-boundary branch. -/
abbrev recursiveGraph
    (_D : EmptyInitialBoundary C) :
    SimpleGraph (↑C.ambientCarrier : Set V) :=
  G.induce (↑C.ambientCarrier : Set V)

/-- The source vertex `zPrime`, used as the left recursive root. -/
def recursiveLeftRoot
    (_D : EmptyInitialBoundary C) :
    (↑C.ambientCarrier : Set V) :=
  ⟨C.zPrime, C.zPrime_mem_ambientCarrier⟩

/-- The block anchor, used as the right recursive root. -/
def recursiveBlockRoot
    (_D : EmptyInitialBoundary C) :
    (↑C.ambientCarrier : Set V) :=
  ⟨C.b, C.b_mem_ambientCarrier⟩

/-- Reusing the left root excludes no additional ordinary vertex. -/
abbrev recursiveException
    (D : EmptyInitialBoundary C) :
    (↑C.ambientCarrier : Set V) :=
  D.recursiveLeftRoot

/-- The induced block embeds into the ambient graph. -/
def recursiveEmbedding
    (D : EmptyInitialBoundary C) :
    D.recursiveGraph ↪g G :=
  Embedding.induce (↑C.ambientCarrier : Set V)

/-- The two recursive roots are distinct. -/
theorem recursiveRoots_ne
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    D.recursiveLeftRoot ≠ D.recursiveBlockRoot := by
  intro h
  exact D.zPrime_ne_b M
    (by
      simpa [recursiveLeftRoot, recursiveBlockRoot] using
        congrArg Subtype.val h)

/-- The block contains the three distinct vertices `ordinary,b,zPrime`. -/
theorem three_le_ambientCarrier_card
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    3 ≤ C.ambientCarrier.card := by
  have hbz : C.b ≠ C.zPrime :=
    (D.zPrime_ne_b M).symm
  have hcard :
      ({C.ordinary, C.b, C.zPrime} : Finset V).card = 3 := by
    simp [C.ordinary_ne_b, C.ordinary_ne_zPrime,
      hbz]
  rw [← hcard]
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_insert,
    Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact C.ordinary_mem_ambientCarrier
  · exact C.b_mem_ambientCarrier
  · exact C.zPrime_mem_ambientCarrier

/-- The induced block, and hence its rooted supergraph, is 2-connected. -/
theorem recursiveRootedGraph_twoConnected
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    IsTwoConnected
      (D.recursiveGraph ⊔
        edge D.recursiveLeftRoot D.recursiveBlockRoot) := by
  apply IsKConnected.mono
    (C.ambientCarrier_nonseparable.isTwoConnected_induce
      (D.three_le_ambientCarrier_card M))
  exact le_sup_left

/-- Every ambient neighbour of an ordinary block vertex remains in `B`. -/
theorem ambient_neighbor_mem_ambientCarrier
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {d w : V}
    (hd : d ∈ C.ambientCarrier)
    (hdb : d ≠ C.b) (hdzPrime : d ≠ C.zPrime)
    (hdw : G.Adj d w) :
    w ∈ C.ambientCarrier := by
  by_cases hwCore :
      w ∈ P.working.rooted.core.carrier
  · exact False.elim
      (D.not_adj_core_interior M
        (Finset.mem_erase.mpr ⟨hdb, hd⟩)
        hwCore hdw)
  · have hwRegion :
        w ∈ P.working.rooted.otherRegion :=
      P.working.rooted.otherRegion_componentRegion.closed
        (C.ambientCarrier_subset_otherRegion hd)
        hdw hwCore
    let wE : P.ExteriorVertex := ⟨w, hwRegion⟩
    have hwBlock :
        wE ∈ C.block.carrier :=
      C.exterior_neighbor_mem_block
        hd hdb hdzPrime (w := wE) hdw
    exact C.mem_ambientCarrier.mpr
      ⟨wE, hwBlock, rfl⟩

/-- The induced embedding maps the full recursive neighbour set onto the
ambient neighbour set of every ordinary block vertex. -/
theorem recursiveEmbedding_neighborSet_image
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {d : V}
    (hd : d ∈ C.ambientCarrier)
    (hdb : d ≠ C.b) (hdzPrime : d ≠ C.zPrime) :
    D.recursiveEmbedding ''
        D.recursiveGraph.neighborSet
          (⟨d, hd⟩ :
            (↑C.ambientCarrier : Set V)) =
      G.neighborSet d := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact D.recursiveEmbedding.toHom.map_rel' ha
  · intro hdw
    have hwB :=
      D.ambient_neighbor_mem_ambientCarrier
        M hd hdb hdzPrime hdw
    exact
      ⟨(⟨w, hwB⟩ :
          (↑C.ambientCarrier : Set V)),
        hdw, rfl⟩

/-- Ordinary block vertices retain their full ambient degree. -/
theorem finiteDegree_recursiveGraph_eq
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {d : V}
    (hd : d ∈ C.ambientCarrier)
    (hdb : d ≠ C.b) (hdzPrime : d ≠ C.zPrime) :
    finiteDegree D.recursiveGraph
        (⟨d, hd⟩ :
          (↑C.ambientCarrier : Set V)) =
      finiteDegree G d := by
  unfold finiteDegree
  rw [← D.recursiveEmbedding_neighborSet_image
      M hd hdb hdzPrime,
    Set.ncard_image_of_injective _
      D.recursiveEmbedding.injective]

/-- The induced block has no more edges than the ambient graph. -/
theorem recursiveGraph_edgeSet_ncard_le
    (D : EmptyInitialBoundary C) :
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

/-- The induced block has strictly fewer vertices than the ambient graph. -/
theorem recursiveVertex_card_lt
    (_D : EmptyInitialBoundary C) :
    Fintype.card (↑C.ambientCarrier : Set V) <
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
  rw [hambientCard]
  omega

/-- The empty-boundary recursive graph is strictly smaller. -/
theorem recursiveComplexity_lt
    (D : EmptyInitialBoundary C) :
    rootedComplexity D.recursiveGraph <
      rootedComplexity G :=
  rootedComplexity_lt_of_card_lt_of_edgeCount_le
    D.recursiveVertex_card_lt
    D.recursiveGraph_edgeSet_ncard_le

/-- Minimality supplies `q` admissible `zPrime`--`b` paths in the block. -/
theorem exists_recursive_family
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    Nonempty
      (AdmissiblePathFamily D.recursiveGraph
        D.recursiveLeftRoot D.recursiveBlockRoot q) := by
  let ordinary :
      (↑C.ambientCarrier : Set V) :=
    ⟨C.ordinary, C.ordinary_mem_ambientCarrier⟩
  have hordinaryLeft :
      ordinary ≠ D.recursiveLeftRoot := by
    intro h
    exact C.ordinary_ne_zPrime
      (by
        simpa [ordinary, recursiveLeftRoot] using
          congrArg Subtype.val h)
  have hordinaryBlock :
      ordinary ≠ D.recursiveBlockRoot := by
    intro h
    exact C.ordinary_ne_b
      (by
        simpa [ordinary, recursiveBlockRoot] using
          congrArg Subtype.val h)
  let I :
      RootedInstance q D.recursiveGraph
        D.recursiveLeftRoot
        D.recursiveBlockRoot
        D.recursiveException := {
    q_pos := M.q_pos
    q_le_four := M.q_le_four
    roots_ne := D.recursiveRoots_ne M
    rooted_two_connected :=
      D.recursiveRootedGraph_twoConnected M
    ordinary_nonempty :=
      ⟨ordinary, hordinaryLeft,
        hordinaryBlock, hordinaryLeft⟩
    degree_lower := by
      intro d hdLeft hdBlock _
      have hdzPrime : d.1 ≠ C.zPrime := by
        intro h
        apply hdLeft
        apply Subtype.ext
        exact h
      have hdb : d.1 ≠ C.b := by
        intro h
        apply hdBlock
        apply Subtype.ext
        exact h
      have hdx : d.1 ≠ x := by
        intro h
        have hdCore :
            d.1 ∈ P.working.rooted.core.carrier := by
          rw [h]
          exact
            P.working.rooted.core.root_mem_carrier
        exact
          Finset.disjoint_left.mp
            C.ambientCarrier_disjoint_core
            d.2 hdCore
      have hdy : d.1 ≠ y :=
        C.ordinary_block_vertex_ne_y
          d.2 hdb hdzPrime
      have hdz : d.1 ≠ z :=
        C.ordinary_block_vertex_ne_z
          d.2 hdb hdzPrime
      rw [D.finiteDegree_recursiveGraph_eq
        M d.2 hdb hdzPrime]
      exact M.degree_lower d.1 hdx hdy hdz
  }
  exact M.smaller_solvable I D.recursiveComplexity_lt

/-- Map the recursive family back to ambient `zPrime`--`b` paths. -/
theorem exists_ambient_zPrime_to_b_family
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    Nonempty
      (AdmissiblePathFamily G C.zPrime C.b q) := by
  obtain ⟨family⟩ := D.exists_recursive_family M
  exact
    ⟨family.mapEmbedding D.recursiveEmbedding⟩

end EmptyInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
