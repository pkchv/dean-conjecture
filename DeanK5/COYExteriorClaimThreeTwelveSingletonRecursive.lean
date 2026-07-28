import DeanK5.COYExteriorClaimThreeTwelveSingleton

/-!
# Degree retention in the singleton-boundary recursive graph

Claim 3.12(1) and uniqueness of the initial boundary imply that every
ambient neighbour of an ordinary block vertex survives in the induced
graph on `B ∪ {v}`.  Hence the recursive call loses no degree.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace SingletonInitialBoundary

variable {C : P.ExteriorFeasibleBlockChoice}

/--
Every ambient neighbour of an ordinary block vertex is either the unique
initial-boundary vertex or another vertex of the block.
-/
theorem ambient_neighbor_eq_vertex_or_mem_ambientCarrier
    (M : MinimalCounterexample q G x y z)
    (D : SingletonInitialBoundary C)
    {d w : V}
    (hd : d ∈ C.ambientCarrier)
    (hdb : d ≠ C.b) (hdzPrime : d ≠ C.zPrime)
    (hdw : G.Adj d w) :
    w = D.vertex ∨ w ∈ C.ambientCarrier := by
  by_cases hwCore :
      w ∈ P.working.rooted.core.carrier
  · left
    exact
      D.core_attachment_eq_vertex M hwCore
        (Finset.mem_erase.mpr ⟨hdb, hd⟩)
        hdw.symm
  · right
    have hdOther :
        d ∈ P.working.rooted.otherRegion :=
      C.ambientCarrier_subset_otherRegion hd
    have hwOther :
        w ∈ P.working.rooted.otherRegion :=
      P.working.rooted.otherRegion_componentRegion.closed
        hdOther hdw hwCore
    let wE : P.ExteriorVertex := ⟨w, hwOther⟩
    have hwBlock :
        wE ∈ C.block.carrier :=
      C.exterior_neighbor_mem_block
        hd hdb hdzPrime (w := wE) hdw
    exact C.mem_ambientCarrier.mpr
      ⟨wE, hwBlock, rfl⟩

/--
Every neighbour of an ordinary block vertex has a unique preimage in the
singleton-boundary recursive graph.
-/
theorem recursiveEmbedding_neighborSet_image
    (M : MinimalCounterexample q G x y z)
    (D : SingletonInitialBoundary C)
    {d : V}
    (hd : d ∈ C.ambientCarrier)
    (hdb : d ≠ C.b) (hdzPrime : d ≠ C.zPrime) :
    D.recursiveEmbedding ''
        D.recursiveGraph.neighborSet
          (some
            (⟨d, hd⟩ :
              (↑C.ambientCarrier : Set V))) =
      G.neighborSet d := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact D.recursiveEmbedding.toHom.map_rel' ha
  · intro hdw
    rcases
        D.ambient_neighbor_eq_vertex_or_mem_ambientCarrier
          M hd hdb hdzPrime hdw with
      rfl | hwBlock
    · refine ⟨none, ?_, rfl⟩
      exact
        (adjoinRoot_adj_none_some
          (G.induce (↑C.ambientCarrier : Set V))
          D.blockAttachments
          ⟨d, hd⟩).2
          ((D.mem_blockAttachments ⟨d, hd⟩).2
            hdw.symm)
    · refine
        ⟨some
          (⟨w, hwBlock⟩ :
            (↑C.ambientCarrier : Set V)),
          ?_, rfl⟩
      exact hdw

/-- Ordinary block vertices retain their full ambient degree. -/
theorem finiteDegree_recursiveGraph_some_eq
    (M : MinimalCounterexample q G x y z)
    (D : SingletonInitialBoundary C)
    {d : V}
    (hd : d ∈ C.ambientCarrier)
    (hdb : d ≠ C.b) (hdzPrime : d ≠ C.zPrime) :
    finiteDegree D.recursiveGraph
        (some
          (⟨d, hd⟩ :
            (↑C.ambientCarrier : Set V))) =
      finiteDegree G d := by
  unfold finiteDegree
  rw [← D.recursiveEmbedding_neighborSet_image
      M hd hdb hdzPrime,
    Set.ncard_image_of_injective _
      D.recursiveEmbedding.injective]

/-- The feasible ordinary vertex differs from the left recursive root. -/
theorem recursiveOrdinary_ne_leftRoot
    (D : SingletonInitialBoundary C) :
    some
        (⟨C.ordinary, C.ordinary_mem_ambientCarrier⟩ :
          (↑C.ambientCarrier : Set V)) ≠
      D.recursiveLeftRoot := by
  simp

/-- The feasible ordinary vertex differs from the block root. -/
theorem recursiveOrdinary_ne_blockRoot
    (D : SingletonInitialBoundary C) :
    some
        (⟨C.ordinary, C.ordinary_mem_ambientCarrier⟩ :
          (↑C.ambientCarrier : Set V)) ≠
      D.recursiveBlockRoot := by
  intro h
  apply C.ordinary_ne_b
  exact congrArg
    (fun w :
      Option (↑C.ambientCarrier : Set V) =>
        Option.getD w
          ⟨C.b, C.b_mem_ambientCarrier⟩ |>.1)
    h

/-- The feasible ordinary vertex differs from the recursive exception. -/
theorem recursiveOrdinary_ne_exception
    (D : SingletonInitialBoundary C) :
    some
        (⟨C.ordinary, C.ordinary_mem_ambientCarrier⟩ :
          (↑C.ambientCarrier : Set V)) ≠
      D.recursiveException := by
  intro h
  apply C.ordinary_ne_zPrime
  exact congrArg
    (fun w :
      Option (↑C.ambientCarrier : Set V) =>
        Option.getD w
          ⟨C.zPrime, C.zPrime_mem_ambientCarrier⟩ |>.1)
    h

/--
Minimality supplies `q` admissible paths from the unique boundary vertex
to the block anchor in the source graph on `B ∪ {v}`.
-/
theorem exists_recursive_family
    (M : MinimalCounterexample q G x y z)
    (D : SingletonInitialBoundary C) :
    Nonempty
      (AdmissiblePathFamily D.recursiveGraph
        D.recursiveLeftRoot D.recursiveBlockRoot q) := by
  let I :
      RootedInstance q D.recursiveGraph
        D.recursiveLeftRoot
        D.recursiveBlockRoot
        D.recursiveException := {
    q_pos := M.q_pos
    q_le_four := M.q_le_four
    roots_ne := D.recursiveRoots_ne
    rooted_two_connected :=
      D.recursiveRootedGraph_twoConnected
    ordinary_nonempty :=
      ⟨some
          (⟨C.ordinary, C.ordinary_mem_ambientCarrier⟩ :
            (↑C.ambientCarrier : Set V)),
        D.recursiveOrdinary_ne_leftRoot,
        D.recursiveOrdinary_ne_blockRoot,
        D.recursiveOrdinary_ne_exception⟩
    degree_lower := by
      intro w hwLeft hwBlock hwException
      cases w with
      | none =>
          exact False.elim (hwLeft rfl)
      | some d =>
          have hdb : d.1 ≠ C.b := by
            intro h
            apply hwBlock
            apply congrArg some
            apply Subtype.ext
            exact h
          have hdzPrime : d.1 ≠ C.zPrime := by
            intro h
            apply hwException
            apply congrArg some
            apply Subtype.ext
            exact h
          have hdx : d.1 ≠ x := by
            intro h
            have hdxCore :
                d.1 ∈ P.working.rooted.core.carrier := by
              rw [h]
              exact
                P.working.rooted.core.root_mem_carrier
            exact
              Finset.disjoint_left.mp
                C.ambientCarrier_disjoint_core
                d.2 hdxCore
          have hdy : d.1 ≠ y :=
            C.ordinary_block_vertex_ne_y
              d.2 hdb hdzPrime
          have hdz : d.1 ≠ z :=
            C.ordinary_block_vertex_ne_z
              d.2 hdb hdzPrime
          rw [D.finiteDegree_recursiveGraph_some_eq
            M d.2 hdb hdzPrime]
          exact M.degree_lower d.1 hdx hdy hdz
  }
  exact M.smaller_solvable I D.recursiveComplexity_lt

/-- Map the recursive family back to genuine ambient `v`--`b` paths. -/
theorem exists_ambient_vertex_to_b_family
    (M : MinimalCounterexample q G x y z)
    (D : SingletonInitialBoundary C) :
    Nonempty
      (AdmissiblePathFamily G D.vertex C.b q) := by
  obtain ⟨family⟩ := D.exists_recursive_family M
  exact
    ⟨family.mapEmbedding D.recursiveEmbedding⟩

end SingletonInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
