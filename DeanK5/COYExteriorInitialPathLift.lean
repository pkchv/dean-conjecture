import DeanK5.COYExteriorInitialCompression
import DeanK5.COYConcatenation

/-!
# Lifting the initial-side exterior compression

A path across the quotient lifts from an actual `S`-attachment to the
retained anchor `b`.  Appending the fixed `b`--`y` connector produces the
outer family used in COY Cases 2.2 and 2.3.  The support certificate keeps
the subsequent Fact 1 concatenation explicitly simple.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/-- A lifted family from actual initial `S`-attachments to `y`. -/
structure LiftedInitialToYData
    (C : P.ExteriorFeasibleBlockChoice) (s : ℕ) where
  /-- The semi-admissible outer family. -/
  family :
    SemiAdmissibleSetPathFamily G
      (↑C.initialAttachments : Set V) y s
  /-- Apart from its endpoint, every path vertex lies in the exterior. -/
  support_class :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = family.endpoint i ∨
        v ∈ P.working.rooted.otherRegion
  /--
  The sharper support decomposition retained from the construction:
  besides its initial endpoint, a lifted path stays in the selected block
  or in the tail of the fixed connector.
  -/
  support_decomp :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = family.endpoint i ∨
        v ∈ C.ambientCarrier ∨
          v ∈ C.pathToY.walk.support.tail

namespace LiftedInitialToYData

variable {C : P.ExteriorFeasibleBlockChoice} {s : ℕ}

/--
A lifted family avoids any exterior vertex that lies outside the selected
block and outside the fixed connector.
-/
theorem avoids_of_not_mem_block_and_connector
    (D : C.LiftedInitialToYData s)
    {v : V}
    (hvRegion : v ∈ P.working.rooted.otherRegion)
    (hvBlock : v ∉ C.ambientCarrier)
    (hvConnector : v ∉ C.pathToY.walk.support)
    (i : Fin s) :
    v ∉ (D.family.path i).walk.support := by
  intro hvPath
  rcases D.support_decomp i v hvPath with
    hvEndpoint | hvCarrier | hvTail
  · subst v
    exact
      P.working.rooted.otherRegion_componentRegion.not_mem_separator
        hvRegion
        (P.working.rooted.core.S_subset_carrier
          (C.initialAttachments_subset_coreS
            (D.family.endpoint_mem i)))
  · exact hvBlock hvCarrier
  · exact hvConnector (List.mem_of_mem_tail hvTail)

end LiftedInitialToYData

/--
Lift a recursive initial compression family and append the fixed
block-to-`y` connector.
-/
theorem exists_liftedInitialToYData
    (C : P.ExteriorFeasibleBlockChoice)
    {s : ℕ}
    (F : AdmissiblePathFamily C.initialCompressionGraph
      (BoundaryCompression.collapsedRoot :
        BoundaryCompressionVertex C.compressionInterior)
      BoundaryCompression.retainedRoot s) :
    Nonempty (C.LiftedInitialToYData s) := by
  classical
  let L (i : Fin s) :
      BoundaryCompression.PathLift
        G C.compressionInterior
        C.initialCompressionBoundary C.b
        (F.path i) :=
    Classical.choice
      (BoundaryCompression.exists_pathLift
        C.compressionInterior_disjoint_initialCompressionBoundary
        C.b_mem_initialCompressionBoundary (F.path i))
  have hendpointInitial (i : Fin s) :
      (L i).endpoint ∈ C.initialAttachments := by
    have h :=
      (L i).endpoint_mem
    simpa using h
  have hdisjoint (i : Fin s) :
      (L i).path.walk.support.Disjoint
        C.pathToY.walk.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvLift hvTail
    have hvConnector :
        v ∈ C.pathToY.walk.support :=
      List.mem_of_mem_tail hvTail
    rcases (L i).support_class v hvLift with
      hvEndpoint | hvb | hvQ
    · subst v
      exact
        P.working.rooted.otherRegion_componentRegion.not_mem_separator
          (C.pathToY_support_mem_otherRegion hvConnector)
          (P.working.rooted.core.S_subset_carrier
            (C.initialAttachments_subset_coreS
              (hendpointInitial i)))
    · subst v
      exact C.pathToY.start_not_mem_tail hvTail
    · have hvBlock :
          v ∈ C.ambientCarrier :=
        Finset.mem_of_mem_erase hvQ
      have hvb' :
          v = C.b :=
        C.pathToY_meets_block_only_at_b hvConnector
          (by
            rw [C.mem_ambientCarrier] at hvBlock
            obtain ⟨w, hwB, hwv⟩ := hvBlock
            exact ⟨w, hwB, hwv⟩)
      exact (Finset.mem_erase.mp hvQ).1 hvb'
  let liftedPath (i : Fin s) :
      SimplePath G (L i).endpoint y :=
    (L i).path.appendDisjoint C.pathToY
      (hdisjoint i)
  have hlength (i : Fin s) :
      (liftedPath i).length =
        F.start + C.pathToY.length +
          i.val * F.step := by
    calc
      (liftedPath i).length =
          (L i).path.length + C.pathToY.length := by
        simp [liftedPath, SimplePath.appendDisjoint_length]
      _ = (F.path i).length + C.pathToY.length := by
        rw [(L i).length_eq]
      _ =
          (F.start + i.val * F.step) +
            C.pathToY.length := by
        rw [F.length_path]
      _ =
          F.start + C.pathToY.length +
            i.val * F.step := by
        omega
  let outer :
      SemiAdmissibleSetPathFamily G
        (↑C.initialAttachments : Set V) y s := {
    start := F.start + C.pathToY.length
    step := F.step
    admissible_step := F.admissible_step
    start_ge_one := by
      have := F.start_ge_two
      omega
    endpoint := fun i => (L i).endpoint
    endpoint_mem := hendpointInitial
    path := liftedPath
    length_path := hlength
    unique_endpoint := by
      intro i v hvPath hvInitial
      have hvParts :
          v ∈ (L i).path.walk.support ∨
            v ∈ C.pathToY.walk.support.tail := by
        change
          v ∈
            (((L i).path.appendDisjoint C.pathToY
              (hdisjoint i)).walk.support) at hvPath
        rw [SimplePath.appendDisjoint,
          SimpleGraph.Walk.support_append] at hvPath
        exact List.mem_append.mp hvPath
      rcases hvParts with hvLift | hvConnector
      · rcases (L i).support_meets_T v hvLift
            (by
              exact Finset.mem_insert_of_mem
                (by simpa using hvInitial)) with
          hvEndpoint | hvb
        · exact hvEndpoint
        · subst v
          exact False.elim
            (C.b_not_mem_initialAttachments
              (by simpa using hvInitial))
      · have hvSupport :
            v ∈ C.pathToY.walk.support :=
          List.mem_of_mem_tail hvConnector
        exact False.elim
          (P.working.rooted.otherRegion_componentRegion.not_mem_separator
              (C.pathToY_support_mem_otherRegion hvSupport)
              (P.working.rooted.core.S_subset_carrier
                (C.initialAttachments_subset_coreS
                  (by simpa using hvInitial))))
  }
  refine ⟨{
    family := outer
    support_class := ?_
    support_decomp := ?_
  }⟩
  intro i v hvPath
  have hvParts :
      v ∈ (L i).path.walk.support ∨
        v ∈ C.pathToY.walk.support.tail := by
    change
      v ∈
        (((L i).path.appendDisjoint C.pathToY
          (hdisjoint i)).walk.support) at hvPath
    rw [SimplePath.appendDisjoint,
      SimpleGraph.Walk.support_append] at hvPath
    exact List.mem_append.mp hvPath
  rcases hvParts with hvLift | hvConnector
  · rcases (L i).support_class v hvLift with
      hvEndpoint | hvb | hvQ
    · exact Or.inl hvEndpoint
    · exact Or.inr
        (hvb ▸ C.ambientCarrier_subset_otherRegion
          C.b_mem_ambientCarrier)
    · exact Or.inr
        (C.ambientCarrier_subset_otherRegion
          (Finset.mem_of_mem_erase hvQ))
  · exact Or.inr
      (C.pathToY_support_mem_otherRegion
        (List.mem_of_mem_tail hvConnector))
  · intro i v hvPath
    have hvParts :
        v ∈ (L i).path.walk.support ∨
          v ∈ C.pathToY.walk.support.tail := by
      change
        v ∈
          (((L i).path.appendDisjoint C.pathToY
            (hdisjoint i)).walk.support) at hvPath
      rw [SimplePath.appendDisjoint,
        SimpleGraph.Walk.support_append] at hvPath
      exact List.mem_append.mp hvPath
    rcases hvParts with hvLift | hvConnector
    · rcases (L i).support_class v hvLift with
        hvEndpoint | hvb | hvQ
      · exact Or.inl hvEndpoint
      · exact Or.inr
          (Or.inl
            (hvb ▸ C.b_mem_ambientCarrier))
      · exact Or.inr
          (Or.inl (Finset.mem_of_mem_erase hvQ))
    · exact Or.inr (Or.inr hvConnector)

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
