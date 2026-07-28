import DeanK5.COYExteriorFeasibleBlockCompression
import DeanK5.COYConcatenation

/-!
# Lifting the feasible-block compression to the second root

A recursive path from the collapsed root to the retained anchor lifts to a
path from an actual working-core `T`-vertex to `b`.  Appending the fixed
`b`--`y` connector yields the semi-admissible outer family used in COY
Fact 1.
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

/--
The lifted family together with the support separation needed for the final
Fact 1 application.
-/
structure LiftedTerminalToYData
    (C : P.ExteriorFeasibleBlockChoice) (s : ℕ) where
  /-- A semi-admissible family from the actual `T`-attachments to `y`. -/
  family :
    SemiAdmissibleSetPathFamily G
      (↑C.terminalAttachments : Set V) y s
  /-- Apart from its `T`-endpoint, every path vertex lies in the exterior. -/
  support_class :
    ∀ i v, v ∈ (family.path i).walk.support →
      v = family.endpoint i ∨
        v ∈ P.working.rooted.otherRegion

/--
Lift a recursive compression family and append the fixed block-to-`y`
connector.  Every concatenation is proved simple from the recorded block
intersection property.
-/
theorem exists_liftedTerminalToYData
    (C : P.ExteriorFeasibleBlockChoice)
    {s : ℕ}
    (F : AdmissiblePathFamily C.compressionGraph
      (BoundaryCompression.collapsedRoot :
        BoundaryCompressionVertex C.compressionInterior)
      BoundaryCompression.retainedRoot s) :
    Nonempty (C.LiftedTerminalToYData s) := by
  classical
  let L (i : Fin s) :
      BoundaryCompression.PathLift
        G C.compressionInterior C.compressionBoundary C.b
        (F.path i) :=
    Classical.choice
      (BoundaryCompression.exists_pathLift
        C.compressionInterior_disjoint_compressionBoundary
        C.b_mem_compressionBoundary (F.path i))
  have hendpointTerminal (i : Fin s) :
      (L i).endpoint ∈ C.terminalAttachments := by
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
          (P.working.rooted.core.T_subset_carrier
            (C.terminalAttachments_subset_coreT
              (hendpointTerminal i)))
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
        (↑C.terminalAttachments : Set V) y s := {
    start := F.start + C.pathToY.length
    step := F.step
    admissible_step := F.admissible_step
    start_ge_one := by
      have := F.start_ge_two
      omega
    endpoint := fun i => (L i).endpoint
    endpoint_mem := hendpointTerminal
    path := liftedPath
    length_path := hlength
    unique_endpoint := by
      intro i v hvPath hvTerminal
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
                (by simpa using hvTerminal)) with
          hvEndpoint | hvb
        · exact hvEndpoint
        · subst v
          exact False.elim
            (C.b_not_mem_terminalAttachments
              (by simpa using hvTerminal))
      · have hvSupport :
            v ∈ C.pathToY.walk.support :=
          List.mem_of_mem_tail hvConnector
        exact False.elim
          (P.working.rooted.otherRegion_componentRegion.not_mem_separator
              (C.pathToY_support_mem_otherRegion hvSupport)
              (P.working.rooted.core.T_subset_carrier
                (C.terminalAttachments_subset_coreT
                  (by simpa using hvTerminal))))
  }
  refine ⟨{
    family := outer
    support_class := ?_
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

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
