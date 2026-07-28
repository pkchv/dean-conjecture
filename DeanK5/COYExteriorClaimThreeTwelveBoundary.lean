import DeanK5.COYExteriorClaimThreeTwelveTerminal

/-!
# The initial boundary in COY Claim 3.12

After Claim 3.12(1), every working-core neighbour of `B - b` lies in
`{x} ∪ S`.  This file records that source boundary and packages its
singleton alternative.
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
The source boundary
`N_G(B - b) ∩ ({x} ∪ S)`, represented by its core endpoints.
-/
noncomputable def initialBoundary
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  by
    classical
    exact
      (insert x P.working.rooted.core.S).filter fun v =>
        ∃ d ∈ C.compressionInterior, G.Adj v d

@[simp] theorem mem_initialBoundary
    (C : P.ExteriorFeasibleBlockChoice) {v : V} :
    v ∈ C.initialBoundary ↔
      v ∈ insert x P.working.rooted.core.S ∧
        ∃ d ∈ C.compressionInterior, G.Adj v d := by
  classical
  simp [initialBoundary]

/--
Once Claim 3.12(1) has removed all `T`-attachments, every core endpoint
of an edge into `B - b` belongs to the initial boundary.
-/
theorem core_attachment_mem_initialBoundary_of_terminal_empty
    (C : P.ExteriorFeasibleBlockChoice)
    (hterminal : C.terminalAttachments = ∅)
    {v d : V}
    (hvCore : v ∈ P.working.rooted.core.carrier)
    (hd : d ∈ C.compressionInterior)
    (hvd : G.Adj v d) :
    v ∈ C.initialBoundary := by
  classical
  by_cases hvx : v = x
  · subst v
    exact C.mem_initialBoundary.mpr
      ⟨Finset.mem_insert_self _ _, ⟨d, hd, hvd⟩⟩
  rcases
      P.working.rooted.core.mem_S_or_mem_T_of_mem_carrier_of_ne_root
        hvCore hvx with hvS | hvT
  · exact C.mem_initialBoundary.mpr
      ⟨Finset.mem_insert_of_mem hvS, ⟨d, hd, hvd⟩⟩
  · have hvTerminal : v ∈ C.terminalAttachments := by
      change
        v ∈ P.working.rooted.core.T.filter
          (fun t => ∃ d ∈ C.compressionInterior, G.Adj t d)
      exact Finset.mem_filter.mpr
        ⟨hvT, ⟨d, hd, hvd⟩⟩
    rw [hterminal] at hvTerminal
    simp at hvTerminal

/--
The same containment with the terminal exclusion discharged by the
minimal-counterexample argument.
-/
theorem core_attachment_mem_initialBoundary
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    {v d : V}
    (hvCore : v ∈ P.working.rooted.core.carrier)
    (hd : d ∈ C.compressionInterior)
    (hvd : G.Adj v d) :
    v ∈ C.initialBoundary :=
  C.core_attachment_mem_initialBoundary_of_terminal_empty
    (C.terminalAttachments_eq_empty M) hvCore hd hvd

/-- Data for the singleton alternative of the initial boundary. -/
structure SingletonInitialBoundary
    (C : P.ExteriorFeasibleBlockChoice) where
  /-- The unique boundary vertex in `{x} ∪ S`. -/
  vertex : V
  /-- The source boundary consists exactly of that vertex. -/
  boundary_eq : C.initialBoundary = {vertex}

namespace SingletonInitialBoundary

variable {C : P.ExteriorFeasibleBlockChoice}

/-- The chosen vertex belongs to the initial boundary. -/
theorem vertex_mem_initialBoundary
    (D : SingletonInitialBoundary C) :
    D.vertex ∈ C.initialBoundary := by
  rw [D.boundary_eq]
  simp

/-- The chosen vertex lies in `{x} ∪ S`. -/
theorem vertex_mem_root_insert_S
    (D : SingletonInitialBoundary C) :
    D.vertex ∈ insert x P.working.rooted.core.S :=
  (C.mem_initialBoundary.mp D.vertex_mem_initialBoundary).1

/-- The chosen vertex lies in the working-core carrier. -/
theorem vertex_mem_core
    (D : SingletonInitialBoundary C) :
    D.vertex ∈ P.working.rooted.core.carrier := by
  have h := D.vertex_mem_root_insert_S
  rcases Finset.mem_insert.mp h with hvx | hvS
  · rw [hvx]
    exact P.working.rooted.core.root_mem_carrier
  · exact P.working.rooted.core.S_subset_carrier hvS

/-- The chosen core vertex is outside the selected exterior block. -/
theorem vertex_not_mem_ambientCarrier
    (D : SingletonInitialBoundary C) :
    D.vertex ∉ C.ambientCarrier := by
  intro hvB
  exact Finset.disjoint_left.mp
    C.ambientCarrier_disjoint_core hvB D.vertex_mem_core

/-- The unique boundary vertex has a neighbour in `B - b`. -/
theorem exists_adjacent_in_compressionInterior
    (D : SingletonInitialBoundary C) :
    ∃ d ∈ C.compressionInterior, G.Adj D.vertex d :=
  (C.mem_initialBoundary.mp D.vertex_mem_initialBoundary).2

/--
Every core endpoint of an edge into `B - b` is the unique initial-boundary
vertex.
-/
theorem core_attachment_eq_vertex
    (M : MinimalCounterexample q G x y z)
    (D : SingletonInitialBoundary C)
    {v d : V}
    (hvCore : v ∈ P.working.rooted.core.carrier)
    (hd : d ∈ C.compressionInterior)
    (hvd : G.Adj v d) :
    v = D.vertex := by
  have hvBoundary :=
    C.core_attachment_mem_initialBoundary M hvCore hd hvd
  rw [D.boundary_eq] at hvBoundary
  simpa using hvBoundary

end SingletonInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
