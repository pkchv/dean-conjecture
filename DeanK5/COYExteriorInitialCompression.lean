import DeanK5.COYExteriorClaimThreeTwelve
import DeanK5.COYBoundaryCompressionBlock

/-!
# Compressing the initial-side attachments of the exterior block

After Claim 3.12, at least two vertices of `{x} ∪ S` meet the interior
`B - b` of the selected feasible block.  In particular, at least one
vertex of `S` does.  COY Cases 2.2 and 2.3 contract all such `S`-vertices
to one root while retaining `b` as the other root.  This file defines that
common compression and proves its structural properties.
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
The `S`-vertices of the working core with an edge to the nonanchor part
of the selected block.
-/
noncomputable def initialAttachments
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  by
    classical
    exact P.working.rooted.core.S.filter fun s =>
      ∃ d ∈ C.compressionInterior, G.Adj s d

@[simp] theorem mem_initialAttachments
    (C : P.ExteriorFeasibleBlockChoice) {s : V} :
    s ∈ C.initialAttachments ↔
      s ∈ P.working.rooted.core.S ∧
        ∃ d ∈ C.compressionInterior, G.Adj s d := by
  classical
  simp [initialAttachments]

/-- Every initial attachment lies on the `S`-side of the working core. -/
theorem initialAttachments_subset_coreS
    (C : P.ExteriorFeasibleBlockChoice) :
    C.initialAttachments ⊆ P.working.rooted.core.S := by
  intro s hs
  exact (C.mem_initialAttachments.mp hs).1

/-- Every `S`-attachment is represented in the full initial boundary. -/
theorem initialAttachments_subset_initialBoundary
    (C : P.ExteriorFeasibleBlockChoice) :
    C.initialAttachments ⊆ C.initialBoundary := by
  intro s hs
  obtain ⟨hsS, d, hd, hsd⟩ :=
    C.mem_initialAttachments.mp hs
  exact C.mem_initialBoundary.mpr
    ⟨Finset.mem_insert_of_mem hsS, ⟨d, hd, hsd⟩⟩

/--
The full initial boundary consists only of the root and the contracted
`S`-attachments.
-/
theorem initialBoundary_subset_insert_root_initialAttachments
    (C : P.ExteriorFeasibleBlockChoice) :
    C.initialBoundary ⊆ insert x C.initialAttachments := by
  intro v hv
  obtain ⟨hvRootS, d, hd, hvd⟩ :=
    C.mem_initialBoundary.mp hv
  rcases Finset.mem_insert.mp hvRootS with rfl | hvS
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (C.mem_initialAttachments.mpr
        ⟨hvS, ⟨d, hd, hvd⟩⟩)

/--
Claim 3.12(2) forces at least one genuine `S`-attachment: the singleton
set `{x}` cannot contain its two distinct initial-boundary vertices.
-/
theorem initialAttachments_nonempty
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice) :
    C.initialAttachments.Nonempty := by
  by_contra hempty
  have hzero :
      C.initialAttachments = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hsubset : C.initialBoundary ⊆ {x} := by
    intro v hv
    have hmem :=
      C.initialBoundary_subset_insert_root_initialAttachments hv
    rw [hzero] at hmem
    simpa using hmem
  have hcard :
      C.initialBoundary.card ≤ 1 := by
    have := Finset.card_le_card hsubset
    simpa using this
  have htwo :=
    C.two_le_initialBoundary_card M
  omega

/-- The source boundary for the initial-side compression. -/
noncomputable def initialCompressionBoundary
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  insert C.b C.initialAttachments

/-- The graph obtained by contracting the initial `S`-attachments. -/
noncomputable abbrev initialCompressionGraph
    (C : P.ExteriorFeasibleBlockChoice) :
    SimpleGraph
      (BoundaryCompressionVertex C.compressionInterior) :=
  BoundaryCompression.graph G C.compressionInterior
    C.initialCompressionBoundary C.b

/-- The initial compression with its artificial root edge adjoined. -/
noncomputable abbrev initialCompressionRootedGraph
    (C : P.ExteriorFeasibleBlockChoice) :
    SimpleGraph
      (BoundaryCompressionVertex C.compressionInterior) :=
  BoundaryCompression.rootedGraph G C.compressionInterior
    C.initialCompressionBoundary C.b

/-- The possible second block exception in the initial compression. -/
def initialCompressionException
    (C : P.ExteriorFeasibleBlockChoice) :
    BoundaryCompressionVertex C.compressionInterior :=
  if hz : C.zPrime ∈ C.compressionInterior then
    BoundaryCompression.inner ⟨C.zPrime, hz⟩
  else
    BoundaryCompression.retainedRoot

/-- The selected block is disjoint from all initial attachments. -/
theorem ambientCarrier_disjoint_initialAttachments
    (C : P.ExteriorFeasibleBlockChoice) :
    Disjoint C.ambientCarrier C.initialAttachments := by
  apply Finset.disjoint_left.mpr
  intro v hvB hvA
  exact Finset.disjoint_left.mp C.ambientCarrier_disjoint_core
    hvB
    (P.working.rooted.core.S_subset_carrier
      (C.initialAttachments_subset_coreS hvA))

/-- The anchor is not one of the collapsed `S`-attachments. -/
theorem b_not_mem_initialAttachments
    (C : P.ExteriorFeasibleBlockChoice) :
    C.b ∉ C.initialAttachments := by
  intro hbA
  exact Finset.disjoint_left.mp
    C.ambientCarrier_disjoint_initialAttachments
    C.b_mem_ambientCarrier hbA

/-- The compression interior and its source boundary are disjoint. -/
theorem compressionInterior_disjoint_initialCompressionBoundary
    (C : P.ExteriorFeasibleBlockChoice) :
    Disjoint C.compressionInterior
      C.initialCompressionBoundary := by
  apply Finset.disjoint_left.mpr
  intro v hvQ hvBoundary
  rw [initialCompressionBoundary,
    Finset.mem_insert] at hvBoundary
  rcases hvBoundary with rfl | hvA
  · exact C.b_not_mem_compressionInterior hvQ
  · exact Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_initialAttachments
      (Finset.mem_of_mem_erase hvQ) hvA

@[simp] theorem b_mem_initialCompressionBoundary
    (C : P.ExteriorFeasibleBlockChoice) :
    C.b ∈ C.initialCompressionBoundary := by
  simp [initialCompressionBoundary]

@[simp] theorem initialCompressionBoundary_erase_b
    (C : P.ExteriorFeasibleBlockChoice) :
    C.initialCompressionBoundary.erase C.b =
      C.initialAttachments := by
  classical
  simp [initialCompressionBoundary,
    C.b_not_mem_initialAttachments]

/-- A concrete attachment witnesses the nontrivial collapsed root. -/
theorem exists_initialAttachment_data
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice) :
    ∃ a ∈ C.initialAttachments,
      ∃ d ∈ C.compressionInterior, G.Adj a d := by
  obtain ⟨a, ha⟩ :=
    C.initialAttachments_nonempty M
  obtain ⟨-, d, hd, had⟩ :=
    C.mem_initialAttachments.mp ha
  exact ⟨a, ha, d, hd, had⟩

/-- The initial compression has the rooted 2-connectivity used recursively. -/
theorem initialCompressionRootedGraph_twoConnected
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice) :
    IsTwoConnected C.initialCompressionRootedGraph := by
  apply BoundaryCompression.rootedGraph_twoConnected_of_nonseparable
    C.ambientCarrier_nonseparable C.b_mem_ambientCarrier
      C.ambientCarrier_disjoint_initialAttachments
  exact C.exists_initialAttachment_data M

/-- The initial compression is strictly smaller in the COY measure. -/
theorem initialCompressionComplexity_lt
    (C : P.ExteriorFeasibleBlockChoice) :
    rootedComplexity C.initialCompressionGraph <
      rootedComplexity G := by
  exact BoundaryCompression.rootedComplexity_lt
    C.compressionInterior_disjoint_core
    P.working.rooted.core.three_le_card_carrier

theorem initialCompressionException_ne_collapsed
    (C : P.ExteriorFeasibleBlockChoice) :
    C.initialCompressionException ≠
      (BoundaryCompression.collapsedRoot :
        BoundaryCompressionVertex C.compressionInterior) := by
  simp only [initialCompressionException]
  split_ifs with hz
  · exact BoundaryCompression.inner_ne_collapsed
      ⟨C.zPrime, hz⟩
  · exact BoundaryCompression.roots_ne.symm

theorem ordinary_inner_ne_initialCompressionException
    (C : P.ExteriorFeasibleBlockChoice) :
    BoundaryCompression.inner
        ⟨C.ordinary, C.ordinary_mem_compressionInterior⟩ ≠
      C.initialCompressionException := by
  simp only [initialCompressionException]
  split_ifs with hz
  · intro h
    apply C.ordinary_ne_zPrime
    exact congrArg
      (fun d : (↑C.compressionInterior : Set V) => d.1)
      (BoundaryCompression.inner_injective
        (Q := C.compressionInterior) h)
  · exact C.ordinary_inner_ne_retained

theorem ne_zPrime_of_inner_ne_initialCompressionException
    (C : P.ExteriorFeasibleBlockChoice)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hne :
      BoundaryCompression.inner ⟨d, hd⟩ ≠
        C.initialCompressionException) :
    d ≠ C.zPrime := by
  simp only [initialCompressionException] at hne
  split_ifs at hne with hz
  · intro hdz
    subst d
    exact hne rfl
  · intro hdz
    subst d
    exact hz hd

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
