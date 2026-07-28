import DeanK5.COYBoundaryCompressionBlock
import DeanK5.COYCoreCardinality
import DeanK5.COYExteriorFeasibleBlock
import DeanK5.COYModifiedExteriorCut
import DeanK5.Graph.NonseparableEmbedding

/-!
# The Claim 3.12 compression of a feasible exterior block

This file fixes the exact finite sets used in the source contraction.
The block carrier is viewed in the ambient graph, its anchor `b` is retained,
and the working-core `T`-vertices that meet the rest of the block are
collapsed to a new root.
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

/-- The selected exterior block, viewed as an ambient vertex set. -/
def ambientCarrier
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  C.block.carrier.image P.exteriorEmbedding

/-- The vertices of the block other than its retained anchor. -/
def compressionInterior
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  C.ambientCarrier.erase C.b

/--
The working-core `T`-vertices with an edge to the nonanchor part of the
selected block.
-/
noncomputable def terminalAttachments
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  by
    classical
    exact P.working.rooted.core.T.filter fun t =>
      ∃ d ∈ C.compressionInterior, G.Adj t d

/-- The source set collapsed by the boundary compression, together with `b`. -/
noncomputable def compressionBoundary
    (C : P.ExteriorFeasibleBlockChoice) : Finset V :=
  insert C.b C.terminalAttachments

/-- The negated conclusion in Claim 3.12(1). -/
noncomputable def HasTerminalAttachment
    (C : P.ExteriorFeasibleBlockChoice) : Prop :=
  C.terminalAttachments.Nonempty

/-- The smaller graph produced by the source contraction. -/
noncomputable abbrev compressionGraph
    (C : P.ExteriorFeasibleBlockChoice) :
    SimpleGraph
      (BoundaryCompressionVertex C.compressionInterior) :=
  BoundaryCompression.graph G C.compressionInterior
    C.compressionBoundary C.b

/-- The two roots in the recursive call after adjoining the artificial edge. -/
noncomputable abbrev compressionRootedGraph
    (C : P.ExteriorFeasibleBlockChoice) :
    SimpleGraph
      (BoundaryCompressionVertex C.compressionInterior) :=
  BoundaryCompression.rootedGraph G C.compressionInterior
    C.compressionBoundary C.b

/--
The possible second block exception becomes the exceptional vertex of the
recursive rooted instance.  When it is the anchor, the retained root is
reused, which excludes no additional ordinary vertex.
-/
def compressionException
    (C : P.ExteriorFeasibleBlockChoice) :
    BoundaryCompressionVertex C.compressionInterior :=
  if hz : C.zPrime ∈ C.compressionInterior then
    BoundaryCompression.inner ⟨C.zPrime, hz⟩
  else
    BoundaryCompression.retainedRoot

@[simp] theorem mem_ambientCarrier
    (C : P.ExteriorFeasibleBlockChoice) {v : V} :
    v ∈ C.ambientCarrier ↔
      ∃ w ∈ C.block.carrier, P.exteriorEmbedding w = v := by
  simp only [ambientCarrier, Finset.mem_image]

theorem ambientCarrier_subset_otherRegion
    (C : P.ExteriorFeasibleBlockChoice) :
    C.ambientCarrier ⊆ P.working.rooted.otherRegion := by
  intro v hv
  rw [C.mem_ambientCarrier] at hv
  obtain ⟨w, -, hw⟩ := hv
  rw [← hw]
  exact w.2

theorem b_mem_ambientCarrier
    (C : P.ExteriorFeasibleBlockChoice) :
    C.b ∈ C.ambientCarrier := by
  apply C.mem_ambientCarrier.mpr
  exact ⟨C.anchor.b, C.anchor.b_mem, rfl⟩

theorem zPrime_mem_ambientCarrier
    (C : P.ExteriorFeasibleBlockChoice) :
    C.zPrime ∈ C.ambientCarrier := by
  apply C.mem_ambientCarrier.mpr
  exact ⟨C.anchor.zPrime, C.anchor.zPrime_mem, rfl⟩

theorem ordinary_mem_ambientCarrier
    (C : P.ExteriorFeasibleBlockChoice) :
    C.ordinary ∈ C.ambientCarrier := by
  apply C.mem_ambientCarrier.mpr
  exact ⟨C.anchor.ordinary, C.anchor.ordinary_mem, rfl⟩

theorem ordinary_ne_b
    (C : P.ExteriorFeasibleBlockChoice) :
    C.ordinary ≠ C.b := by
  intro h
  apply C.anchor.ordinary_not_special
  have heq : C.anchor.ordinary = C.anchor.b :=
    Subtype.ext h
  exact heq ▸ C.anchor.b_special

theorem ordinary_ne_zPrime
    (C : P.ExteriorFeasibleBlockChoice) :
    C.ordinary ≠ C.zPrime := by
  intro h
  apply C.anchor.ordinary_not_special
  have heq : C.anchor.ordinary = C.anchor.zPrime :=
    Subtype.ext h
  exact heq ▸ C.anchor.zPrime_special

theorem ordinary_mem_compressionInterior
    (C : P.ExteriorFeasibleBlockChoice) :
    C.ordinary ∈ C.compressionInterior := by
  exact Finset.mem_erase.mpr
    ⟨C.ordinary_ne_b, C.ordinary_mem_ambientCarrier⟩

theorem ambientCarrier_disjoint_core
    (C : P.ExteriorFeasibleBlockChoice) :
    Disjoint C.ambientCarrier
      P.working.rooted.core.carrier := by
  apply Finset.disjoint_left.mpr
  intro v hvB hvCore
  exact
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      (C.ambientCarrier_subset_otherRegion hvB) hvCore

theorem compressionInterior_disjoint_core
    (C : P.ExteriorFeasibleBlockChoice) :
    Disjoint C.compressionInterior
      P.working.rooted.core.carrier := by
  apply Finset.disjoint_left.mpr
  intro v hvQ hvCore
  exact Finset.disjoint_left.mp C.ambientCarrier_disjoint_core
    (Finset.mem_of_mem_erase hvQ) hvCore

theorem terminalAttachments_subset_coreT
    (C : P.ExteriorFeasibleBlockChoice) :
    C.terminalAttachments ⊆ P.working.rooted.core.T := by
  classical
  intro t ht
  change
    t ∈ P.working.rooted.core.T.filter
      (fun t => ∃ d ∈ C.compressionInterior, G.Adj t d) at ht
  exact (Finset.mem_filter.mp ht).1

theorem ambientCarrier_disjoint_terminalAttachments
    (C : P.ExteriorFeasibleBlockChoice) :
    Disjoint C.ambientCarrier C.terminalAttachments := by
  apply Finset.disjoint_left.mpr
  intro v hvB hvT
  exact Finset.disjoint_left.mp C.ambientCarrier_disjoint_core
    hvB
    (P.working.rooted.core.T_subset_carrier
      (C.terminalAttachments_subset_coreT hvT))

theorem b_not_mem_terminalAttachments
    (C : P.ExteriorFeasibleBlockChoice) :
    C.b ∉ C.terminalAttachments := by
  intro hbT
  exact Finset.disjoint_left.mp
    C.ambientCarrier_disjoint_terminalAttachments
    C.b_mem_ambientCarrier hbT

theorem compressionInterior_disjoint_compressionBoundary
    (C : P.ExteriorFeasibleBlockChoice) :
    Disjoint C.compressionInterior C.compressionBoundary := by
  apply Finset.disjoint_left.mpr
  intro v hvQ hvT
  rw [compressionBoundary, Finset.mem_insert] at hvT
  rcases hvT with rfl | hvA
  · exact (Finset.mem_erase.mp hvQ).1 rfl
  · exact Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_terminalAttachments
      (Finset.mem_of_mem_erase hvQ) hvA

@[simp] theorem b_mem_compressionBoundary
    (C : P.ExteriorFeasibleBlockChoice) :
    C.b ∈ C.compressionBoundary := by
  simp [compressionBoundary]

theorem b_not_mem_compressionInterior
    (C : P.ExteriorFeasibleBlockChoice) :
    C.b ∉ C.compressionInterior := by
  simp [compressionInterior]

@[simp] theorem compressionBoundary_erase_b
    (C : P.ExteriorFeasibleBlockChoice) :
    C.compressionBoundary.erase C.b =
      C.terminalAttachments := by
  classical
  simp [compressionBoundary, C.b_not_mem_terminalAttachments]

theorem exists_attachment_data
    (C : P.ExteriorFeasibleBlockChoice)
    (hA : C.HasTerminalAttachment) :
    ∃ a ∈ C.terminalAttachments,
      ∃ d ∈ C.ambientCarrier.erase C.b, G.Adj a d := by
  classical
  obtain ⟨a, ha⟩ := hA
  have ha' :
      a ∈ P.working.rooted.core.T.filter
        (fun t => ∃ d ∈ C.compressionInterior, G.Adj t d) := by
    simpa [terminalAttachments] using ha
  exact ⟨a, ha, (Finset.mem_filter.mp ha').2⟩

/-- A nonempty terminal-attachment set is a `T`-attachment in Fact 3. -/
theorem core_hasTAttachment
    (C : P.ExteriorFeasibleBlockChoice)
    (hA : C.HasTerminalAttachment) :
    P.working.rooted.core.HasTAttachment
      P.working.rooted.otherRegion := by
  obtain ⟨t, ht, d, hd, htd⟩ :=
    C.exists_attachment_data hA
  exact
    ⟨d,
      C.ambientCarrier_subset_otherRegion
        (Finset.mem_of_mem_erase hd),
      t, C.terminalAttachments_subset_coreT ht, htd⟩

/-- Fact 3 gives the strict rank bound needed by the recursive call. -/
theorem rank_add_one_lt
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (hA : C.HasTerminalAttachment) :
    P.working.rank + 1 < q :=
  (M.rootedCore_factThree P.working.rooted).2
    (C.core_hasTAttachment hA)

/-- The selected block remains nonseparable when viewed in the ambient graph. -/
theorem ambientCarrier_nonseparable
    (C : P.ExteriorFeasibleBlockChoice) :
    IsNonseparableCarrier G C.ambientCarrier := by
  simpa [ambientCarrier] using
    C.block.image_nonseparable P.exteriorEmbedding

/--
The source contraction has the rooted 2-connectivity required by the
recursive theorem.
-/
theorem compressionRootedGraph_twoConnected
    (C : P.ExteriorFeasibleBlockChoice)
    (hA : C.HasTerminalAttachment) :
    IsTwoConnected C.compressionRootedGraph := by
  apply BoundaryCompression.rootedGraph_twoConnected_of_nonseparable
    C.ambientCarrier_nonseparable C.b_mem_ambientCarrier
      C.ambientCarrier_disjoint_terminalAttachments
  exact C.exists_attachment_data hA

/-- The source contraction is strictly smaller in the COY induction measure. -/
theorem compressionComplexity_lt
    (C : P.ExteriorFeasibleBlockChoice) :
    rootedComplexity C.compressionGraph <
      rootedComplexity G := by
  exact BoundaryCompression.rootedComplexity_lt
    C.compressionInterior_disjoint_core
    P.working.rooted.core.three_le_card_carrier

theorem compressionException_ne_collapsed
    (C : P.ExteriorFeasibleBlockChoice) :
    C.compressionException ≠
      (BoundaryCompression.collapsedRoot :
        BoundaryCompressionVertex C.compressionInterior) := by
  simp only [compressionException]
  split_ifs with hz
  · exact BoundaryCompression.inner_ne_collapsed
      ⟨C.zPrime, hz⟩
  · exact BoundaryCompression.roots_ne.symm

theorem ordinary_inner_ne_collapsed
    (C : P.ExteriorFeasibleBlockChoice) :
    BoundaryCompression.inner
        ⟨C.ordinary, C.ordinary_mem_compressionInterior⟩ ≠
      (BoundaryCompression.collapsedRoot :
        BoundaryCompressionVertex C.compressionInterior) :=
  BoundaryCompression.inner_ne_collapsed _

theorem ordinary_inner_ne_retained
    (C : P.ExteriorFeasibleBlockChoice) :
    BoundaryCompression.inner
        ⟨C.ordinary, C.ordinary_mem_compressionInterior⟩ ≠
      (BoundaryCompression.retainedRoot :
        BoundaryCompressionVertex C.compressionInterior) :=
  BoundaryCompression.inner_ne_retained _

theorem ordinary_inner_ne_exception
    (C : P.ExteriorFeasibleBlockChoice) :
    BoundaryCompression.inner
        ⟨C.ordinary, C.ordinary_mem_compressionInterior⟩ ≠
      C.compressionException := by
  simp only [compressionException]
  split_ifs with hz
  · intro h
    apply C.ordinary_ne_zPrime
    exact congrArg
      (fun d : (↑C.compressionInterior : Set V) => d.1)
      (BoundaryCompression.inner_injective
        (Q := C.compressionInterior) h)
  · exact C.ordinary_inner_ne_retained

theorem ne_zPrime_of_inner_ne_exception
    (C : P.ExteriorFeasibleBlockChoice)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hne :
      BoundaryCompression.inner ⟨d, hd⟩ ≠
        C.compressionException) :
    d ≠ C.zPrime := by
  simp only [compressionException] at hne
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
