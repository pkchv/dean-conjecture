import DeanK5.COYBoundaryCompressionDegree
import DeanK5.COYExteriorFeasibleBlockOrdinary

/-!
# Degree ledger for the feasible-block compression

This is the local degree calculation in COY Claim 3.12(1).  At an
ordinary vertex of the selected block, every exterior neighbour remains
inside the block.  The block neighbours therefore survive the compression
injectively.  Claim 3.3 leaves at most `rank + 1` core neighbours; in its
equality case one of them lies in `T` and supplies the additional collapsed
root neighbour.
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
All neighbours of an ordinary block vertex in the induced exterior are
exactly its ambient neighbours that lie in the selected block.
-/
private theorem exterior_degree_eq_block_neighbor_ncard
    (C : P.ExteriorFeasibleBlockChoice)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime) :
    finiteDegree P.exteriorGraph
        (C.exteriorVertex
          (Finset.mem_of_mem_erase hd)) =
      (G.neighborSet d ∩
        (↑C.ambientCarrier : Set V)).ncard := by
  let dE :=
    C.exteriorVertex (Finset.mem_of_mem_erase hd)
  have hdb : d ≠ C.b :=
    (Finset.mem_erase.mp hd).1
  have himage :
      Subtype.val '' P.exteriorGraph.neighborSet dE =
        G.neighborSet d ∩
          (↑C.ambientCarrier : Set V) := by
    ext v
    constructor
    · rintro ⟨w, hdw, rfl⟩
      have hwBlock :
          w ∈ C.block.carrier :=
        C.exterior_neighbor_mem_block
          (Finset.mem_of_mem_erase hd) hdb hdz hdw
      constructor
      · exact hdw
      · exact C.mem_ambientCarrier.mpr
          ⟨w, hwBlock, rfl⟩
    · rintro ⟨hdv, hvBlock⟩
      let vE : P.ExteriorVertex :=
        ⟨v, C.ambientCarrier_subset_otherRegion hvBlock⟩
      have hdvE : P.exteriorGraph.Adj dE vE :=
        hdv
      exact ⟨vE, hdvE, rfl⟩
  unfold finiteDegree
  calc
    (P.exteriorGraph.neighborSet dE).ncard =
        (Subtype.val ''
          P.exteriorGraph.neighborSet dE).ncard := by
      rw [Set.ncard_image_of_injective _ Subtype.val_injective]
    _ =
        (G.neighborSet d ∩
          (↑C.ambientCarrier : Set V)).ncard := by
      rw [himage]

/--
The block neighbours of an ordinary compression vertex survive as
distinct neighbours after the boundary collapse.
-/
private theorem exterior_degree_le_compression_degree
    (C : P.ExteriorFeasibleBlockChoice)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime) :
    finiteDegree P.exteriorGraph
        (C.exteriorVertex
          (Finset.mem_of_mem_erase hd)) ≤
      finiteDegree C.compressionGraph
        (BoundaryCompression.inner ⟨d, hd⟩) := by
  letI : Fintype (G.neighborSet d) :=
    Fintype.ofFinite _
  let A := G.neighborFinset d ∩ C.ambientCarrier
  have hAcard :
      A.card =
        (G.neighborSet d ∩
          (↑C.ambientCarrier : Set V)).ncard := by
    calc
      A.card = (↑A : Set V).ncard := by simp
      _ =
          (G.neighborSet d ∩
            (↑C.ambientCarrier : Set V)).ncard := by
        congr 1
        ext v
        simp [A]
  have hselected :
      A.card ≤
        finiteDegree C.compressionGraph
          (BoundaryCompression.inner ⟨d, hd⟩) := by
    apply BoundaryCompression.selectedNeighbors_card_le_finiteDegree
      (T := C.compressionBoundary) (t := C.b)
      hd
    · intro v hv
      simpa [A] using (Finset.mem_inter.mp hv).1
    · intro v hv
      have hvB : v ∈ C.ambientCarrier :=
        (Finset.mem_inter.mp hv).2
      by_cases hvb : v = C.b
      · subst v
        exact Finset.mem_union_right _
          C.b_mem_compressionBoundary
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hvb, hvB⟩)
    · have hfull :=
        BoundaryCompression.collapse_injective_on_block
          C.b_mem_ambientCarrier
          C.ambientCarrier_disjoint_terminalAttachments
      intro u hu v hv huv
      change u ∈ A at hu
      change v ∈ A at hv
      apply hfull
      · exact (Finset.mem_inter.mp hu).2
      · exact (Finset.mem_inter.mp hv).2
      · simpa only [compressionInterior] using huv
  rw [C.exterior_degree_eq_block_neighbor_ncard hd hdz,
    ← hAcard]
  exact hselected

/--
If an ordinary block vertex has a `T`-neighbour, that neighbour is represented
by the collapsed root, in addition to all of the injectively retained block
neighbours.
-/
private theorem exterior_degree_add_one_le_compression_degree_of_T_neighbor
    (C : P.ExteriorFeasibleBlockChoice)
    {d t : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime)
    (htT : t ∈ P.working.rooted.core.T)
    (hdt : G.Adj d t) :
    finiteDegree P.exteriorGraph
          (C.exteriorVertex
            (Finset.mem_of_mem_erase hd)) + 1 ≤
      finiteDegree C.compressionGraph
        (BoundaryCompression.inner ⟨d, hd⟩) := by
  letI : Fintype (G.neighborSet d) :=
    Fintype.ofFinite _
  let A := G.neighborFinset d ∩ C.ambientCarrier
  have hAcard :
      A.card =
        (G.neighborSet d ∩
          (↑C.ambientCarrier : Set V)).ncard := by
    calc
      A.card = (↑A : Set V).ncard := by simp
      _ =
          (G.neighborSet d ∩
            (↑C.ambientCarrier : Set V)).ncard := by
        congr 1
        ext v
        simp [A]
  have htAttachment : t ∈ C.terminalAttachments := by
    classical
    change
      t ∈ P.working.rooted.core.T.filter
        (fun t => ∃ d ∈ C.compressionInterior, G.Adj t d)
    exact Finset.mem_filter.mpr
      ⟨htT, ⟨d, hd, hdt.symm⟩⟩
  have htNotBlock : t ∉ C.ambientCarrier := by
    intro htB
    exact Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_terminalAttachments
      htB htAttachment
  have htNotA : t ∉ A := by
    intro htA
    exact htNotBlock (Finset.mem_inter.mp htA).2
  have hblockNotCollapsed :
      ∀ ⦃v : V⦄, v ∈ C.ambientCarrier →
        BoundaryCompression.collapse
            C.compressionInterior C.b v ≠
          (BoundaryCompression.collapsedRoot :
            BoundaryCompressionVertex C.compressionInterior) := by
    intro v hvB hcollapse
    obtain ⟨hvNotQ, hvNotB⟩ :=
      (BoundaryCompression.collapse_eq_collapsed_iff
        C.compressionInterior C.b v).mp hcollapse
    exact hvNotQ
      (Finset.mem_erase.mpr ⟨hvNotB, hvB⟩)
  have htCollapse :
      BoundaryCompression.collapse
          C.compressionInterior C.b t =
        (BoundaryCompression.collapsedRoot :
          BoundaryCompressionVertex C.compressionInterior) := by
    apply
      (BoundaryCompression.collapse_eq_collapsed_iff
        C.compressionInterior C.b t).mpr
    constructor
    · intro htQ
      exact htNotBlock (Finset.mem_of_mem_erase htQ)
    · intro htb
      exact htNotBlock (htb ▸ C.b_mem_ambientCarrier)
  have hinjective :
      Set.InjOn
        (BoundaryCompression.collapse
          C.compressionInterior C.b)
        (↑(insert t A) : Set V) := by
    intro u hu v hv huv
    have hu' : u = t ∨ u ∈ A := by
      simpa using hu
    have hv' : v = t ∨ v ∈ A := by
      simpa using hv
    rcases hu' with rfl | huA
    · rcases hv' with rfl | hvA
      · rfl
      · exfalso
        exact hblockNotCollapsed
          (Finset.mem_inter.mp hvA).2
          (huv.symm.trans htCollapse)
    · rcases hv' with rfl | hvA
      · exfalso
        exact hblockNotCollapsed
          (Finset.mem_inter.mp huA).2
          (huv.trans htCollapse)
      · have hfull :=
          BoundaryCompression.collapse_injective_on_block
            C.b_mem_ambientCarrier
            C.ambientCarrier_disjoint_terminalAttachments
        apply hfull
        · exact (Finset.mem_inter.mp huA).2
        · exact (Finset.mem_inter.mp hvA).2
        · simpa only [compressionInterior] using huv
  have hselected :
      (insert t A).card ≤
        finiteDegree C.compressionGraph
          (BoundaryCompression.inner ⟨d, hd⟩) := by
    apply BoundaryCompression.selectedNeighbors_card_le_finiteDegree
      (T := C.compressionBoundary) (t := C.b)
      hd
    · intro v hv
      have hv' : v = t ∨ v ∈ A := by
        simpa using hv
      rcases hv' with rfl | hvA
      · exact hdt
      · simpa [A] using (Finset.mem_inter.mp hvA).1
    · intro v hv
      have hv' : v = t ∨ v ∈ A := by
        simpa using hv
      rcases hv' with rfl | hvA
      · exact Finset.mem_union_right _
          (by
            simp only [compressionBoundary,
              Finset.mem_insert]
            exact Or.inr htAttachment)
      · have hvB : v ∈ C.ambientCarrier :=
          (Finset.mem_inter.mp hvA).2
        by_cases hvb : v = C.b
        · subst v
          exact Finset.mem_union_right _
            C.b_mem_compressionBoundary
        · exact Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hvb, hvB⟩)
    · exact hinjective
  rw [C.exterior_degree_eq_block_neighbor_ncard hd hdz,
    ← hAcard]
  rw [Finset.card_insert_of_notMem htNotA] at hselected
  exact hselected

/--
The source degree ledger for Claim 3.12(1): every nonexceptional vertex in
the compressed block loses at most the working-core rank.
-/
theorem finiteDegree_le_compression_add_rank
    (C : P.ExteriorFeasibleBlockChoice)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime) :
    finiteDegree G d ≤
      finiteDegree C.compressionGraph
          (BoundaryCompression.inner ⟨d, hd⟩) +
        P.working.rank := by
  have hdB : d ∈ C.ambientCarrier :=
    Finset.mem_of_mem_erase hd
  have hdb : d ≠ C.b :=
    (Finset.mem_erase.mp hd).1
  have hdOther :
      d ∈ P.working.rooted.otherRegion :=
    C.ambientCarrier_subset_otherRegion hdB
  have hdNotCarrier :
      d ∉ P.working.rooted.core.carrier :=
    P.working.rooted.otherRegion_componentRegion.not_mem_separator
      hdOther
  have hdy : d ≠ y :=
    C.ordinary_block_vertex_ne_y hdB hdb hdz
  have hdExcluded : d ≠ P.working.excludedVertex :=
    C.ordinary_block_vertex_ne_excluded hdB hdb hdz
  have hcoreUpper :=
    P.working.coreNeighbor_ncard_le
      hdNotCarrier hdy hdExcluded
  have hdegreeSplit :
      finiteDegree G d =
        finiteDegree P.exteriorGraph
            (C.exteriorVertex hdB) +
          (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard := by
    simpa [exteriorVertex] using
      (ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
        P.working.rooted.otherRegion_componentRegion hdOther)
  by_cases hcoreSmall :
      (G.neighborSet d ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard ≤
          P.working.rank
  · have hexterior :=
      C.exterior_degree_le_compression_degree hd hdz
    omega
  · have hcoreEq :
        (G.neighborSet d ∩
          (↑P.working.rooted.core.carrier : Set V)).ncard =
            P.working.rank + 1 := by
      omega
    obtain ⟨t, htT, hdt⟩ :=
      P.working.exists_T_neighbor_of_coreNeighbor_ncard_eq
        hdNotCarrier hdy hdExcluded hcoreEq
    have hexterior :=
      C.exterior_degree_add_one_le_compression_degree_of_T_neighbor
        hd hdz htT hdt
    omega

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
