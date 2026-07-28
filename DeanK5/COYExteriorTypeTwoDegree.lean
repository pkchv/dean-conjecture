import DeanK5.COYBoundaryCompressionDegree
import DeanK5.COYExteriorInitialCompression

/-!
# Degree ledger for the type-two exterior compression

In COY Case 2.2, every core neighbour of an ordinary block vertex lies in
`{x} ∪ S`.  Type minimality prevents such a vertex from seeing both `x`
and a vertex of `S`, since those three vertices would form a type-one
core.  Collapsing the `S`-attachments therefore loses at most one degree.
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
An exterior vertex adjacent both to `x` and to a type-two `S`-vertex would
produce a rank-one type-one rooted core, contradicting the type-minimal
choice of the working core.
-/
theorem not_root_adj_and_typeTwo_S_neighbor
    (M : MinimalCounterexample q G x y z)
    (K : TypeTwoCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeTwo K)
    {d : V}
    (hdCore : d ∉ P.working.rooted.core.carrier)
    (hdy : d ≠ y) :
    ¬(G.Adj x d ∧ ∃ s ∈ K.S, G.Adj d s) := by
  rintro ⟨hxd, s, hsS, hds⟩
  have hxs : x ≠ s := by
    intro h
    exact K.root_not_mem_S (h ▸ hsS)
  have hdx : d ≠ x := by
    intro h
    apply hdCore
    rw [h]
    exact P.working.rooted.core.root_mem_carrier
  have hdsNe : d ≠ s := by
    intro h
    apply hdCore
    rw [h, hcore]
    exact (Core.typeTwo K).S_subset_carrier
      (by simpa [Core.S] using hsS)
  have hsCore :
      s ∈ P.working.rooted.core.carrier := by
    rw [hcore]
    exact (Core.typeTwo K).S_subset_carrier
      (by simpa [Core.S] using hsS)
  have hys : y ≠ s := by
    intro h
    apply P.working.rooted.other_root_not_mem
    exact h.symm ▸ hsCore
  let D : TypeOneCore G x 1 := {
    T := {d, s}
    rank_pos := le_rfl
    card_T := by simp [hdsNe]
    root_not_mem := by
      simp [hdx.symm, hxs]
    root_adj := by
      intro v hv
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxd
      · exact K.root_adj_S _ hsS
    clique_T := by
      simpa only [Finset.coe_insert, Finset.coe_singleton,
        SimpleGraph.isClique_pair] using
        (show d ≠ s → G.Adj d s from fun _ => hds)
  }
  let R : RootedCore G x y 1 := {
    core := .typeOne D
    other_root_not_mem := by
      simp [Core.carrier, Core.S, Core.T,
        D, M.roots_ne.symm, hdy.symm, hys]
  }
  have hworkingType :
      P.working.rooted.core.typeNumber = 2 := by
    rw [hcore]
    rfl
  have hchosenType :
      P.orientation.chosen.rooted.core.typeNumber = 2 := by
    rw [← P.working.typeNumber_eq_optimal]
    exact hworkingType
  have hminimal :=
    P.orientation.type_le_core_at_chosen_root R
  rw [hchosenType] at hminimal
  change 2 ≤ 1 at hminimal
  omega

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

/-- The retained block neighbours survive the initial compression injectively. -/
theorem exterior_degree_le_initialCompression_degree
    (C : P.ExteriorFeasibleBlockChoice)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime) :
    finiteDegree P.exteriorGraph
        (C.exteriorVertex
          (Finset.mem_of_mem_erase hd)) ≤
      finiteDegree C.initialCompressionGraph
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
        finiteDegree C.initialCompressionGraph
          (BoundaryCompression.inner ⟨d, hd⟩) := by
    apply BoundaryCompression.selectedNeighbors_card_le_finiteDegree
      (T := C.initialCompressionBoundary) (t := C.b)
      hd
    · intro v hv
      simpa [A] using (Finset.mem_inter.mp hv).1
    · intro v hv
      have hvB : v ∈ C.ambientCarrier :=
        (Finset.mem_inter.mp hv).2
      by_cases hvb : v = C.b
      · subst v
        exact Finset.mem_union_right _
          C.b_mem_initialCompressionBoundary
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hvb, hvB⟩)
    · have hfull :=
        BoundaryCompression.collapse_injective_on_block
          C.b_mem_ambientCarrier
          C.ambientCarrier_disjoint_initialAttachments
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
If an ordinary block vertex has an `S`-neighbour, the collapsed root gives
one further compressed neighbour beyond all retained block neighbours.
-/
theorem exterior_degree_add_one_le_initialCompression_degree_of_S_neighbor
    (C : P.ExteriorFeasibleBlockChoice)
    {d s : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime)
    (hsS : s ∈ P.working.rooted.core.S)
    (hds : G.Adj d s) :
    finiteDegree P.exteriorGraph
          (C.exteriorVertex
            (Finset.mem_of_mem_erase hd)) + 1 ≤
      finiteDegree C.initialCompressionGraph
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
  have hsAttachment : s ∈ C.initialAttachments :=
    C.mem_initialAttachments.mpr
      ⟨hsS, ⟨d, hd, hds.symm⟩⟩
  have hsNotBlock : s ∉ C.ambientCarrier := by
    intro hsB
    exact Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_initialAttachments
      hsB hsAttachment
  have hsNotA : s ∉ A := by
    intro hsA
    exact hsNotBlock (Finset.mem_inter.mp hsA).2
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
  have hsCollapse :
      BoundaryCompression.collapse
          C.compressionInterior C.b s =
        (BoundaryCompression.collapsedRoot :
          BoundaryCompressionVertex C.compressionInterior) := by
    apply
      (BoundaryCompression.collapse_eq_collapsed_iff
        C.compressionInterior C.b s).mpr
    constructor
    · intro hsQ
      exact hsNotBlock (Finset.mem_of_mem_erase hsQ)
    · intro hsb
      exact hsNotBlock (hsb ▸ C.b_mem_ambientCarrier)
  have hinjective :
      Set.InjOn
        (BoundaryCompression.collapse
          C.compressionInterior C.b)
        (↑(insert s A) : Set V) := by
    intro u hu v hv huv
    have hu' : u = s ∨ u ∈ A := by
      simpa using hu
    have hv' : v = s ∨ v ∈ A := by
      simpa using hv
    rcases hu' with rfl | huA
    · rcases hv' with rfl | hvA
      · rfl
      · exfalso
        exact hblockNotCollapsed
          (Finset.mem_inter.mp hvA).2
          (huv.symm.trans hsCollapse)
    · rcases hv' with rfl | hvA
      · exfalso
        exact hblockNotCollapsed
          (Finset.mem_inter.mp huA).2
          (huv.trans hsCollapse)
      · have hfull :=
          BoundaryCompression.collapse_injective_on_block
            C.b_mem_ambientCarrier
            C.ambientCarrier_disjoint_initialAttachments
        apply hfull
        · exact (Finset.mem_inter.mp huA).2
        · exact (Finset.mem_inter.mp hvA).2
        · simpa only [compressionInterior] using huv
  have hselected :
      (insert s A).card ≤
        finiteDegree C.initialCompressionGraph
          (BoundaryCompression.inner ⟨d, hd⟩) := by
    apply BoundaryCompression.selectedNeighbors_card_le_finiteDegree
      (T := C.initialCompressionBoundary) (t := C.b)
      hd
    · intro v hv
      have hv' : v = s ∨ v ∈ A := by
        simpa using hv
      rcases hv' with rfl | hvA
      · exact hds
      · simpa [A] using (Finset.mem_inter.mp hvA).1
    · intro v hv
      have hv' : v = s ∨ v ∈ A := by
        simpa using hv
      rcases hv' with rfl | hvA
      · exact Finset.mem_union_right _
          (by
            simp only [initialCompressionBoundary,
              Finset.mem_insert]
            exact Or.inr hsAttachment)
      · have hvB : v ∈ C.ambientCarrier :=
          (Finset.mem_inter.mp hvA).2
        by_cases hvb : v = C.b
        · subst v
          exact Finset.mem_union_right _
            C.b_mem_initialCompressionBoundary
        · exact Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hvb, hvB⟩)
    · exact hinjective
  rw [C.exterior_degree_eq_block_neighbor_ncard hd hdz,
    ← hAcard]
  rw [Finset.card_insert_of_notMem hsNotA] at hselected
  exact hselected

/--
The source degree ledger for COY Case 2.2: at a nonexceptional interior
vertex, contracting all `S`-attachments loses at most one degree.
-/
theorem finiteDegree_le_initialCompression_add_one_of_typeTwo
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (K : TypeTwoCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeTwo K)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime) :
    finiteDegree G d ≤
      finiteDegree C.initialCompressionGraph
          (BoundaryCompression.inner ⟨d, hd⟩) + 1 := by
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
  have hdegreeSplit :
      finiteDegree G d =
        finiteDegree P.exteriorGraph
            (C.exteriorVertex hdB) +
          (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard := by
    simpa [exteriorVertex] using
      (ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
        P.working.rooted.otherRegion_componentRegion hdOther)
  have hcoreSubset :
      G.neighborSet d ∩
          (↑P.working.rooted.core.carrier : Set V) ⊆
        (↑(insert x K.S) : Set V) := by
    intro v hv
    have hvBoundary :=
      C.core_attachment_mem_initialBoundary M
        hv.2 hd (show G.Adj v d from hv.1.symm)
    have hvRootS :=
      (C.mem_initialBoundary.mp hvBoundary).1
    simpa [hcore, Core.S] using hvRootS
  by_cases hSNeighbor :
      ∃ s ∈ K.S, G.Adj d s
  · obtain ⟨s, hsS, hds⟩ := hSNeighbor
    have hxNotAdj : ¬G.Adj x d := by
      intro hxd
      exact
        not_root_adj_and_typeTwo_S_neighbor
          M K hcore hdNotCarrier hdy
          ⟨hxd, ⟨s, hsS, hds⟩⟩
    have hcoreSubsetS :
        G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V) ⊆
          (↑K.S : Set V) := by
      intro v hv
      have hvRootS := hcoreSubset hv
      have hvClass :
          v = x ∨ v ∈ K.S := by
        simpa using hvRootS
      rcases hvClass with rfl | hvS
      · exact False.elim
          (hxNotAdj hv.1.symm)
      · exact hvS
    have hcoreCard :
        (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard ≤ 2 := by
      calc
        (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard
            ≤ (↑K.S : Set V).ncard :=
          Set.ncard_le_ncard hcoreSubsetS
        _ = K.S.card := Set.ncard_coe_finset K.S
        _ = 2 := K.card_S
    have hsCoreS :
        s ∈ P.working.rooted.core.S := by
      simpa [hcore, Core.S] using hsS
    have hexterior :=
      C.exterior_degree_add_one_le_initialCompression_degree_of_S_neighbor
        hd hdz hsCoreS hds
    omega
  · have hcoreSubsetRoot :
        G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V) ⊆
          ({x} : Set V) := by
      intro v hv
      have hvRootS := hcoreSubset hv
      have hvClass :
          v = x ∨ v ∈ K.S := by
        simpa using hvRootS
      rcases hvClass with rfl | hvS
      · simp
      · exact False.elim
          (hSNeighbor
            ⟨v, hvS,
              (show G.Adj d v from hv.1)⟩)
    have hcoreCard :
        (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard ≤ 1 := by
      calc
        (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard
            ≤ ({x} : Set V).ncard :=
          Set.ncard_le_ncard hcoreSubsetRoot
        _ = 1 := by simp
    have hexterior :=
      C.exterior_degree_le_initialCompression_degree hd hdz
    omega

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
