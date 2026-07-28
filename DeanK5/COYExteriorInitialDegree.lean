import DeanK5.COYExteriorTypeTwoDegree

/-!
# The general initial-compression degree ledger

For COY Claim 3.13, the recursive parameter is reduced by
`ℓ♯ - 1`.  Claim 3.3 bounds the number of core neighbours by
`rank + 1`; Claim 3.12(1) rules out the equality case because equality
would supply a `T`-neighbour.  If an `S`-neighbour exists, one neighbour
survives as the collapsed root.  Otherwise the only possible lost core
neighbour is `x`.
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
At an ordinary block vertex, Claim 3.12(1) improves Claim 3.3 from
`rank + 1` core neighbours to at most `rank`.
-/
theorem coreNeighbor_ncard_le_rank
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime) :
    (G.neighborSet d ∩
      (↑P.working.rooted.core.carrier : Set V)).ncard ≤
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
  have hupper :=
    P.working.coreNeighbor_ncard_le
      hdNotCarrier hdy hdExcluded
  have hnotEq :
      (G.neighborSet d ∩
        (↑P.working.rooted.core.carrier : Set V)).ncard ≠
          P.working.rank + 1 := by
    intro heq
    obtain ⟨t, htT, hdt⟩ :=
      P.working.exists_T_neighbor_of_coreNeighbor_ncard_eq
        hdNotCarrier hdy hdExcluded heq
    have htAttachment : t ∈ C.terminalAttachments := by
      classical
      change
        t ∈ P.working.rooted.core.T.filter
          (fun t =>
            ∃ d ∈ C.compressionInterior, G.Adj t d)
      exact Finset.mem_filter.mpr
        ⟨htT, ⟨d, hd, hdt.symm⟩⟩
    rw [C.terminalAttachments_eq_empty M] at htAttachment
    simp at htAttachment
  omega

/--
The Claim 3.13 degree ledger.  If `rank ≤ ℓ♯` and `ℓ♯ ≥ 2`, every
nonexceptional interior vertex loses at most `ℓ♯ - 1` degree in the
initial compression.
-/
theorem finiteDegree_le_initialCompression_add_rankLoss
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (ℓSharp : ℕ)
    (hSharp : 2 ≤ ℓSharp)
    (hrank : P.working.rank ≤ ℓSharp)
    {d : V} (hd : d ∈ C.compressionInterior)
    (hdz : d ≠ C.zPrime) :
    finiteDegree G d ≤
      finiteDegree C.initialCompressionGraph
          (BoundaryCompression.inner ⟨d, hd⟩) +
        (ℓSharp - 1) := by
  have hdB : d ∈ C.ambientCarrier :=
    Finset.mem_of_mem_erase hd
  have hdOther :
      d ∈ P.working.rooted.otherRegion :=
    C.ambientCarrier_subset_otherRegion hdB
  have hdegreeSplit :
      finiteDegree G d =
        finiteDegree P.exteriorGraph
            (C.exteriorVertex hdB) +
          (G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V)).ncard := by
    simpa [exteriorVertex] using
      (ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
        P.working.rooted.otherRegion_componentRegion hdOther)
  have hcoreCard :=
    C.coreNeighbor_ncard_le_rank M hd hdz
  by_cases hSNeighbor :
      ∃ s ∈ P.working.rooted.core.S, G.Adj d s
  · obtain ⟨s, hsS, hds⟩ := hSNeighbor
    have hexterior :=
      C.exterior_degree_add_one_le_initialCompression_degree_of_S_neighbor
        hd hdz hsS hds
    omega
  · have hcoreSubsetRoot :
        G.neighborSet d ∩
            (↑P.working.rooted.core.carrier : Set V) ⊆
          ({x} : Set V) := by
      intro v hv
      have hvBoundary :=
        C.core_attachment_mem_initialBoundary M
          hv.2 hd (show G.Adj v d from hv.1.symm)
      have hvRootS :=
        (C.mem_initialBoundary.mp hvBoundary).1
      rcases Finset.mem_insert.mp hvRootS with rfl | hvS
      · simp
      · exact False.elim
          (hSNeighbor
            ⟨v, hvS,
              (show G.Adj d v from hv.1)⟩)
    have hcoreOne :
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
