import DeanK5.COYExteriorTypeTwoDegree

/-!
# The recursive type-two exterior family

The initial-side compression in COY Case 2.2 loses at most one degree.
Minimality therefore supplies `q - 1` admissible paths across the selected
block.
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

/-- Minimality supplies the `q - 1` paths used in COY Case 2.2. -/
theorem exists_typeTwo_initialCompression_recursive_family
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (K : TypeTwoCore G x P.working.rank)
    (hcore : P.working.rooted.core = .typeTwo K) :
    Nonempty
      (AdmissiblePathFamily C.initialCompressionGraph
        (BoundaryCompression.collapsedRoot :
          BoundaryCompressionVertex C.compressionInterior)
        BoundaryCompression.retainedRoot
        (q - 1)) := by
  let q' := q - 1
  have hq'Pos : 1 ≤ q' := by
    have hqTwo := M.two_le_q
    dsimp [q']
    omega
  have hq'Four : q' ≤ 4 := by
    have hsub : q - 1 ≤ q :=
      Nat.sub_le q 1
    exact hsub.trans M.q_le_four
  let I :
      RootedInstance q' C.initialCompressionGraph
        (BoundaryCompression.collapsedRoot :
          BoundaryCompressionVertex C.compressionInterior)
        BoundaryCompression.retainedRoot
        C.initialCompressionException := {
    q_pos := hq'Pos
    q_le_four := hq'Four
    roots_ne := BoundaryCompression.roots_ne
    rooted_two_connected :=
      C.initialCompressionRootedGraph_twoConnected M
    ordinary_nonempty :=
      ⟨BoundaryCompression.inner
          ⟨C.ordinary, C.ordinary_mem_compressionInterior⟩,
        C.ordinary_inner_ne_collapsed,
        C.ordinary_inner_ne_retained,
        C.ordinary_inner_ne_initialCompressionException⟩
    degree_lower := by
      intro w hwCollapsed hwRetained hwException
      cases w with
      | none =>
          exact False.elim (hwCollapsed rfl)
      | some w =>
          cases w with
          | none =>
              exact False.elim (hwRetained rfl)
          | some d =>
              have hdzPrime :
                  d.1 ≠ C.zPrime :=
                C.ne_zPrime_of_inner_ne_initialCompressionException
                  d.2 hwException
              have hdB :
                  d.1 ∈ C.ambientCarrier :=
                Finset.mem_of_mem_erase d.2
              have hdb :
                  d.1 ≠ C.b :=
                (Finset.mem_erase.mp d.2).1
              have hdx : d.1 ≠ x := by
                intro hdx
                have hdCore :
                    d.1 ∈
                      P.working.rooted.core.carrier := by
                  rw [hdx]
                  exact
                    P.working.rooted.core.root_mem_carrier
                exact
                  Finset.disjoint_left.mp
                    C.ambientCarrier_disjoint_core
                    hdB hdCore
              have hdy : d.1 ≠ y :=
                C.ordinary_block_vertex_ne_y
                  hdB hdb hdzPrime
              have hdz : d.1 ≠ z :=
                C.ordinary_block_vertex_ne_z
                  hdB hdb hdzPrime
              have hambient :=
                M.degree_lower d.1 hdx hdy hdz
              have hledger :=
                C.finiteDegree_le_initialCompression_add_one_of_typeTwo
                  M K hcore d.2 hdzPrime
              have hledger' :
                  finiteDegree G d.1 ≤
                    finiteDegree C.initialCompressionGraph
                        (BoundaryCompression.inner d) + 1 := by
                convert hledger using 1
              change q' + 1 ≤
                finiteDegree C.initialCompressionGraph
                  (BoundaryCompression.inner d)
              dsimp [q']
              omega
  }
  exact M.smaller_solvable I C.initialCompressionComplexity_lt

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
