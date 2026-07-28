import DeanK5.COYExteriorInitialDegree

/-!
# The general initial-compression recursive family

This is the recursive call used in COY Claim 3.13.  For an augmented
side size `ℓ♯`, the degree ledger loses at most `ℓ♯ - 1`, so minimality
is applied with parameter `q - ℓ♯ + 1`.  Positivity is kept explicit as
the hypothesis `ℓ♯ < q`.
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
Minimality supplies the `q - ℓ♯ + 1` admissible paths across the initial
compression.
-/
theorem exists_initialCompression_recursive_family_of_rankLoss
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (ℓSharp : ℕ)
    (hSharp : 2 ≤ ℓSharp)
    (hrank : P.working.rank ≤ ℓSharp)
    (hSharpLt : ℓSharp < q) :
    Nonempty
      (AdmissiblePathFamily C.initialCompressionGraph
        (BoundaryCompression.collapsedRoot :
          BoundaryCompressionVertex C.compressionInterior)
        BoundaryCompression.retainedRoot
        (q - ℓSharp + 1)) := by
  let q' := q - ℓSharp + 1
  have hq'Pos : 1 ≤ q' := by
    dsimp [q']
    omega
  have hq'Four : q' ≤ 4 := by
    have hq'Le : q' ≤ q := by
      dsimp [q']
      omega
    exact hq'Le.trans M.q_le_four
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
                C.finiteDegree_le_initialCompression_add_rankLoss
                  M ℓSharp hSharp hrank d.2 hdzPrime
              have hledger' :
                  finiteDegree G d.1 ≤
                    finiteDegree C.initialCompressionGraph
                        (BoundaryCompression.inner d) +
                      (ℓSharp - 1) := by
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
