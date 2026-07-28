import DeanK5.COYExteriorFeasibleBlockDegree

/-!
# The recursive call inside the feasible-block compression

Under a working-core `T`-attachment, the Claim 3.12 contraction is a
strictly smaller rooted instance with parameter `q - rank`.  Its exceptional
vertex is precisely the possible second special block vertex.
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
Minimality supplies `q - rank` admissible paths across the compressed
feasible block.
-/
theorem exists_compression_recursive_family
    (M : MinimalCounterexample q G x y z)
    (C : P.ExteriorFeasibleBlockChoice)
    (hA : C.HasTerminalAttachment) :
    Nonempty
      (AdmissiblePathFamily C.compressionGraph
        (BoundaryCompression.collapsedRoot :
          BoundaryCompressionVertex C.compressionInterior)
        BoundaryCompression.retainedRoot
        (q - P.working.rank)) := by
  let q' := q - P.working.rank
  have hrankStrong :
      P.working.rank + 1 < q :=
    C.rank_add_one_lt M hA
  have hq'Pos : 1 ≤ q' := by
    dsimp [q']
    omega
  have hq'Four : q' ≤ 4 := by
    have hsub : q - P.working.rank ≤ q :=
      Nat.sub_le q P.working.rank
    exact hsub.trans M.q_le_four
  let I :
      RootedInstance q' C.compressionGraph
        (BoundaryCompression.collapsedRoot :
          BoundaryCompressionVertex C.compressionInterior)
        BoundaryCompression.retainedRoot
        C.compressionException := {
    q_pos := hq'Pos
    q_le_four := hq'Four
    roots_ne := BoundaryCompression.roots_ne
    rooted_two_connected :=
      C.compressionRootedGraph_twoConnected hA
    ordinary_nonempty :=
      ⟨BoundaryCompression.inner
          ⟨C.ordinary, C.ordinary_mem_compressionInterior⟩,
        C.ordinary_inner_ne_collapsed,
        C.ordinary_inner_ne_retained,
        C.ordinary_inner_ne_exception⟩
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
                C.ne_zPrime_of_inner_ne_exception
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
                C.finiteDegree_le_compression_add_rank
                  d.2 hdzPrime
              have hledger' :
                  finiteDegree G d.1 ≤
                    finiteDegree C.compressionGraph
                        (BoundaryCompression.inner d) +
                      P.working.rank := by
                convert hledger using 1
              change q' + 1 ≤
                finiteDegree C.compressionGraph
                  (BoundaryCompression.inner d)
              dsimp [q']
              omega
  }
  exact M.smaller_solvable I C.compressionComplexity_lt

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
