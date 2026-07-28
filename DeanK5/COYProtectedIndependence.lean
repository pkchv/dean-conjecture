import DeanK5.COYEdgeSwapLobe
import DeanK5.COYEdgeSwapRecursive

/-!
# Independence of the protected vertices

This file completes COY Claim 3.2(2).  In a minimal counterexample, neither
root can be adjacent to the exceptional vertex.  Together with the previously
proved root nonedge, the three protected vertices are pairwise nonadjacent.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The left root is not adjacent to the exceptional vertex. -/
theorem left_root_not_adj_exception
    (M : MinimalCounterexample q G x y z) :
    ¬G.Adj x z := by
  intro hxz
  apply M.contradiction_of_edge_swap_lobe
    (M.edgeSwapLobe hxz)
  · exact M.edgeSwapLobe_other_root_mem hxz
  · simpa using M.edgeSwapLobe_three_le_carrier_card hxz
  · obtain ⟨w, hwCarrier, hwx, hwy, -, hwCut⟩ :=
      M.edgeSwapLobe_exists_ordinary_carrier hxz
    exact ⟨w, hwCarrier, hwx, hwy, hwCut⟩

/-- The right root is not adjacent to the exceptional vertex. -/
theorem right_root_not_adj_exception
    (M : MinimalCounterexample q G x y z) :
    ¬G.Adj y z :=
  M.swapRoots.left_root_not_adj_exception

/--
COY Claim 3.2(2): the two roots and the exceptional vertex are pairwise
nonadjacent.
-/
theorem protected_vertices_pairwise_nonadjacent
    (M : MinimalCounterexample q G x y z) :
    ¬G.Adj x y ∧ ¬G.Adj x z ∧ ¬G.Adj y z :=
  ⟨M.roots_not_adj, M.left_root_not_adj_exception,
    M.right_root_not_adj_exception⟩

end MinimalCounterexample

end COY

end DeanK5
