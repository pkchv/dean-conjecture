import DeanK5.COYCoreExterior
import DeanK5.COYProtectedIndependence

/-!
# Initial cores in a COY minimal counterexample

After COY Claim 3.2, the underlying graph is 2-connected and the protected
vertices are pairwise nonadjacent.  Hence each root has degree at least two
and supports a source core with respect to the ordered root pair.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace MinimalCounterexample

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}

/-- The left root has degree at least two in the underlying graph. -/
theorem two_le_left_root_degree
    (M : MinimalCounterexample q G x y z) :
    2 ≤ finiteDegree G x :=
  ClassicalGraphTheory.degree_at_least_connectivity
    G 2 M.underlying_two_connected x

/-- The right root has degree at least two in the underlying graph. -/
theorem two_le_right_root_degree
    (M : MinimalCounterexample q G x y z) :
    2 ≤ finiteDegree G y :=
  M.swapRoots.two_le_left_root_degree

/-- A source core exists with respect to the ordered pair `(x,y)`. -/
theorem exists_left_rootedCore
    (M : MinimalCounterexample q G x y z) :
    ∃ ℓ : ℕ, Nonempty (RootedCore G x y ℓ) := by
  rcases exists_typeOne_or_typeThree_rootedCore
      G x y M.roots_ne M.roots_not_adj
      M.two_le_left_root_degree with
    ⟨C, -, -⟩ | ⟨C, -, -⟩
  · exact ⟨1, ⟨C⟩⟩
  · exact ⟨0, ⟨C⟩⟩

/-- A source core exists with respect to the ordered pair `(y,x)`. -/
theorem exists_right_rootedCore
    (M : MinimalCounterexample q G x y z) :
    ∃ ℓ : ℕ, Nonempty (RootedCore G y x ℓ) :=
  M.swapRoots.exists_left_rootedCore

/--
Every selected left-root core satisfies the bounded Fact 3 inequalities on
the component containing the right root.
-/
theorem rootedCore_factThree
    (M : MinimalCounterexample q G x y z)
    {ℓ : ℕ} (R : RootedCore G x y ℓ) :
    ℓ < q ∧
      (R.core.HasTAttachment R.otherRegion →
        ℓ + 1 < q) :=
  R.factThree_on_otherRegion
    M.rooted_two_connected M.q_pos M.q_le_four
    (by
      simpa [RootedInstance.Solvable] using M.no_paths)

end MinimalCounterexample

end COY

end DeanK5
