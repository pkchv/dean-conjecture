import DeanK5.BoundaryLiftingCore
import DeanK5.RootLifting

/-!
# Boundary-root lifting (paper Section 6.1)

This module applies the rooted path theorem and then invokes the
theorem-independent boundary replacement developed in
`BoundaryLiftingCore`.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {U : Type u} {V : Type v}

/--
Lemma 6.2, artificial-root clause.  The graph-theoretic hypotheses and both
degree bounds are passed unchanged to `root_lifting`; the resulting family
is then lifted through the explicit `L(u),R(v)` boundary data above.
-/
theorem boundary_root_lifting_artificial_detailed
    [Fintype U] [DecidableEq U]
    (q : ℕ) (H : SimpleGraph U) (D Z : Finset U)
    (α β : U)
    (hqTwo : 2 ≤ q) (hqFour : q ≤ 4)
    (hαβ : α ≠ β)
    (hnotadj : ¬ H.Adj α β)
    (hconn : IsTwoConnected (H ⊔ edge α β))
    (hZD : Z ⊆ D)
    (hαZ : α ∉ Z) (hβZ : β ∉ Z)
    (hdeg : ∀ v, v ≠ α → v ≠ β → v ∉ Z →
      q + 1 ≤ finiteDegree H v)
    (hdegZ : ∀ z ∈ Z, q ≤ finiteDegree H z)
    (horder_one : Z.card = 1 → 4 ≤ Fintype.card U)
    {B : SimpleGraph V} {c : V}
    (A : BoundaryRootAmbient H α β Z B c) :
    DetailedBoundaryRootLiftResult H α β Z B c A q := by
  have lifted : RootLiftResult H Z α β q :=
    root_lifting q H D Z α β hqTwo hqFour hαβ hnotadj hconn
      hZD hαZ hβZ hdeg hdegZ horder_one
  obtain ⟨F, -⟩ := lifted
  exact ⟨F, A.lift_family_with_membership F⟩

end DeanK5
