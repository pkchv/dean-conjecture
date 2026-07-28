import DeanK5.COYFactThree

/-!
# The exterior component of a rooted COY core

For a core with respect to an ordered root pair, the second root lies outside
the core carrier.  This file names its deletion component and packages the
component-region facts used throughout the proof of COY Theorem 3.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace RootedCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y : V} {ℓ : ℕ}

/-- The component of `G - V(R)` containing the second root. -/
noncomputable def otherComponent
    (R : RootedCore G x y ℓ) :
    (deleteVertices G R.core.carrier).ConnectedComponent :=
  (deleteVertices G R.core.carrier).connectedComponentMk
    ⟨y, R.other_root_not_mem⟩

/-- The ambient vertices of the component containing the second root. -/
noncomputable def otherRegion
    (R : RootedCore G x y ℓ) : Finset V :=
  componentVertices G R.core.carrier R.otherComponent

/-- The second root belongs to its named exterior region. -/
theorem other_root_mem_otherRegion
    (R : RootedCore G x y ℓ) :
    y ∈ R.otherRegion := by
  apply (mem_componentVertices_iff
    G R.core.carrier R.otherComponent y).2
  exact ⟨R.other_root_not_mem,
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

/-- The named exterior region is a connected component region. -/
theorem otherRegion_componentRegion
    (R : RootedCore G x y ℓ) :
    ComponentRegion G R.core.carrier R.otherRegion :=
  componentRegion_componentVertices
    G R.core.carrier R.otherComponent

/--
Fact 3 specialized to the deletion component containing the second root.
-/
theorem factThree_on_otherRegion
    (R : RootedCore G x y ℓ)
    {q : ℕ}
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ < q ∧
      (R.core.HasTAttachment R.otherRegion →
        ℓ + 1 < q) :=
  R.factThree
    R.otherRegion_componentRegion
    R.other_root_mem_otherRegion
    hconn hqOne hqFour hno

end RootedCore

end COY

end DeanK5
