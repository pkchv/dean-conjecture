import DeanK5.COYCoreAdapters
import DeanK5.COYSemiPathOperations

/-!
# The prefix family in COY Claim 3.16

For a type-3 core, Fact 2 supplies two semi-admissible paths from the
root to any selected vertex of `T`.  Appending a nontrivial connector
from that vertex into the exterior raises the first length to at least
two, producing the admissible prefix family used in Claim 3.16.

The second constructor below discharges the simplicity condition from
the geometric statement that the connector, after leaving its initial
vertex, stays outside the core carrier.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY.TypeThreeCore

variable [DecidableEq V]
  {G : SimpleGraph V} {x target left : V} {ℓ : ℕ}

/--
Append a fixed nontrivial connector to the two type-3 core paths ending
at `target ∈ T`.

The capacity hypothesis is precisely the bound needed to select two
members of the bounded type-3 catalogue.
-/
noncomputable def claimThreeSixteenPrefixFamily
    (C : TypeThreeCore G x ℓ)
    (htarget : target ∈ C.T)
    (connector : SimplePath G target left)
    (hconnector : 1 ≤ connector.length)
    (hcapacity : 2 ≤ ℓ + 1)
    (hdisjoint : ∀ i : Fin 2,
      ((C.semiAdmissiblePathsToT target htarget 2
        (by omega) (by omega) hcapacity).path i).walk.support.Disjoint
          connector.walk.support.tail) :
    AdmissiblePathFamily G x left 2 :=
  (C.semiAdmissiblePathsToT target htarget 2
      (by omega) (by omega) hcapacity).appendFixedToAdmissible
    connector hconnector hdisjoint

/--
The fixed-connector description of every path in the Claim 3.16 prefix
family.
-/
@[simp] theorem claimThreeSixteenPrefixFamily_path
    (C : TypeThreeCore G x ℓ)
    (htarget : target ∈ C.T)
    (connector : SimplePath G target left)
    (hconnector : 1 ≤ connector.length)
    (hcapacity : 2 ≤ ℓ + 1)
    (hdisjoint : ∀ i : Fin 2,
      ((C.semiAdmissiblePathsToT target htarget 2
        (by omega) (by omega) hcapacity).path i).walk.support.Disjoint
          connector.walk.support.tail)
    (i : Fin 2) :
    (C.claimThreeSixteenPrefixFamily htarget connector hconnector
      hcapacity hdisjoint).path i =
      ((C.semiAdmissiblePathsToT target htarget 2
        (by omega) (by omega) hcapacity).path i).appendDisjoint
          connector (hdisjoint i) :=
  rfl

/--
The core paths and the connector are disjoint when every vertex of the
connector after `target` lies outside the type-3 core carrier.
-/
theorem claimThreeSixteenPrefix_disjoint_of_tail_outside
    (C : TypeThreeCore G x ℓ)
    (htarget : target ∈ C.T)
    (connector : SimplePath G target left)
    (hcapacity : 2 ≤ ℓ + 1)
    (htailOutside : ∀ v ∈ connector.walk.support.tail,
      v ∉ insert x (C.S ∪ C.T))
    (i : Fin 2) :
    ((C.semiAdmissiblePathsToT target htarget 2
      (by omega) (by omega) hcapacity).path i).walk.support.Disjoint
        connector.walk.support.tail := by
  apply List.disjoint_left.mpr
  intro v hvCore hvConnector
  exact htailOutside v hvConnector
    (C.semiAdmissiblePathsToT_support target htarget 2
      (by omega) (by omega) hcapacity i v hvCore)

/--
Construct the two admissible Claim 3.16 prefix paths directly from the
geometric fact that the connector tail lies outside the core carrier.
-/
noncomputable def claimThreeSixteenPrefixFamilyOfTailOutside
    (C : TypeThreeCore G x ℓ)
    (htarget : target ∈ C.T)
    (connector : SimplePath G target left)
    (hconnector : 1 ≤ connector.length)
    (hcapacity : 2 ≤ ℓ + 1)
    (htailOutside : ∀ v ∈ connector.walk.support.tail,
      v ∉ insert x (C.S ∪ C.T)) :
    AdmissiblePathFamily G x left 2 :=
  C.claimThreeSixteenPrefixFamily htarget connector hconnector hcapacity
    (C.claimThreeSixteenPrefix_disjoint_of_tail_outside
      htarget connector hcapacity htailOutside)

/--
The automatic constructor uses the same fixed-connector paths as the
explicit-disjointness constructor.
-/
@[simp] theorem claimThreeSixteenPrefixFamilyOfTailOutside_path
    (C : TypeThreeCore G x ℓ)
    (htarget : target ∈ C.T)
    (connector : SimplePath G target left)
    (hconnector : 1 ≤ connector.length)
    (hcapacity : 2 ≤ ℓ + 1)
    (htailOutside : ∀ v ∈ connector.walk.support.tail,
      v ∉ insert x (C.S ∪ C.T))
    (i : Fin 2) :
    (C.claimThreeSixteenPrefixFamilyOfTailOutside
      htarget connector hconnector hcapacity htailOutside).path i =
      ((C.semiAdmissiblePathsToT target htarget 2
        (by omega) (by omega) hcapacity).path i).appendDisjoint
          connector
          (C.claimThreeSixteenPrefix_disjoint_of_tail_outside
            htarget connector hcapacity htailOutside i) :=
  rfl

end COY.TypeThreeCore

end DeanK5
