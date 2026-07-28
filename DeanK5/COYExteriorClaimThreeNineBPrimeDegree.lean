import DeanK5.COYExteriorClaimThreeNineBPrimeBalanced
import DeanK5.COYExteriorClaimThreeNineBPrimeLedger
import DeanK5.COYExteriorClaimThreeNineBPrimeTerminal

/-!
# COY Claim 3.9(4)

This file combines the two modified-core exclusions with the final degree
ledger.  In the natural branch the vertex excluded by Claim 3.3 is simply
the other root.  In the balanced modification, exterior degree at most two
rules out the removed vertex by three explicit exterior neighbours.  In the
terminal modification, the larger-core construction rules it out by
maximality.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

namespace ExteriorZEndBlock

/--
Under the negation of Claim 3.9(4), the second exterior neighbour is not
the special vertex omitted from Claim 3.3.
-/
theorem bPrime_ne_excludedVertex_of_exterior_degree_le_two
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hPrimeY : E.bPrime ≠ y)
    (hdegree :
      finiteDegree P.exteriorGraph E.certificate.bPrime ≤ 2) :
    E.bPrime ≠ P.working.excludedVertex := by
  cases hworking : P.working with
  | natural hnot =>
      change E.bPrime ≠ y
      exact hPrimeY
  | modified T K =>
      cases K with
      | balanced s₀ hs₀ hbalance =>
          change E.bPrime ≠ T.t₀
          exact
            E.bPrime_ne_t₀_of_balanced
              T s₀ hs₀ hbalance hworking hdegree
      | terminal hlarge =>
          change E.bPrime ≠ T.t₀
          exact
            E.bPrime_ne_t₀_of_terminal
              M T hlarge hworking

/--
COY Claim 3.9(4): unless `b'_z` is the other root, its degree in the
selected exterior component is at least three.
-/
theorem three_le_exterior_degree_bPrime
    (M : MinimalCounterexample q G x y z)
    (E : P.ExteriorZEndBlock)
    (hPrimeY : E.bPrime ≠ y) :
    3 ≤ finiteDegree P.exteriorGraph E.certificate.bPrime := by
  by_contra hnot
  have hdegree :
      finiteDegree P.exteriorGraph E.certificate.bPrime ≤ 2 := by
    omega
  have hExcluded :=
    E.bPrime_ne_excludedVertex_of_exterior_degree_le_two
      M hPrimeY hdegree
  have hthree :=
    E.three_le_exterior_degree_bPrime_of_ne_excluded
      M hPrimeY hExcluded
  omega

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
