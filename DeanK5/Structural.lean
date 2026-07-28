import DeanK5.BGLPConnectivityInternal

/-!
# Three-connectivity (paper Section 3.2)

Small structural steps whose proofs are entirely internal once the rooted
admissible-path theorem is supplied.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

/--
Paper Lemma 3.2, conditional on Lemma 3.1's 2-connectivity conclusion
and its minimum-degree bookkeeping.  The specialized BGLP connectivity
argument is proved internally in `BGLPConnectivityInternal`.
-/
theorem root_deletion_is_three_connected
    [Fintype V] [DecidableEq V]
    (J : SimpleGraph V)
    (hconn : IsTwoConnected J)
    (hdeg : MinDegreeAtLeast J 4)
    (hno : ¬ HasCycleDivisibleBy J 5) :
    IsKConnected J 3 :=
  BGLP.three_connected_of_two_connected_minDegree_four
    J hconn hdeg hno

end DeanK5
