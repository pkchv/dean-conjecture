import DeanK5.Published

/-!
# Three-connectivity (paper Section 3.2)

Small structural steps whose proofs are entirely internal once the named
published axioms are supplied.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

/--
Paper Lemma 3.2, conditional on Lemma 3.1's 2-connectivity conclusion
and its minimum-degree bookkeeping.

BGLP Lemma 2.3 with `k = 5` and `r = 1` gives connectivity at least
`5/2`; integrality is represented by instantiating `ConnectivityAtLeast`
at the integer `2`, yielding 3-connectivity.
-/
theorem root_deletion_is_three_connected
    [Fintype V] [DecidableEq V]
    (J : SimpleGraph V)
    (hconn : IsTwoConnected J)
    (hdeg : MinDegreeAtLeast J 4)
    (hno : ¬ HasCycleDivisibleBy J 5) :
    IsKConnected J 3 := by
  have hfamilies :
      ¬ Nonempty (AdmissibleCycleFamily J 5) :=
    no_five_admissible_cycles_of_no_divisible_cycle hno
  have hκ :=
    BGLP.connectivity_of_no_admissible_cycles 5 1 J
      (by omega) hconn (by simpa using hdeg) hfamilies
  apply hκ 2
  norm_num

end DeanK5
