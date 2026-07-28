import DeanK5.COYMinimalCounterexampleElimination

/-!
# Internal bounded COY rooted-path theorem

The preceding development eliminates every minimal counterexample to the
bounded one-exception rooted-path statement.  Strong induction on the rooted
complexity therefore gives the exact `2 ≤ q ≤ 4` interface used elsewhere in
the Dean-conjecture formalization.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/--
The bounded one-exception rooted-path theorem, proved internally.

The exceptional vertex may coincide with a root in recursive calls; this
public interface retains the pairwise-distinct specialization used by the
downstream graph-theoretic argument.
-/
theorem one_exception_rooted_paths_internal
    [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (x y z : V)
    (hqTwo : 2 ≤ q) (hqFour : q ≤ 4)
    (horder : 4 ≤ Fintype.card V)
    (hxy : x ≠ y) (_hzx : z ≠ x) (_hzy : z ≠ y)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hdeg : ∀ v, v ≠ x → v ≠ y → v ≠ z →
      q + 1 ≤ finiteDegree G v) :
    Nonempty (AdmissiblePathFamily G x y q) :=
  bounded_interface_of_minimal_counterexample_false
    (fun M => M.impossible)
    q G x y z hqTwo hqFour horder hxy hconn hdeg

end COY

end DeanK5
