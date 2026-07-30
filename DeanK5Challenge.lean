import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card

namespace DeanK5.Comparator

/--
Every finite nonempty simple graph of minimum degree at least five contains
a simple cycle whose length is divisible by five.
-/
theorem dean_conjecture_k5
    {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V)
    (hmin : ∀ v : V, 5 ≤ (G.neighborSet v).ncard) :
    ∃ (v : V) (C : G.Walk v v),
      C.IsCycle ∧ 5 ∣ C.length := by
  sorry

end DeanK5.Comparator
