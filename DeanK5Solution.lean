import DeanK5.FinalDeduction

namespace DeanK5.Comparator

/--
The project theorem in the direct form used for comparison.
-/
theorem dean_conjecture_k5
    {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V)
    (hmin : ∀ v : V, 5 ≤ (G.neighborSet v).ncard) :
    ∃ (v : V) (C : G.Walk v v),
      C.IsCycle ∧ 5 ∣ C.length := by
  letI := Fintype.ofFinite V
  have hdegree' : DeanK5.MinDegreeAtLeast G 5 := by
    simpa [DeanK5.MinDegreeAtLeast, DeanK5.finiteDegree] using hmin
  obtain ⟨C, hC⟩ := DeanK5.dean_conjecture_k5 G hdegree'
  exact
    ⟨C.base, C.walk, C.isCycle,
      Nat.dvd_iff_mod_eq_zero.mpr
        (by simpa [DeanK5.SimpleCycle.length] using hC)⟩

end DeanK5.Comparator
