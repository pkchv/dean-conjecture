import DeanK5.COYCoreStructure

/-!
# Cardinality of COY cores

This file records the uniform lower bound on the carrier of each of the
three source core types.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY.Core

variable [DecidableEq V] {G : SimpleGraph V} {x : V} {ℓ : ℕ}

/-- Every COY core contains at least three vertices. -/
theorem three_le_card_carrier (C : COY.Core G x ℓ) :
    3 ≤ C.carrier.card := by
  cases C with
  | typeOne C =>
      have hrank := C.rank_pos
      simp only [carrier, S, T, Finset.empty_union]
      rw [Finset.card_insert_of_notMem C.root_not_mem, C.card_T]
      omega
  | typeTwo C =>
      have hx : x ∉ C.S ∪ C.T := by
        simp [C.root_not_mem_S, C.root_not_mem_T]
      simp only [carrier, S, T]
      rw [Finset.card_insert_of_notMem hx,
        Finset.card_union_of_disjoint C.disjoint, C.card_S]
      omega
  | typeThree C =>
      have hx : x ∉ C.S ∪ C.T := by
        simp [C.root_not_mem_S, C.root_not_mem_T]
      have htwo : 2 ≤ C.T.card :=
        (Nat.le_max_right (ℓ + 1) 2).trans C.card_T_lower
      simp only [carrier, S, T]
      rw [Finset.card_insert_of_notMem hx,
        Finset.card_union_of_disjoint C.disjoint]
      omega

end COY.Core

end DeanK5
