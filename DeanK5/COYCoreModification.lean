import DeanK5.COYCoreExtensions

/-!
# The special type-3 COY core modifications

Condition (H2-3) of the source proof removes one distinguished vertex from
the root-adjacent side of a selected type-3 core.  In the tight case it also
removes one terminal-side vertex and lowers the rank.  These constructors
certify that both resulting configurations remain source type-3 cores.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeThreeCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

/--
Modification (M1): when `|T| = |S| + 1`, erase one vertex from each side
and lower the rank by one.
-/
def eraseBalanced
    (C : TypeThreeCore G x ℓ)
    (s₀ t₀ : V)
    (hs₀ : s₀ ∈ C.S)
    (ht₀ : t₀ ∈ C.T)
    (hℓ : 2 ≤ ℓ)
    (hbalance : C.T.card = C.S.card + 1) :
    TypeThreeCore G x (ℓ - 1) where
  S := C.S.erase s₀
  T := C.T.erase t₀
  card_S := by
    rw [Finset.card_erase_of_mem hs₀, C.card_S]
  card_T_lower := by
    rw [Finset.card_erase_of_mem ht₀, hbalance, C.card_S]
    omega
  disjoint :=
    C.disjoint.mono
      (Finset.erase_subset s₀ C.S)
      (Finset.erase_subset t₀ C.T)
  root_not_mem_S := fun hx =>
    C.root_not_mem_S (Finset.mem_of_mem_erase hx)
  root_not_mem_T := fun hx =>
    C.root_not_mem_T (Finset.mem_of_mem_erase hx)
  independent_S := by
    intro a ha b hb hab
    exact C.independent_S
      (by
        change a ∈ C.S.erase s₀ at ha
        simpa using Finset.mem_of_mem_erase ha)
      (by
        change b ∈ C.S.erase s₀ at hb
        simpa using Finset.mem_of_mem_erase hb)
      hab
  independent_T := by
    intro a ha b hb hab
    exact C.independent_T
      (by
        change a ∈ C.T.erase t₀ at ha
        simpa using Finset.mem_of_mem_erase ha)
      (by
        change b ∈ C.T.erase t₀ at hb
        simpa using Finset.mem_of_mem_erase hb)
      hab
  root_adj_T := by
    intro t ht
    exact C.root_adj_T t (Finset.mem_of_mem_erase ht)
  cross_adj := by
    intro t ht s hs
    exact C.cross_adj
      t (Finset.mem_of_mem_erase ht)
      s (Finset.mem_of_mem_erase hs)

/--
Modification (M2): when `|T| ≥ |S| + 2`, erase the distinguished
root-adjacent vertex and retain the rank.
-/
def eraseTerminal
    (C : TypeThreeCore G x ℓ)
    (t₀ : V)
    (ht₀ : t₀ ∈ C.T)
    (hthree : 3 ≤ C.T.card)
    (hlarge : ℓ + 2 ≤ C.T.card) :
    TypeThreeCore G x ℓ where
  S := C.S
  T := C.T.erase t₀
  card_S := C.card_S
  card_T_lower := by
    rw [Finset.card_erase_of_mem ht₀]
    have htwo : 2 ≤ C.T.card - 1 := by
      omega
    omega
  disjoint :=
    C.disjoint.mono (fun _ h => h)
      (Finset.erase_subset t₀ C.T)
  root_not_mem_S := C.root_not_mem_S
  root_not_mem_T := fun hx =>
    C.root_not_mem_T (Finset.mem_of_mem_erase hx)
  independent_S := C.independent_S
  independent_T := by
    intro a ha b hb hab
    exact C.independent_T
      (by
        change a ∈ C.T.erase t₀ at ha
        simpa using Finset.mem_of_mem_erase ha)
      (by
        change b ∈ C.T.erase t₀ at hb
        simpa using Finset.mem_of_mem_erase hb)
      hab
  root_adj_T := by
    intro t ht
    exact C.root_adj_T t (Finset.mem_of_mem_erase ht)
  cross_adj := by
    intro t ht s hs
    exact C.cross_adj t (Finset.mem_of_mem_erase ht) s hs

end TypeThreeCore

end COY

end DeanK5
