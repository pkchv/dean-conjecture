import DeanK5.COYCoreModification

/-!
# The modified working core in COY Theorem 3

The source makes a special type-3 modification only under condition (T).
This file records that condition exactly enough to retain its distinguished
component and attachment, then makes the (M1)/(M2) choice and constructs the
resulting rooted core.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- The source condition (T) for modifying an optimal type-3 core. -/
structure TypeThreeModificationTrigger
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y z : V}
    (O : OptimalRootedCore G x y) where
  /-- The selected optimal core is of type 3. -/
  core : TypeThreeCore G x O.rank
  /-- Identification with the selected source core. -/
  core_eq : O.rooted.core = .typeThree core
  /-- The root-adjacent side has at least three vertices. -/
  three_le_T : 3 ≤ core.T.card
  /-- The exterior component of the selected core consists only of `y`. -/
  exterior_singleton : O.rooted.otherRegion = {y}
  /-- The neighborhood of the chosen root is exactly `T`. -/
  root_neighbors : ∀ v, G.Adj x v ↔ v ∈ core.T
  /-- The neighborhood of the other root is exactly `T`. -/
  other_root_neighbors : ∀ v, G.Adj y v ↔ v ∈ core.T
  /-- A second deletion component. -/
  component :
    (deleteVertices G O.rooted.core.carrier).ConnectedComponent
  /-- The second component differs from the one containing `y`. -/
  component_ne_other :
    component ≠ O.rooted.otherComponent
  /-- A nonexceptional vertex in the second component. -/
  ordinary : V
  ordinary_mem :
    ordinary ∈ componentVertices
      G O.rooted.core.carrier component
  ordinary_ne_exception : ordinary ≠ z
  /-- A vertex in the second component adjacent to the distinguished `T`-vertex. -/
  attachment : V
  attachment_mem :
    attachment ∈ componentVertices
      G O.rooted.core.carrier component
  /-- The distinguished `T`-vertex attached to the second component. -/
  t₀ : V
  t₀_mem : t₀ ∈ core.T
  t₀_adj_attachment : G.Adj t₀ attachment

namespace TypeThreeModificationTrigger

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}

/-- The distinguished vertex is adjacent to the selected root. -/
theorem root_adj_t₀
    (T : TypeThreeModificationTrigger (z := z) O) :
    G.Adj x T.t₀ :=
  (T.root_neighbors T.t₀).2 T.t₀_mem

/-- The distinguished vertex is adjacent to the other root. -/
theorem other_root_adj_t₀
    (T : TypeThreeModificationTrigger (z := z) O) :
    G.Adj y T.t₀ :=
  (T.other_root_neighbors T.t₀).2 T.t₀_mem

/-- In the balanced (M1) case the original rank is at least two. -/
theorem two_le_rank_of_balanced
    (T : TypeThreeModificationTrigger (z := z) O)
    (hbalance : T.core.T.card = T.core.S.card + 1) :
    2 ≤ O.rank := by
  have hthree := T.three_le_T
  rw [hbalance, T.core.card_S] at hthree
  omega

end TypeThreeModificationTrigger

/-- The mutually exclusive source modifications (M1) and (M2). -/
inductive TypeThreeModificationChoice
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y z : V}
    {O : OptimalRootedCore G x y}
    (T : TypeThreeModificationTrigger (z := z) O) where
  /-- Tight case: erase one vertex from each side and lower the rank. -/
  | balanced
      (s₀ : V) (s₀_mem : s₀ ∈ T.core.S)
      (card_eq : T.core.T.card = T.core.S.card + 1)
  /-- Slack case: erase only `t₀` and retain the rank. -/
  | terminal (large : O.rank + 2 ≤ T.core.T.card)

namespace TypeThreeModificationChoice

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}
  {T : TypeThreeModificationTrigger (z := z) O}

/-- Condition (T) always selects one of (M1) and (M2). -/
theorem exists_choice :
    Nonempty (TypeThreeModificationChoice T) := by
  by_cases hbalance :
      T.core.T.card = T.core.S.card + 1
  · have hrank := T.two_le_rank_of_balanced hbalance
    have hSNonempty : T.core.S.Nonempty := by
      rw [← Finset.card_pos, T.core.card_S]
      omega
    obtain ⟨s₀, hs₀⟩ := hSNonempty
    exact ⟨.balanced s₀ hs₀ hbalance⟩
  · have hlarge : O.rank + 2 ≤ T.core.T.card := by
      have hlower := T.core.card_T_lower
      rw [T.core.card_S] at hbalance
      omega
    exact ⟨.terminal hlarge⟩

/-- The rank of the modified core. -/
def rank (K : TypeThreeModificationChoice T) : ℕ :=
  match K with
  | .balanced _ _ _ => O.rank - 1
  | .terminal _ => O.rank

/-- The type-3 core produced by the selected modification. -/
def core (K : TypeThreeModificationChoice T) :
    TypeThreeCore G x K.rank :=
  match K with
  | .balanced s₀ hs₀ hbalance =>
      T.core.eraseBalanced s₀ T.t₀ hs₀ T.t₀_mem
        (T.two_le_rank_of_balanced hbalance) hbalance
  | .terminal hlarge =>
      T.core.eraseTerminal T.t₀ T.t₀_mem
        T.three_le_T hlarge

/-- The modified carrier is contained in the original selected carrier. -/
theorem carrier_subset_original
    (K : TypeThreeModificationChoice T) :
    (Core.typeThree K.core).carrier ⊆
      O.rooted.core.carrier := by
  intro v hv
  rw [T.core_eq]
  cases K with
  | balanced s₀ hs₀ hbalance =>
      simp only [core, rank, Core.carrier, Core.S, Core.T,
        TypeThreeCore.eraseBalanced,
        Finset.mem_insert, Finset.mem_union,
        Finset.mem_erase] at hv ⊢
      aesop
  | terminal hlarge =>
      simp only [core, rank, Core.carrier, Core.S, Core.T,
        TypeThreeCore.eraseTerminal,
        Finset.mem_insert, Finset.mem_union,
        Finset.mem_erase] at hv ⊢
      aesop

/-- The modified type-3 core, rooted at the original ordered pair. -/
def rooted (K : TypeThreeModificationChoice T) :
    RootedCore G x y K.rank where
  core := .typeThree K.core
  other_root_not_mem := by
    intro hy
    exact O.rooted.other_root_not_mem
      (K.carrier_subset_original hy)

/-- The distinguished vertex has been removed from the working `T`-side. -/
theorem t₀_not_mem_core_T
    (K : TypeThreeModificationChoice T) :
    T.t₀ ∉ K.core.T := by
  cases K <;>
    simp [core, TypeThreeCore.eraseBalanced,
      TypeThreeCore.eraseTerminal]

end TypeThreeModificationChoice

end COY

end DeanK5
