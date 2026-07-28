import DeanK5.COYCoreSelection

/-!
# Extension operations for COY cores

The maximal-core argument repeatedly turns an exterior vertex with too many
core neighbors into a larger core of the same source type.  These constructors
record those set and adjacency checks once.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace TypeOneCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

/-- Add one clique vertex to a type-1 core. -/
def insertTerminal
    (C : TypeOneCore G x ℓ)
    (v : V)
    (hvRoot : v ≠ x)
    (hvT : v ∉ C.T)
    (hxv : G.Adj x v)
    (hvAdj : ∀ t ∈ C.T, G.Adj v t) :
    TypeOneCore G x (ℓ + 1) where
  T := insert v C.T
  rank_pos := by omega
  card_T := by simp [hvT, C.card_T]
  root_not_mem := by
    simp [hvRoot.symm, C.root_not_mem]
  root_adj := by
    intro t ht
    simp only [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact hxv
    · exact C.root_adj t ht
  clique_T := by
    rw [Finset.coe_insert,
      isClique_insert_of_notMem (by simpa using hvT)]
    exact ⟨C.clique_T, fun t ht => hvAdj t (by simpa using ht)⟩

end TypeOneCore

namespace TypeTwoCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

/-- Add one clique vertex to a type-2 core. -/
def insertTerminal
    (C : TypeTwoCore G x ℓ)
    (v : V)
    (hvRoot : v ≠ x)
    (hvS : v ∉ C.S)
    (hvT : v ∉ C.T)
    (hvAdjS : ∀ s ∈ C.S, G.Adj s v)
    (hvAdjT : ∀ t ∈ C.T, G.Adj v t) :
    TypeTwoCore G x (ℓ + 1) where
  S := C.S
  T := insert v C.T
  rank_ge_two := by
    have h := C.rank_ge_two
    omega
  card_S := C.card_S
  card_T := by simp [hvT, C.card_T]
  disjoint := by
    rw [Finset.disjoint_insert_right]
    exact ⟨hvS, C.disjoint⟩
  root_not_mem_S := C.root_not_mem_S
  root_not_mem_T := by
    simp [hvRoot.symm, C.root_not_mem_T]
  independent_S := C.independent_S
  clique_T := by
    rw [Finset.coe_insert,
      isClique_insert_of_notMem (by simpa using hvT)]
    exact ⟨C.clique_T,
      fun t ht => hvAdjT t (by simpa using ht)⟩
  root_adj_S := C.root_adj_S
  cross_adj := by
    intro s hs t ht
    simp only [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact hvAdjS s hs
    · exact C.cross_adj s hs t ht

end TypeTwoCore

namespace TypeThreeCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x : V} {ℓ : ℕ}

/-- Add one vertex to the root-adjacent independent side of a type-3 core. -/
def insertTerminal
    (C : TypeThreeCore G x ℓ)
    (v : V)
    (hvRoot : v ≠ x)
    (hvS : v ∉ C.S)
    (hvT : v ∉ C.T)
    (hxv : G.Adj x v)
    (hvNonadjT : ∀ t ∈ C.T, ¬G.Adj v t)
    (hvAdjS : ∀ s ∈ C.S, G.Adj v s) :
    TypeThreeCore G x ℓ where
  S := C.S
  T := insert v C.T
  card_S := C.card_S
  card_T_lower := by
    calc
      max (ℓ + 1) 2 ≤ C.T.card := C.card_T_lower
      _ ≤ (insert v C.T).card :=
        Finset.card_le_card (Finset.subset_insert v C.T)
  disjoint := by
    rw [Finset.disjoint_insert_right]
    exact ⟨hvS, C.disjoint⟩
  root_not_mem_S := C.root_not_mem_S
  root_not_mem_T := by
    simp [hvRoot.symm, C.root_not_mem_T]
  independent_S := C.independent_S
  independent_T := by
    intro a ha b hb hab
    simp only [Finset.coe_insert,
      Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (hab rfl)
      · exact hvNonadjT b (by simpa using hb)
    · rcases hb with rfl | hb
      · intro hav
        exact hvNonadjT a (by simpa using ha) hav.symm
      · exact C.independent_T ha hb hab
  root_adj_T := by
    intro t ht
    simp only [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact hxv
    · exact C.root_adj_T t ht
  cross_adj := by
    intro t ht s hs
    simp only [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact hvAdjS s hs
    · exact C.cross_adj t ht s hs

/--
Add an exterior vertex to the terminal independent side, retaining a
sufficiently large subset of the old root-adjacent side.
-/
def insertInitial
    (C : TypeThreeCore G x ℓ)
    (v : V) (U : Finset V)
    (hUT : U ⊆ C.T)
    (hUCard : max ((ℓ + 1) + 1) 2 ≤ U.card)
    (hvRoot : v ≠ x)
    (hvS : v ∉ C.S)
    (hvU : v ∉ U)
    (hvNonadjS : ∀ s ∈ C.S, ¬G.Adj v s)
    (hvAdjU : ∀ t ∈ U, G.Adj v t) :
    TypeThreeCore G x (ℓ + 1) where
  S := insert v C.S
  T := U
  card_S := by simp [hvS, C.card_S]
  card_T_lower := hUCard
  disjoint := by
    rw [Finset.disjoint_left]
    intro a ha haU
    simp only [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact hvU haU
    · exact Finset.disjoint_left.mp C.disjoint ha (hUT haU)
  root_not_mem_S := by
    simp [hvRoot.symm, C.root_not_mem_S]
  root_not_mem_T := by
    intro hxU
    exact C.root_not_mem_T (hUT hxU)
  independent_S := by
    intro a ha b hb hab
    simp only [Finset.coe_insert,
      Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (hab rfl)
      · exact hvNonadjS b (by simpa using hb)
    · rcases hb with rfl | hb
      · intro hav
        exact hvNonadjS a (by simpa using ha) hav.symm
      · exact C.independent_S ha hb hab
  independent_T := by
    intro a ha b hb hab
    exact C.independent_T
      (by simpa using hUT (by simpa using ha))
      (by simpa using hUT (by simpa using hb))
      hab
  root_adj_T := by
    intro t ht
    exact C.root_adj_T t (hUT ht)
  cross_adj := by
    intro t ht s hs
    simp only [Finset.mem_insert] at hs
    rcases hs with rfl | hs
    · exact (hvAdjU t ht).symm
    · exact C.cross_adj t (hUT ht) s hs

end TypeThreeCore

end COY

end DeanK5
