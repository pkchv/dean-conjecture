import DeanK5.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Source-level COY core structures

This file records the three core configurations from Chiba--Ota--Yamashita
using finite vertex sets in an ambient graph.  These records retain both
the positive adjacencies used to construct paths and the clique or
independence conditions used by the maximal-core arguments.

The path catalogues themselves live in `COYCores.lean`; conversion from
these source-level records to the pointed path certificates is kept
separate.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- A source type-1 `ℓ`-core `x ∨ T`. -/
structure TypeOneCore
    [DecidableEq V]
    (G : SimpleGraph V) (x : V) (ℓ : ℕ) where
  /-- The clique joined completely to the root. -/
  T : Finset V
  /-- Type 1 is defined only for positive rank. -/
  rank_pos : 1 ≤ ℓ
  /-- The clique has the source-prescribed order `ℓ+1`. -/
  card_T : T.card = ℓ + 1
  /-- The root is not one of the clique vertices. -/
  root_not_mem : x ∉ T
  /-- Every clique vertex is adjacent to the root. -/
  root_adj : ∀ t ∈ T, G.Adj x t
  /-- The set `T` is a clique in the ambient graph. -/
  clique_T : G.IsClique (↑T : Set V)

/-- A source type-2 `ℓ`-core `x ∨ S ∨ T`. -/
structure TypeTwoCore
    [DecidableEq V]
    (G : SimpleGraph V) (x : V) (ℓ : ℕ) where
  /-- The two-vertex independent class adjacent to the root. -/
  S : Finset V
  /-- The terminal clique. -/
  T : Finset V
  /-- Type 2 is defined only for rank at least two. -/
  rank_ge_two : 2 ≤ ℓ
  /-- The first class has exactly two vertices. -/
  card_S : S.card = 2
  /-- The terminal clique has exactly `ℓ` vertices. -/
  card_T : T.card = ℓ
  /-- The two classes are disjoint. -/
  disjoint : Disjoint S T
  /-- The root lies outside the first class. -/
  root_not_mem_S : x ∉ S
  /-- The root lies outside the terminal clique. -/
  root_not_mem_T : x ∉ T
  /-- The first class is independent in the ambient graph. -/
  independent_S : G.IsIndepSet (↑S : Set V)
  /-- The terminal class is a clique in the ambient graph. -/
  clique_T : G.IsClique (↑T : Set V)
  /-- The root is joined completely to the first class. -/
  root_adj_S : ∀ s ∈ S, G.Adj x s
  /-- The two classes are completely joined. -/
  cross_adj : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t

/-- A source type-3 `ℓ`-core `x ∨ T ∨ S`. -/
structure TypeThreeCore
    [DecidableEq V]
    (G : SimpleGraph V) (x : V) (ℓ : ℕ) where
  /-- The terminal independent class, of order `ℓ`. -/
  S : Finset V
  /-- The independent class adjacent to the root. -/
  T : Finset V
  /-- The terminal class has exactly `ℓ` vertices. -/
  card_S : S.card = ℓ
  /-- The root-adjacent class has at least `max (ℓ+1) 2` vertices. -/
  card_T_lower : max (ℓ + 1) 2 ≤ T.card
  /-- The two classes are disjoint. -/
  disjoint : Disjoint S T
  /-- The root lies outside the terminal class. -/
  root_not_mem_S : x ∉ S
  /-- The root lies outside the root-adjacent class. -/
  root_not_mem_T : x ∉ T
  /-- The terminal class is independent in the ambient graph. -/
  independent_S : G.IsIndepSet (↑S : Set V)
  /-- The root-adjacent class is independent in the ambient graph. -/
  independent_T : G.IsIndepSet (↑T : Set V)
  /-- The root is joined completely to `T`. -/
  root_adj_T : ∀ t ∈ T, G.Adj x t
  /-- The two independent classes are completely joined. -/
  cross_adj : ∀ t ∈ T, ∀ s ∈ S, G.Adj t s

/-- One of the three source `ℓ`-core configurations. -/
inductive Core
    [DecidableEq V]
    (G : SimpleGraph V) (x : V) (ℓ : ℕ) where
  /-- A type-1 core. -/
  | typeOne (data : TypeOneCore G x ℓ)
  /-- A type-2 core. -/
  | typeTwo (data : TypeTwoCore G x ℓ)
  /-- A type-3 core. -/
  | typeThree (data : TypeThreeCore G x ℓ)

namespace Core

variable [DecidableEq V] {G : SimpleGraph V} {x : V} {ℓ : ℕ}

/-- The numerical source type of a core. -/
def typeNumber : Core G x ℓ → ℕ
  | .typeOne _ => 1
  | .typeTwo _ => 2
  | .typeThree _ => 3

/-- The source set `S`, empty in type 1. -/
def S : Core G x ℓ → Finset V
  | .typeOne _ => ∅
  | .typeTwo C => C.S
  | .typeThree C => C.S

/-- The source set `T`. -/
def T : Core G x ℓ → Finset V
  | .typeOne C => C.T
  | .typeTwo C => C.T
  | .typeThree C => C.T

/-- The vertices occupied by a core, including its root. -/
def carrier (C : Core G x ℓ) : Finset V :=
  insert x (C.S ∪ C.T)

@[simp] theorem root_mem_carrier (C : Core G x ℓ) :
    x ∈ C.carrier := by
  simp [carrier]

theorem S_subset_carrier (C : Core G x ℓ) :
    C.S ⊆ C.carrier := by
  intro v hv
  simp [carrier, hv]

theorem T_subset_carrier (C : Core G x ℓ) :
    C.T ⊆ C.carrier := by
  intro v hv
  simp [carrier, hv]

theorem root_not_mem_S (C : Core G x ℓ) :
    x ∉ C.S := by
  cases C with
  | typeOne C => simp [S]
  | typeTwo C => simpa [S] using C.root_not_mem_S
  | typeThree C => simpa [S] using C.root_not_mem_S

theorem root_not_mem_T (C : Core G x ℓ) :
    x ∉ C.T := by
  cases C with
  | typeOne C => simpa [T] using C.root_not_mem
  | typeTwo C => simpa [T] using C.root_not_mem_T
  | typeThree C => simpa [T] using C.root_not_mem_T

theorem disjoint_S_T (C : Core G x ℓ) :
    Disjoint C.S C.T := by
  cases C with
  | typeOne C => simp [S, T]
  | typeTwo C => simpa [S, T] using C.disjoint
  | typeThree C => simpa [S, T] using C.disjoint

/-- Every source core contains a vertex other than its root. -/
theorem exists_ne_root_mem_carrier (C : Core G x ℓ) :
    ∃ t ∈ C.carrier, t ≠ x := by
  cases C with
  | typeOne C =>
      have hpos : 0 < C.T.card := by
        rw [C.card_T]
        omega
      obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
      exact ⟨t, by simp [carrier, S, T, ht],
        fun h => C.root_not_mem (h ▸ ht)⟩
  | typeTwo C =>
      have hpos : 0 < C.S.card := by
        rw [C.card_S]
        omega
      obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
      exact ⟨s, by simp [carrier, S, T, hs],
        fun h => C.root_not_mem_S (h ▸ hs)⟩
  | typeThree C =>
      have hpos : 0 < C.T.card := by
        have htwo : 2 ≤ C.T.card :=
          (Nat.le_max_right (ℓ + 1) 2).trans C.card_T_lower
        omega
      obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
      exact ⟨t, by simp [carrier, S, T, ht],
        fun h => C.root_not_mem_T (h ▸ ht)⟩

/-- Classify a nonroot vertex of a core into one of its two source parts. -/
theorem mem_S_or_mem_T_of_mem_carrier_of_ne_root
    (C : Core G x ℓ) {v : V}
    (hv : v ∈ C.carrier) (hvx : v ≠ x) :
    v ∈ C.S ∨ v ∈ C.T := by
  simpa [carrier, hvx] using hv

end Core

/--
A core with respect to the ordered root pair `(x,y)`: the second root is
outside the core carrier.
-/
structure RootedCore
    [DecidableEq V]
    (G : SimpleGraph V) (x y : V) (ℓ : ℕ) where
  /-- The underlying core with root `x`. -/
  core : Core G x ℓ
  /-- The other root is outside the selected core. -/
  other_root_not_mem : y ∉ core.carrier

/--
COY Remark 1: a root of degree at least two, nonadjacent to the other
root, supports a type-1 or type-3 core.

If two neighbors of `x` are adjacent, they form the clique of a rank-one
type-1 core.  Otherwise the entire neighborhood of `x` is independent
and forms the `T`-side of a rank-zero type-3 core.
-/
theorem exists_typeOne_or_typeThree_rootedCore
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hnotAdj : ¬G.Adj x y)
    (hdegree : 2 ≤ finiteDegree G x) :
    (∃ C : RootedCore G x y 1,
      ∃ D : TypeOneCore G x 1, C.core = .typeOne D) ∨
    (∃ C : RootedCore G x y 0,
      ∃ D : TypeThreeCore G x 0, C.core = .typeThree D) := by
  classical
  let N : Finset V := (G.neighborSet x).toFinset
  have hmemN (v : V) :
      v ∈ N ↔ G.Adj x v := by
    simp [N, SimpleGraph.mem_neighborSet]
  have hNcard : N.card = finiteDegree G x := by
    unfold finiteDegree
    simp only [N]
    rw [Set.ncard_eq_toFinset_card']
  by_cases hpair :
      ∃ u ∈ N, ∃ v ∈ N, u ≠ v ∧ G.Adj u v
  · obtain ⟨u, huN, v, hvN, huv, huvAdj⟩ := hpair
    have hxuAdj : G.Adj x u := (hmemN u).1 huN
    have hxvAdj : G.Adj x v := (hmemN v).1 hvN
    have hxu : x ≠ u := hxuAdj.ne
    have hxv : x ≠ v := hxvAdj.ne
    have hyu : y ≠ u := by
      intro hyu
      subst u
      exact hnotAdj hxuAdj
    have hyv : y ≠ v := by
      intro hyv
      subst v
      exact hnotAdj hxvAdj
    let D : TypeOneCore G x 1 := {
      T := {u, v}
      rank_pos := le_rfl
      card_T := by simp [huv]
      root_not_mem := by simp [hxu, hxv]
      root_adj := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact hxuAdj
        · exact hxvAdj
      clique_T := by
        simpa only [Finset.coe_insert, Finset.coe_singleton,
          SimpleGraph.isClique_pair] using
          (show u ≠ v → G.Adj u v from fun _ => huvAdj)
    }
    let C : RootedCore G x y 1 := {
      core := .typeOne D
      other_root_not_mem := by
        simp [Core.carrier, Core.S, Core.T,
          D, hxy.symm, hyu, hyv]
    }
    exact Or.inl ⟨C, D, rfl⟩
  · have hrootNotN : x ∉ N := by
      intro hxN
      exact G.loopless.irrefl x ((hmemN x).1 hxN)
    have hyNotN : y ∉ N := by
      intro hyN
      exact hnotAdj ((hmemN y).1 hyN)
    let D : TypeThreeCore G x 0 := {
      S := ∅
      T := N
      card_S := by simp
      card_T_lower := by
        simpa [hNcard] using hdegree
      disjoint := by simp
      root_not_mem_S := by simp
      root_not_mem_T := hrootNotN
      independent_S := by simp
      independent_T := by
        intro u hu v hv huv huvAdj
        apply hpair
        exact ⟨u, by simpa using hu, v, by simpa using hv,
          huv, huvAdj⟩
      root_adj_T := by
        intro t ht
        exact (hmemN t).1 ht
      cross_adj := by simp
    }
    let C : RootedCore G x y 0 := {
      core := .typeThree D
      other_root_not_mem := by
        simp [Core.carrier, Core.S, Core.T,
          D, hxy.symm, hyNotN]
    }
    exact Or.inr ⟨C, D, rfl⟩

end COY

end DeanK5
