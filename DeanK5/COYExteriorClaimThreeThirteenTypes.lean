import DeanK5.COYExteriorClaimThreeThirteenRank

/-!
# The source types in COY Claim 3.13

After the selected working core is known to be type three, COY classifies it
relative to ordinary vertices of the exterior component.  The definitions
below retain the exact source cardinality conditions.  Type III means that
neither of the two witness configurations exists.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}

/--
A vertex of the source set `V_nc`: an exterior vertex distinct from the two
protected vertices and not a cut vertex of the exterior graph.
-/
structure ExteriorOrdinaryVertex
    (P : PreferredWorkingCoreData G x y z) where
  /-- The vertex, typed in the selected exterior component. -/
  vertex : P.ExteriorVertex
  /-- The vertex is not the second root. -/
  ne_y : vertex.1 ≠ y
  /-- The vertex is not the exceptional vertex. -/
  ne_z : vertex.1 ≠ z
  /-- The vertex is not a cut vertex of the exterior graph. -/
  not_cut : ¬IsCutVertex P.exteriorGraph vertex

namespace TypeThreeStage

variable {P : PreferredWorkingCoreData G x y z}

/-- The neighbors of `v` in the type-three `S`-side. -/
noncomputable def initialNeighborFinset
    (D : P.TypeThreeStage) (v : V) : Finset V := by
  classical
  exact D.core.S.filter (G.Adj v)

/-- The neighbors of `v` in the type-three `T`-side. -/
noncomputable def terminalNeighborFinset
    (D : P.TypeThreeStage) (v : V) : Finset V := by
  classical
  exact D.core.T.filter (G.Adj v)

@[simp] theorem mem_initialNeighborFinset
    (D : P.TypeThreeStage) {v s : V} :
    s ∈ D.initialNeighborFinset v ↔
      s ∈ D.core.S ∧ G.Adj v s := by
  classical
  simp [initialNeighborFinset]

@[simp] theorem mem_terminalNeighborFinset
    (D : P.TypeThreeStage) {v t : V} :
    t ∈ D.terminalNeighborFinset v ↔
      t ∈ D.core.T ∧ G.Adj v t := by
  classical
  simp [terminalNeighborFinset]

/--
A source Type I witness: an ordinary exterior vertex with exactly
`rank + 1` neighbors in the `T`-side.
-/
structure TypeIWitness
    (D : P.TypeThreeStage) where
  /-- The exterior witness. -/
  ordinary : P.ExteriorOrdinaryVertex
  /-- The exact source terminal-neighbor count. -/
  terminal_neighbor_card :
    (D.terminalNeighborFinset
      ordinary.vertex.1).card =
        P.working.rank + 1

/--
A source Type II witness: the core has rank one and an ordinary exterior
vertex has exactly one neighbor in each of `S` and `T`.
-/
structure TypeIIWitness
    (D : P.TypeThreeStage) where
  /-- The exterior witness. -/
  ordinary : P.ExteriorOrdinaryVertex
  /-- Type II is defined only at rank one. -/
  rank_eq_one : P.working.rank = 1
  /-- The exact source initial-side neighbor count. -/
  initial_neighbor_card :
    (D.initialNeighborFinset
      ordinary.vertex.1).card = 1
  /-- The exact source terminal-side neighbor count. -/
  terminal_neighbor_card :
    (D.terminalNeighborFinset
      ordinary.vertex.1).card = 1

/-- Source Type III: neither a Type I nor a Type II witness exists. -/
def IsTypeIII
    (D : P.TypeThreeStage) : Prop :=
  ¬Nonempty D.TypeIWitness ∧
    ¬Nonempty D.TypeIIWitness

namespace TypeIWitness

variable {D : P.TypeThreeStage}

/-- A Type I witness belongs to the selected exterior region. -/
theorem mem_otherRegion
    (W : D.TypeIWitness) :
    W.ordinary.vertex.1 ∈
      P.working.rooted.otherRegion :=
  W.ordinary.vertex.2

/-- At rank one, a Type I witness has two distinct `T`-neighbors. -/
theorem terminal_neighbors_card_eq_two
    (W : D.TypeIWitness)
    (hrank : P.working.rank = 1) :
    (D.terminalNeighborFinset
      W.ordinary.vertex.1).card = 2 := by
  rw [W.terminal_neighbor_card, hrank]

/-- A Type I witness has a named `T`-neighbor at rank one. -/
theorem exists_terminal_neighbor
    (W : D.TypeIWitness)
    (hrank : P.working.rank = 1) :
    ∃ t ∈ D.core.T,
      G.Adj W.ordinary.vertex.1 t := by
  have hcard :=
    W.terminal_neighbors_card_eq_two hrank
  obtain ⟨t, ht⟩ :=
    Finset.card_pos.mp (by
      rw [hcard]
      omega)
  exact ⟨t,
    (D.mem_terminalNeighborFinset.mp ht).1,
    (D.mem_terminalNeighborFinset.mp ht).2⟩

end TypeIWitness

namespace TypeIIWitness

variable {D : P.TypeThreeStage}

/-- A Type II witness belongs to the selected exterior region. -/
theorem mem_otherRegion
    (W : D.TypeIIWitness) :
    W.ordinary.vertex.1 ∈
      P.working.rooted.otherRegion :=
  W.ordinary.vertex.2

/-- A Type II witness has a named `T`-neighbor. -/
theorem exists_terminal_neighbor
    (W : D.TypeIIWitness) :
    ∃ t ∈ D.core.T,
      G.Adj W.ordinary.vertex.1 t := by
  have hpositive :
      0 <
        (D.terminalNeighborFinset
          W.ordinary.vertex.1).card := by
    rw [W.terminal_neighbor_card]
    omega
  obtain ⟨t, ht⟩ :=
    Finset.card_pos.mp hpositive
  exact ⟨t,
    (D.mem_terminalNeighborFinset.mp ht).1,
    (D.mem_terminalNeighborFinset.mp ht).2⟩

end TypeIIWitness

end TypeThreeStage

end PreferredWorkingCoreData

end COY

end DeanK5
