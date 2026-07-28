import DeanK5.COYConcatenation

/-!
# Explicit COY cores

This file formalizes the explicit path catalogues in the three core
configurations used in Chiba--Ota--Yamashita.  It proves the bounded
instances of both parts of COY Fact 2 needed by this project.

Rather than treating the displayed vertex sequences as informal walks,
`SimplePath.ofVertexList` checks adjacency and absence of repeated
vertices and then constructs a Mathlib walk with `Walk.ofSupport`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace SimplePath

/--
Construct a certified simple path from an explicit list of internal
vertices.  This is the basic constructor used for all COY core paths.
-/
def ofVertexList
    {G : SimpleGraph V} {x y : V}
    (middle : List V)
    (hchain : (x :: middle ++ [y]).IsChain G.Adj)
    (hnodup : (x :: middle ++ [y]).Nodup) :
    SimplePath G x y := by
  let vertices := x :: middle ++ [y]
  have hne : vertices ≠ [] := by
    simp [vertices]
  let walk₀ := SimpleGraph.Walk.ofSupport vertices hne hchain
  have hstart : vertices.head hne = x := by
    simp [vertices]
  have hend : vertices.getLast hne = y := by
    simp [vertices]
  let walk : G.Walk x y := walk₀.copy hstart hend
  exact {
    walk := walk
    isPath := by
      rw [SimpleGraph.Walk.isPath_def]
      dsimp [walk]
      rw [SimpleGraph.Walk.support_copy]
      dsimp [walk₀]
      rw [SimpleGraph.Walk.support_ofSupport]
      exact hnodup
  }

@[simp] theorem ofVertexList_support
    {G : SimpleGraph V} {x y : V}
    (middle : List V)
    (hchain : (x :: middle ++ [y]).IsChain G.Adj)
    (hnodup : (x :: middle ++ [y]).Nodup) :
    (ofVertexList middle hchain hnodup :
      SimplePath G x y).walk.support =
        x :: middle ++ [y] := by
  rw [ofVertexList, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_ofSupport]

@[simp] theorem ofVertexList_length
    {G : SimpleGraph V} {x y : V}
    (middle : List V)
    (hchain : (x :: middle ++ [y]).IsChain G.Adj)
    (hnodup : (x :: middle ++ [y]).Nodup) :
    (ofVertexList middle hchain hnodup :
      SimplePath G x y).length = middle.length + 1 := by
  rw [ofVertexList, SimplePath.length,
    SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_ofSupport]
  simp

end SimplePath

namespace COY

/--
A type-1 `ℓ`-core, pointed at the terminal vertex `target`.

The source core is `x ∨ T`, where `T` is a clique of order `ℓ+1`.
Here `target` is one chosen vertex of `T` and `other` enumerates the
remaining `ℓ` vertices.  The separation fields state exactly that these
are distinct vertices; the adjacency fields state exactly the edges used
by the paths in Fact 2.
-/
structure PointedTypeOneCore
    (G : SimpleGraph V) (x target : V) (ℓ : ℕ) where
  /-- The vertices of the clique other than `target`. -/
  other : Fin ℓ ↪ V
  x_ne_target : x ≠ target
  x_ne_other : ∀ i, x ≠ other i
  target_ne_other : ∀ i, target ≠ other i
  adj_x_target : G.Adj x target
  adj_x_other : ∀ i, G.Adj x (other i)
  adj_other_target : ∀ i, G.Adj (other i) target
  adj_other : ∀ i j, i ≠ j → G.Adj (other i) (other j)

namespace PointedTypeOneCore

variable {G : SimpleGraph V} {x target : V} {ℓ : ℕ}

/-- The direct `x`--`target` path in a type-1 core. -/
def pathOne (C : PointedTypeOneCore G x target ℓ) :
    SimplePath G x target :=
  SimplePath.ofAdj C.adj_x_target

/-- The two-edge `x`--`target` path through `other 0`. -/
def pathTwo
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, hℓ⟩
  have hot : C.other i₀ ≠ target :=
    (C.target_ne_other i₀).symm
  exact SimplePath.ofVertexList [C.other i₀]
    (by simp [C.adj_x_other, C.adj_other_target])
    (by
      simp [C.x_ne_other, C.x_ne_target,
        hot])

/-- The three-edge `x`--`target` path through `other 0, other 1`. -/
def pathThree
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, by omega⟩
  let i₁ : Fin ℓ := ⟨1, by omega⟩
  have hot : ∀ i, C.other i ≠ target :=
    fun i => (C.target_ne_other i).symm
  exact SimplePath.ofVertexList [C.other i₀, C.other i₁]
    (by
      simp [C.adj_x_other, C.adj_other,
        C.adj_other_target, i₀, i₁])
    (by
      have hne : i₀ ≠ i₁ := by
        simp [i₀, i₁]
      simp [C.x_ne_other, C.x_ne_target,
        hot, C.other.injective.ne hne,
        i₀, i₁])

/-- The four-edge `x`--`target` path through `other 0,1,2`. -/
def pathFour
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, by omega⟩
  let i₁ : Fin ℓ := ⟨1, by omega⟩
  let i₂ : Fin ℓ := ⟨2, by omega⟩
  have hot : ∀ i, C.other i ≠ target :=
    fun i => (C.target_ne_other i).symm
  exact SimplePath.ofVertexList
    [C.other i₀, C.other i₁, C.other i₂]
    (by
      simp [C.adj_x_other, C.adj_other,
        C.adj_other_target, i₀, i₁, i₂])
    (by
      have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
      have h02 : i₀ ≠ i₂ := by simp [i₀, i₂]
      have h12 : i₁ ≠ i₂ := by simp [i₁, i₂]
      simp [C.x_ne_other, C.x_ne_target,
        hot, C.other.injective.ne h01,
        C.other.injective.ne h02,
        C.other.injective.ne h12, i₀, i₁, i₂])

/-- The five-edge `x`--`target` path through `other 0,1,2,3`. -/
def pathFive
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 4 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, by omega⟩
  let i₁ : Fin ℓ := ⟨1, by omega⟩
  let i₂ : Fin ℓ := ⟨2, by omega⟩
  let i₃ : Fin ℓ := ⟨3, by omega⟩
  have hot : ∀ i, C.other i ≠ target :=
    fun i => (C.target_ne_other i).symm
  exact SimplePath.ofVertexList
    [C.other i₀, C.other i₁, C.other i₂, C.other i₃]
    (by
      simp [C.adj_x_other, C.adj_other,
        C.adj_other_target, i₀, i₁, i₂, i₃])
    (by
      have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
      have h02 : i₀ ≠ i₂ := by simp [i₀, i₂]
      have h03 : i₀ ≠ i₃ := by simp [i₀, i₃]
      have h12 : i₁ ≠ i₂ := by simp [i₁, i₂]
      have h13 : i₁ ≠ i₃ := by simp [i₁, i₃]
      have h23 : i₂ ≠ i₃ := by simp [i₂, i₃]
      simp [C.x_ne_other, C.x_ne_target,
        hot, C.other.injective.ne h01,
        C.other.injective.ne h02,
        C.other.injective.ne h03,
        C.other.injective.ne h12,
        C.other.injective.ne h13,
        C.other.injective.ne h23,
        i₀, i₁, i₂, i₃])

@[simp] theorem pathOne_length
    (C : PointedTypeOneCore G x target ℓ) :
    C.pathOne.length = 1 := by
  simp [pathOne]

@[simp] theorem pathTwo_length
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    (C.pathTwo hℓ).length = 2 := by
  simp [pathTwo]

@[simp] theorem pathThree_length
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    (C.pathThree hℓ).length = 3 := by
  simp [pathThree]

@[simp] theorem pathFour_length
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    (C.pathFour hℓ).length = 4 := by
  simp [pathFour]

@[simp] theorem pathFive_length
    (C : PointedTypeOneCore G x target ℓ)
    (hℓ : 4 ≤ ℓ) :
    (C.pathFive hℓ).length = 5 := by
  simp [pathFive]

/--
COY Fact 2(2), type 1, for `ℓ = 2`: three semi-admissible paths
of lengths `1,2,3`.
-/
def factTwoTypeOneTwo
    (C : PointedTypeOneCore G x target 2) :
    SemiAdmissiblePathFamily G x target 3 where
  start := 1
  step := 1
  admissible_step := Or.inl rfl
  start_ge_one := le_rfl
  path := ![C.pathOne, C.pathTwo (by omega),
    C.pathThree (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
COY Fact 2(2), type 1, for `ℓ = 3`: four semi-admissible paths
of lengths `1,2,3,4`.
-/
def factTwoTypeOneThree
    (C : PointedTypeOneCore G x target 3) :
    SemiAdmissiblePathFamily G x target 4 where
  start := 1
  step := 1
  admissible_step := Or.inl rfl
  start_ge_one := le_rfl
  path := ![C.pathOne, C.pathTwo (by omega),
    C.pathThree (by omega), C.pathFour (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
COY Fact 2(2), type 1, for `ℓ = 4`: five semi-admissible paths
of lengths `1,2,3,4,5`.
-/
def factTwoTypeOneFour
    (C : PointedTypeOneCore G x target 4) :
    SemiAdmissiblePathFamily G x target 5 where
  start := 1
  step := 1
  admissible_step := Or.inl rfl
  start_ge_one := le_rfl
  path := ![C.pathOne, C.pathTwo (by omega),
    C.pathThree (by omega), C.pathFour (by omega),
    C.pathFive (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
The bounded truncation of COY Fact 2(2), type 1.

For any nonempty initial segment of at most four members, a type-1
`ℓ`-core supplies `q` semi-admissible `x`--`target` paths of lengths
`1,2,...,q`.  The condition `q ≤ ℓ+1` is exactly the availability
condition for the required intermediate clique vertices.
-/
def factTwoTypeOneBounded
    (C : PointedTypeOneCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target q := by
  interval_cases q
  · exact {
      start := 1
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := le_rfl
      path := ![C.pathOne]
      length_path := by
        intro i
        fin_cases i
        simp
    }
  · exact {
      start := 1
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := le_rfl
      path := ![C.pathOne, C.pathTwo (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 1
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := le_rfl
      path := ![C.pathOne, C.pathTwo (by omega),
        C.pathThree (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 1
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := le_rfl
      path := ![C.pathOne, C.pathTwo (by omega),
        C.pathThree (by omega), C.pathFour (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }

/--
Every vertex used by the bounded type-1 catalogue is the root, the
target, or one of the enumerated remaining clique vertices.
-/
theorem factTwoTypeOneBounded_support
    (C : PointedTypeOneCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.factTwoTypeOneBounded
      hqOne hqFour hqCore).path i).walk.support) :
    z = x ∨ z = target ∨ ∃ j, z = C.other j := by
  interval_cases q <;> fin_cases i <;>
    simp [factTwoTypeOneBounded, pathOne, pathTwo,
      pathThree, pathFour] at hz ⊢
  all_goals aesop

end PointedTypeOneCore

/--
A type-2 `ℓ`-core pointed at a terminal vertex of its two-vertex
independent side.

The source core is `x ∨ S ∨ T`, with `|S| = 2`, `|T| = ℓ`, `S`
independent, and `T` a clique.  Only the edges used below are recorded;
the separation fields certify that the displayed walks are simple.
-/
structure PointedTypeTwoSCore
    (G : SimpleGraph V) (x target : V) (ℓ : ℕ) where
  /-- The other vertex of the two-element side `S`. -/
  otherS : V
  /-- The clique `T`. -/
  t : Fin ℓ ↪ V
  x_ne_target : x ≠ target
  x_ne_otherS : x ≠ otherS
  x_ne_t : ∀ i, x ≠ t i
  otherS_ne_target : otherS ≠ target
  otherS_ne_t : ∀ i, otherS ≠ t i
  t_ne_target : ∀ i, t i ≠ target
  adj_x_otherS : G.Adj x otherS
  adj_otherS_t : ∀ i, G.Adj otherS (t i)
  adj_t_target : ∀ i, G.Adj (t i) target
  adj_t : ∀ i j, i ≠ j → G.Adj (t i) (t j)

namespace PointedTypeTwoSCore

variable {G : SimpleGraph V} {x target : V} {ℓ : ℕ}

/-- The type-2 path using one clique vertex. -/
def pathThree
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, hℓ⟩
  exact SimplePath.ofVertexList [C.otherS, C.t i₀]
    (by
      simp [C.adj_x_otherS, C.adj_otherS_t,
        C.adj_t_target])
    (by
      simp [C.x_ne_otherS, C.x_ne_t,
        C.x_ne_target, C.otherS_ne_t,
        C.otherS_ne_target, C.t_ne_target])

/-- The type-2 path using two clique vertices. -/
def pathFour
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, by omega⟩
  let i₁ : Fin ℓ := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  exact SimplePath.ofVertexList
    [C.otherS, C.t i₀, C.t i₁]
    (by
      simp [C.adj_x_otherS, C.adj_otherS_t,
        C.adj_t, C.adj_t_target, i₀, i₁])
    (by
      simp [C.x_ne_otherS, C.x_ne_t,
        C.x_ne_target, C.otherS_ne_t,
        C.otherS_ne_target, C.t_ne_target,
        C.t.injective.ne h01, i₀, i₁])

/-- The type-2 path using three clique vertices. -/
def pathFive
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, by omega⟩
  let i₁ : Fin ℓ := ⟨1, by omega⟩
  let i₂ : Fin ℓ := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂]
  exact SimplePath.ofVertexList
    [C.otherS, C.t i₀, C.t i₁, C.t i₂]
    (by
      simp [C.adj_x_otherS, C.adj_otherS_t,
        C.adj_t, C.adj_t_target, i₀, i₁, i₂])
    (by
      simp [C.x_ne_otherS, C.x_ne_t,
        C.x_ne_target, C.otherS_ne_t,
        C.otherS_ne_target, C.t_ne_target,
        C.t.injective.ne h01, C.t.injective.ne h02,
        C.t.injective.ne h12, i₀, i₁, i₂])

/-- The type-2 path using four clique vertices. -/
def pathSix
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 4 ≤ ℓ) :
    SimplePath G x target := by
  let i₀ : Fin ℓ := ⟨0, by omega⟩
  let i₁ : Fin ℓ := ⟨1, by omega⟩
  let i₂ : Fin ℓ := ⟨2, by omega⟩
  let i₃ : Fin ℓ := ⟨3, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂]
  have h03 : i₀ ≠ i₃ := by simp [i₀, i₃]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂]
  have h13 : i₁ ≠ i₃ := by simp [i₁, i₃]
  have h23 : i₂ ≠ i₃ := by simp [i₂, i₃]
  exact SimplePath.ofVertexList
    [C.otherS, C.t i₀, C.t i₁, C.t i₂, C.t i₃]
    (by
      simp [C.adj_x_otherS, C.adj_otherS_t,
        C.adj_t, C.adj_t_target, i₀, i₁, i₂, i₃])
    (by
      simp [C.x_ne_otherS, C.x_ne_t,
        C.x_ne_target, C.otherS_ne_t,
        C.otherS_ne_target, C.t_ne_target,
        C.t.injective.ne h01, C.t.injective.ne h02,
        C.t.injective.ne h03, C.t.injective.ne h12,
        C.t.injective.ne h13, C.t.injective.ne h23,
        i₀, i₁, i₂, i₃])

@[simp] theorem pathThree_length
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    (C.pathThree hℓ).length = 3 := by
  simp [pathThree]

@[simp] theorem pathFour_length
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    (C.pathFour hℓ).length = 4 := by
  simp [pathFour]

@[simp] theorem pathFive_length
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    (C.pathFive hℓ).length = 5 := by
  simp [pathFive]

@[simp] theorem pathSix_length
    (C : PointedTypeTwoSCore G x target ℓ)
    (hℓ : 4 ≤ ℓ) :
    (C.pathSix hℓ).length = 6 := by
  simp [pathSix]

/--
COY Fact 2(1), type 2, for `ℓ = 2`: admissible paths of lengths
`3,4`.
-/
def factTwoTypeTwoTwo
    (C : PointedTypeTwoSCore G x target 2) :
    AdmissiblePathFamily G x target 2 where
  start := 3
  step := 1
  admissible_step := Or.inl rfl
  start_ge_two := by omega
  path := ![C.pathThree (by omega), C.pathFour (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
COY Fact 2(1), type 2, for `ℓ = 3`: admissible paths of lengths
`3,4,5`.
-/
def factTwoTypeTwoThree
    (C : PointedTypeTwoSCore G x target 3) :
    AdmissiblePathFamily G x target 3 where
  start := 3
  step := 1
  admissible_step := Or.inl rfl
  start_ge_two := by omega
  path := ![C.pathThree (by omega), C.pathFour (by omega),
    C.pathFive (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
COY Fact 2(1), type 2, for `ℓ = 4`: admissible paths of lengths
`3,4,5,6`.
-/
def factTwoTypeTwoFour
    (C : PointedTypeTwoSCore G x target 4) :
    AdmissiblePathFamily G x target 4 where
  start := 3
  step := 1
  admissible_step := Or.inl rfl
  start_ge_two := by omega
  path := ![C.pathThree (by omega), C.pathFour (by omega),
    C.pathFive (by omega), C.pathSix (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
The bounded truncation of COY Fact 2(1), type 2.

A nonempty initial segment of at most four members has exact lengths
`3,4,...,q+2`.
-/
def factTwoTypeTwoBounded
    (C : PointedTypeTwoSCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ) :
    AdmissiblePathFamily G x target q := by
  interval_cases q
  · exact {
      start := 3
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := by omega
      path := ![C.pathThree (by omega)]
      length_path := by
        intro i
        fin_cases i
        simp
    }
  · exact {
      start := 3
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := by omega
      path := ![C.pathThree (by omega), C.pathFour (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 3
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := by omega
      path := ![C.pathThree (by omega), C.pathFour (by omega),
        C.pathFive (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 3
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := by omega
      path := ![C.pathThree (by omega), C.pathFour (by omega),
        C.pathFive (by omega), C.pathSix (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }

/--
Every vertex used by the bounded type-2 catalogue to `S` is represented
by its pointed core certificate.
-/
theorem factTwoTypeTwoBounded_support
    (C : PointedTypeTwoSCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.factTwoTypeTwoBounded
      hqOne hqFour hqCore).path i).walk.support) :
    z = x ∨ z = target ∨ z = C.otherS ∨
      ∃ j, z = C.t j := by
  interval_cases q <;> fin_cases i <;>
    simp [factTwoTypeTwoBounded, pathThree, pathFour,
      pathFive, pathSix] at hz ⊢
  all_goals aesop

end PointedTypeTwoSCore

/--
A type-2 `ℓ`-core pointed at a terminal vertex of its clique side `T`.

The embedding `s` enumerates the two independent vertices and `otherT`
enumerates the `ℓ-1` clique vertices other than `target`.  The source
definition requires `ℓ ≥ 2`; this is recorded by `rank_ge_two`.  The
adjacency and separation fields are precisely those needed to certify
the paths in COY Fact 2(2).
-/
structure PointedTypeTwoTCore
    (G : SimpleGraph V) (x target : V) (ℓ : ℕ) where
  rank_ge_two : 2 ≤ ℓ
  /-- The two-vertex independent side `S`. -/
  s : Fin 2 ↪ V
  /-- The clique vertices other than `target`. -/
  otherT : Fin (ℓ - 1) ↪ V
  x_ne_target : x ≠ target
  x_ne_s : ∀ i, x ≠ s i
  x_ne_otherT : ∀ i, x ≠ otherT i
  s_ne_target : ∀ i, s i ≠ target
  otherT_ne_target : ∀ i, otherT i ≠ target
  s_ne_otherT : ∀ i j, s i ≠ otherT j
  adj_x_s : ∀ i, G.Adj x (s i)
  adj_s_target : ∀ i, G.Adj (s i) target
  adj_s_otherT : ∀ i j, G.Adj (s i) (otherT j)
  adj_otherT_target : ∀ i, G.Adj (otherT i) target
  adj_otherT : ∀ i j, i ≠ j →
    G.Adj (otherT i) (otherT j)

namespace PointedTypeTwoTCore

variable {G : SimpleGraph V} {x target : V} {ℓ : ℕ}

/-- The two-edge path `x-S-target`. -/
def pathTwo (C : PointedTypeTwoTCore G x target ℓ) :
    SimplePath G x target := by
  let s₀ : Fin 2 := 0
  exact SimplePath.ofVertexList [C.s s₀]
    (by simp [C.adj_x_s, C.adj_s_target])
    (by
      simp [C.x_ne_s, C.x_ne_target,
        C.s_ne_target])

/-- The three-edge path through one vertex of `S` and one spare vertex of `T`. -/
def pathThree (C : PointedTypeTwoTCore G x target ℓ) :
    SimplePath G x target := by
  let s₀ : Fin 2 := 0
  let t₀ : Fin (ℓ - 1) := ⟨0, by
    have := C.rank_ge_two
    omega⟩
  exact SimplePath.ofVertexList [C.s s₀, C.otherT t₀]
    (by
      simp [C.adj_x_s, C.adj_s_otherT,
        C.adj_otherT_target])
    (by
      simp [C.x_ne_s, C.x_ne_otherT,
        C.x_ne_target, C.s_ne_otherT,
        C.s_ne_target, C.otherT_ne_target])

/--
The four-edge path used in the tight `ℓ = 2` case.

It passes from the sole spare clique vertex through the second vertex of
`S`; hence it does not assume a second spare clique vertex.
-/
def pathFour (C : PointedTypeTwoTCore G x target ℓ) :
    SimplePath G x target := by
  let s₀ : Fin 2 := 0
  let s₁ : Fin 2 := 1
  let t₀ : Fin (ℓ - 1) := ⟨0, by
    have := C.rank_ge_two
    omega⟩
  have hs01 : s₀ ≠ s₁ := by simp [s₀, s₁]
  have htNeS : C.otherT t₀ ≠ C.s s₁ :=
    (C.s_ne_otherT s₁ t₀).symm
  have htAdjS : G.Adj (C.otherT t₀) (C.s s₁) :=
    (C.adj_s_otherT s₁ t₀).symm
  exact SimplePath.ofVertexList
    [C.s s₀, C.otherT t₀, C.s s₁]
    (by
      simp [C.adj_x_s, C.adj_s_otherT,
        C.adj_s_target, htAdjS])
    (by
      simp [C.x_ne_s, C.x_ne_otherT,
        C.x_ne_target, C.s_ne_otherT,
        C.s_ne_target, C.otherT_ne_target,
        C.s.injective.ne hs01, htNeS, s₀, s₁, t₀])

/--
The five-edge path available when `ℓ ≥ 3`.

It uses two spare clique vertices and both vertices of `S`.
-/
def pathFive
    (C : PointedTypeTwoTCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    SimplePath G x target := by
  let s₀ : Fin 2 := 0
  let s₁ : Fin 2 := 1
  let t₀ : Fin (ℓ - 1) := ⟨0, by omega⟩
  let t₁ : Fin (ℓ - 1) := ⟨1, by omega⟩
  have hs01 : s₀ ≠ s₁ := by simp [s₀, s₁]
  have ht01 : t₀ ≠ t₁ := by simp [t₀, t₁]
  have htNeS : ∀ i j, C.otherT i ≠ C.s j :=
    fun i j => (C.s_ne_otherT j i).symm
  have htAdjS : ∀ i j, G.Adj (C.otherT i) (C.s j) :=
    fun i j => (C.adj_s_otherT j i).symm
  exact SimplePath.ofVertexList
    [C.s s₀, C.otherT t₀, C.otherT t₁, C.s s₁]
    (by
      simp [C.adj_x_s, C.adj_s_otherT,
        C.adj_otherT, C.adj_s_target, htAdjS,
        t₀, t₁])
    (by
      simp [C.x_ne_s, C.x_ne_otherT,
        C.x_ne_target, C.s_ne_otherT,
        C.s_ne_target, C.otherT_ne_target,
        C.s.injective.ne hs01,
        C.otherT.injective.ne ht01, htNeS,
        s₀, s₁, t₀, t₁])

@[simp] theorem pathTwo_length
    (C : PointedTypeTwoTCore G x target ℓ) :
    C.pathTwo.length = 2 := by
  simp [pathTwo]

@[simp] theorem pathThree_length
    (C : PointedTypeTwoTCore G x target ℓ) :
    C.pathThree.length = 3 := by
  simp [pathThree]

@[simp] theorem pathFour_length
    (C : PointedTypeTwoTCore G x target ℓ) :
    C.pathFour.length = 4 := by
  simp [pathFour]

@[simp] theorem pathFive_length
    (C : PointedTypeTwoTCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    (C.pathFive hℓ).length = 5 := by
  simp [pathFive]

/--
The bounded target-in-`T` case of COY Fact 2(2).

For `1 ≤ q ≤ 4` and `q ≤ ℓ+1`, a pointed type-2 core supplies `q`
semi-admissible paths of exact lengths `2,3,...,q+1`.  When
`q = 3` and `ℓ = 2`, `pathFour` uses both vertices of `S`, so the
construction remains valid at the sharp lower bound.
-/
def factTwoTypeTwoTBounded
    (C : PointedTypeTwoTCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target q := by
  interval_cases q
  · exact {
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := by omega
      path := ![C.pathTwo]
      length_path := by
        intro i
        fin_cases i
        simp
    }
  · exact {
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := by omega
      path := ![C.pathTwo, C.pathThree]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := by omega
      path := ![C.pathTwo, C.pathThree, C.pathFour]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_one := by omega
      path := ![C.pathTwo, C.pathThree, C.pathFour,
        C.pathFive (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }

/--
Every vertex used by the bounded type-2 catalogue to `T` is represented
by its pointed core certificate.
-/
theorem factTwoTypeTwoTBounded_support
    (C : PointedTypeTwoTCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.factTwoTypeTwoTBounded
      hqOne hqFour hqCore).path i).walk.support) :
    z = x ∨ z = target ∨ (∃ j, z = C.s j) ∨
      ∃ j, z = C.otherT j := by
  interval_cases q <;> fin_cases i <;>
    simp [factTwoTypeTwoTBounded, pathTwo, pathThree,
      pathFour, pathFive] at hz ⊢
  all_goals aesop

end PointedTypeTwoTCore

/--
A type-3 `ℓ`-core pointed at a terminal vertex of its `T` side.

The embedding `s` enumerates the independent set `S` of order `ℓ`,
while `otherT` supplies `ℓ` vertices of `T` other than `target`.
No deleted vertex is part of the certificate: the same data can
therefore be obtained inside the full core or after deletion of some
further `T`-vertex.  The fields record exactly the separation and
complete-bipartite adjacencies used by COY Fact 2(2).
-/
structure PointedTypeThreeTCore
    (G : SimpleGraph V) (x target : V) (ℓ : ℕ) where
  /-- The independent side `S`. -/
  s : Fin ℓ ↪ V
  /-- Spare vertices of `T`, disjoint from `target`. -/
  otherT : Fin ℓ ↪ V
  x_ne_target : x ≠ target
  x_ne_s : ∀ i, x ≠ s i
  x_ne_otherT : ∀ i, x ≠ otherT i
  s_ne_target : ∀ i, s i ≠ target
  otherT_ne_target : ∀ i, otherT i ≠ target
  s_ne_otherT : ∀ i j, s i ≠ otherT j
  adj_x_target : G.Adj x target
  adj_x_otherT : ∀ i, G.Adj x (otherT i)
  adj_otherT_s : ∀ i j, G.Adj (otherT i) (s j)
  adj_s_target : ∀ i, G.Adj (s i) target

namespace PointedTypeThreeTCore

variable {G : SimpleGraph V} {x target : V} {ℓ : ℕ}

/-- The direct path from the join vertex to the selected vertex of `T`. -/
def pathOne (C : PointedTypeThreeTCore G x target ℓ) :
    SimplePath G x target :=
  SimplePath.ofAdj C.adj_x_target

/-- The first nontrivial alternating path, of length three. -/
def pathThree
    (C : PointedTypeThreeTCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    SimplePath G x target := by
  let t₀ : Fin ℓ := ⟨0, hℓ⟩
  let s₀ : Fin ℓ := ⟨0, hℓ⟩
  have htNeS : C.otherT t₀ ≠ C.s s₀ :=
    (C.s_ne_otherT s₀ t₀).symm
  exact SimplePath.ofVertexList [C.otherT t₀, C.s s₀]
    (by
      simp [C.adj_x_otherT, C.adj_otherT_s,
        C.adj_s_target])
    (by
      simp [C.x_ne_otherT, C.x_ne_s,
        C.x_ne_target, C.otherT_ne_target,
        C.s_ne_target, htNeS])

/-- The five-edge alternating path through two vertices of each side. -/
def pathFive
    (C : PointedTypeThreeTCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    SimplePath G x target := by
  let t₀ : Fin ℓ := ⟨0, by omega⟩
  let t₁ : Fin ℓ := ⟨1, by omega⟩
  let s₀ : Fin ℓ := ⟨0, by omega⟩
  let s₁ : Fin ℓ := ⟨1, by omega⟩
  have ht01 : t₀ ≠ t₁ := by simp [t₀, t₁]
  have hs01 : s₀ ≠ s₁ := by simp [s₀, s₁]
  have htNeS : ∀ i j, C.otherT i ≠ C.s j :=
    fun i j => (C.s_ne_otherT j i).symm
  have hsAdjT : ∀ i j, G.Adj (C.s i) (C.otherT j) :=
    fun i j => (C.adj_otherT_s j i).symm
  exact SimplePath.ofVertexList
    [C.otherT t₀, C.s s₀, C.otherT t₁, C.s s₁]
    (by
      simp [C.adj_x_otherT, C.adj_otherT_s,
        C.adj_s_target, hsAdjT])
    (by
      simp [C.x_ne_otherT, C.x_ne_s,
        C.x_ne_target, C.otherT_ne_target,
        C.s_ne_target, C.s_ne_otherT, htNeS,
        C.otherT.injective.ne ht01,
        C.s.injective.ne hs01,
        t₀, t₁, s₀, s₁])

/-- The seven-edge alternating path through three vertices of each side. -/
def pathSeven
    (C : PointedTypeThreeTCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    SimplePath G x target := by
  let t₀ : Fin ℓ := ⟨0, by omega⟩
  let t₁ : Fin ℓ := ⟨1, by omega⟩
  let t₂ : Fin ℓ := ⟨2, by omega⟩
  let s₀ : Fin ℓ := ⟨0, by omega⟩
  let s₁ : Fin ℓ := ⟨1, by omega⟩
  let s₂ : Fin ℓ := ⟨2, by omega⟩
  have ht01 : t₀ ≠ t₁ := by simp [t₀, t₁]
  have ht02 : t₀ ≠ t₂ := by simp [t₀, t₂]
  have ht12 : t₁ ≠ t₂ := by simp [t₁, t₂]
  have hs01 : s₀ ≠ s₁ := by simp [s₀, s₁]
  have hs02 : s₀ ≠ s₂ := by simp [s₀, s₂]
  have hs12 : s₁ ≠ s₂ := by simp [s₁, s₂]
  have htNeS : ∀ i j, C.otherT i ≠ C.s j :=
    fun i j => (C.s_ne_otherT j i).symm
  have hsAdjT : ∀ i j, G.Adj (C.s i) (C.otherT j) :=
    fun i j => (C.adj_otherT_s j i).symm
  exact SimplePath.ofVertexList
    [C.otherT t₀, C.s s₀, C.otherT t₁,
      C.s s₁, C.otherT t₂, C.s s₂]
    (by
      simp [C.adj_x_otherT, C.adj_otherT_s,
        C.adj_s_target, hsAdjT])
    (by
      simp [C.x_ne_otherT, C.x_ne_s,
        C.x_ne_target, C.otherT_ne_target,
        C.s_ne_target, C.s_ne_otherT, htNeS,
        C.otherT.injective.ne ht01,
        C.otherT.injective.ne ht02,
        C.otherT.injective.ne ht12,
        C.s.injective.ne hs01, C.s.injective.ne hs02,
        C.s.injective.ne hs12,
        t₀, t₁, t₂, s₀, s₁, s₂])

@[simp] theorem pathOne_length
    (C : PointedTypeThreeTCore G x target ℓ) :
    C.pathOne.length = 1 := by
  simp [pathOne]

@[simp] theorem pathThree_length
    (C : PointedTypeThreeTCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    (C.pathThree hℓ).length = 3 := by
  simp [pathThree]

@[simp] theorem pathFive_length
    (C : PointedTypeThreeTCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    (C.pathFive hℓ).length = 5 := by
  simp [pathFive]

@[simp] theorem pathSeven_length
    (C : PointedTypeThreeTCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    (C.pathSeven hℓ).length = 7 := by
  simp [pathSeven]

/--
The bounded target-in-`T` case of COY Fact 2(2), type 3.

For `1 ≤ q ≤ 4` and `q ≤ ℓ+1`, the selected initial segment has
exact lengths `1,3,...,2q-1`.
-/
def factTwoTypeThreeTBounded
    (C : PointedTypeThreeTCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1) :
    SemiAdmissiblePathFamily G x target q := by
  interval_cases q
  · exact {
      start := 1
      step := 2
      admissible_step := Or.inr rfl
      start_ge_one := le_rfl
      path := ![C.pathOne]
      length_path := by
        intro i
        fin_cases i
        simp
    }
  · exact {
      start := 1
      step := 2
      admissible_step := Or.inr rfl
      start_ge_one := le_rfl
      path := ![C.pathOne, C.pathThree (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 1
      step := 2
      admissible_step := Or.inr rfl
      start_ge_one := le_rfl
      path := ![C.pathOne, C.pathThree (by omega),
        C.pathFive (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 1
      step := 2
      admissible_step := Or.inr rfl
      start_ge_one := le_rfl
      path := ![C.pathOne, C.pathThree (by omega),
        C.pathFive (by omega), C.pathSeven (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }

/--
Every vertex used by the bounded type-3 catalogue to `T` is represented
by its pointed core certificate.
-/
theorem factTwoTypeThreeTBounded_support
    (C : PointedTypeThreeTCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ + 1)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.factTwoTypeThreeTBounded
      hqOne hqFour hqCore).path i).walk.support) :
    z = x ∨ z = target ∨ (∃ j, z = C.s j) ∨
      ∃ j, z = C.otherT j := by
  interval_cases q <;> fin_cases i <;>
    simp [factTwoTypeThreeTBounded, pathOne, pathThree,
      pathFive, pathSeven] at hz ⊢
  all_goals aesop

end PointedTypeThreeTCore

/--
A type-3 `ℓ`-core pointed at a terminal vertex of `S`, after one
specified vertex of `T` has been deleted.

The embedding `otherS` enumerates `S \\ {target}` and `t` enumerates
`ℓ` surviving vertices of `T`.  This is the exact amount of vertex data
used by COY Fact 2(1) to build paths of lengths `2,4,...,2ℓ`.
-/
structure PointedTypeThreeSCore
    (G : SimpleGraph V) (x target : V) (ℓ : ℕ) where
  /-- The vertices of `S` other than `target`. -/
  otherS : Fin (ℓ - 1) ↪ V
  /-- Surviving vertices of `T`; the deleted vertex is not represented. -/
  t : Fin ℓ ↪ V
  x_ne_target : x ≠ target
  x_ne_otherS : ∀ i, x ≠ otherS i
  x_ne_t : ∀ i, x ≠ t i
  target_ne_otherS : ∀ i, target ≠ otherS i
  target_ne_t : ∀ i, target ≠ t i
  otherS_ne_t : ∀ i j, otherS i ≠ t j
  adj_x_t : ∀ i, G.Adj x (t i)
  adj_t_target : ∀ i, G.Adj (t i) target
  adj_t_otherS : ∀ i j, G.Adj (t i) (otherS j)

namespace PointedTypeThreeSCore

variable {G : SimpleGraph V} {x target : V} {ℓ : ℕ}

/-- The first alternating path in a pointed type-3 core. -/
def pathTwo
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    SimplePath G x target := by
  let t₀ : Fin ℓ := ⟨0, hℓ⟩
  have htTarget : C.t t₀ ≠ target :=
    (C.target_ne_t t₀).symm
  exact SimplePath.ofVertexList [C.t t₀]
    (by simp [C.adj_x_t, C.adj_t_target])
    (by
      simp [C.x_ne_t, C.x_ne_target, htTarget])

/-- The four-edge alternating path in a pointed type-3 core. -/
def pathFour
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    SimplePath G x target := by
  let t₀ : Fin ℓ := ⟨0, by omega⟩
  let t₁ : Fin ℓ := ⟨1, by omega⟩
  let s₀ : Fin (ℓ - 1) := ⟨0, by omega⟩
  have ht01 : t₀ ≠ t₁ := by simp [t₀, t₁]
  have htTarget : ∀ i, C.t i ≠ target :=
    fun i => (C.target_ne_t i).symm
  have hsTarget : C.otherS s₀ ≠ target :=
    (C.target_ne_otherS s₀).symm
  have htNeS : ∀ i, C.t i ≠ C.otherS s₀ :=
    fun i => (C.otherS_ne_t s₀ i).symm
  have hsAdjT : ∀ i, G.Adj (C.otherS s₀) (C.t i) :=
    fun i => (C.adj_t_otherS i s₀).symm
  exact SimplePath.ofVertexList
    [C.t t₀, C.otherS s₀, C.t t₁]
    (by
      simp [C.adj_x_t, C.adj_t_otherS,
        C.adj_t_target, hsAdjT])
    (by
      simp [C.x_ne_t, C.x_ne_otherS,
        C.x_ne_target, C.otherS_ne_t, htNeS, htTarget, hsTarget,
        C.t.injective.ne ht01, t₀, t₁, s₀])

/-- The six-edge alternating path in a pointed type-3 core. -/
def pathSix
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    SimplePath G x target := by
  let t₀ : Fin ℓ := ⟨0, by omega⟩
  let t₁ : Fin ℓ := ⟨1, by omega⟩
  let t₂ : Fin ℓ := ⟨2, by omega⟩
  let s₀ : Fin (ℓ - 1) := ⟨0, by omega⟩
  let s₁ : Fin (ℓ - 1) := ⟨1, by omega⟩
  have ht01 : t₀ ≠ t₁ := by simp [t₀, t₁]
  have ht02 : t₀ ≠ t₂ := by simp [t₀, t₂]
  have ht12 : t₁ ≠ t₂ := by simp [t₁, t₂]
  have hs01 : s₀ ≠ s₁ := by simp [s₀, s₁]
  have htTarget : ∀ i, C.t i ≠ target :=
    fun i => (C.target_ne_t i).symm
  have hsTarget : ∀ i, C.otherS i ≠ target :=
    fun i => (C.target_ne_otherS i).symm
  have htNeS : ∀ i j, C.t i ≠ C.otherS j :=
    fun i j => (C.otherS_ne_t j i).symm
  have hsAdjT : ∀ j i, G.Adj (C.otherS j) (C.t i) :=
    fun j i => (C.adj_t_otherS i j).symm
  exact SimplePath.ofVertexList
    [C.t t₀, C.otherS s₀, C.t t₁,
      C.otherS s₁, C.t t₂]
    (by
      simp [C.adj_x_t, C.adj_t_otherS,
        C.adj_t_target, hsAdjT])
    (by
      simp [C.x_ne_t, C.x_ne_otherS,
        C.x_ne_target, C.otherS_ne_t, htNeS, htTarget, hsTarget,
        C.t.injective.ne ht01, C.t.injective.ne ht02,
        C.t.injective.ne ht12,
        C.otherS.injective.ne hs01,
        t₀, t₁, t₂, s₀, s₁])

/-- The eight-edge alternating path in a pointed type-3 core. -/
def pathEight
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 4 ≤ ℓ) :
    SimplePath G x target := by
  let t₀ : Fin ℓ := ⟨0, by omega⟩
  let t₁ : Fin ℓ := ⟨1, by omega⟩
  let t₂ : Fin ℓ := ⟨2, by omega⟩
  let t₃ : Fin ℓ := ⟨3, by omega⟩
  let s₀ : Fin (ℓ - 1) := ⟨0, by omega⟩
  let s₁ : Fin (ℓ - 1) := ⟨1, by omega⟩
  let s₂ : Fin (ℓ - 1) := ⟨2, by omega⟩
  have ht01 : t₀ ≠ t₁ := by simp [t₀, t₁]
  have ht02 : t₀ ≠ t₂ := by simp [t₀, t₂]
  have ht03 : t₀ ≠ t₃ := by simp [t₀, t₃]
  have ht12 : t₁ ≠ t₂ := by simp [t₁, t₂]
  have ht13 : t₁ ≠ t₃ := by simp [t₁, t₃]
  have ht23 : t₂ ≠ t₃ := by simp [t₂, t₃]
  have hs01 : s₀ ≠ s₁ := by simp [s₀, s₁]
  have hs02 : s₀ ≠ s₂ := by simp [s₀, s₂]
  have hs12 : s₁ ≠ s₂ := by simp [s₁, s₂]
  have htTarget : ∀ i, C.t i ≠ target :=
    fun i => (C.target_ne_t i).symm
  have hsTarget : ∀ i, C.otherS i ≠ target :=
    fun i => (C.target_ne_otherS i).symm
  have htNeS : ∀ i j, C.t i ≠ C.otherS j :=
    fun i j => (C.otherS_ne_t j i).symm
  have hsAdjT : ∀ j i, G.Adj (C.otherS j) (C.t i) :=
    fun j i => (C.adj_t_otherS i j).symm
  exact SimplePath.ofVertexList
    [C.t t₀, C.otherS s₀, C.t t₁,
      C.otherS s₁, C.t t₂, C.otherS s₂, C.t t₃]
    (by
      simp [C.adj_x_t, C.adj_t_otherS,
        C.adj_t_target, hsAdjT])
    (by
      simp [C.x_ne_t, C.x_ne_otherS,
        C.x_ne_target, C.otherS_ne_t, htNeS, htTarget, hsTarget,
        C.t.injective.ne ht01, C.t.injective.ne ht02,
        C.t.injective.ne ht03, C.t.injective.ne ht12,
        C.t.injective.ne ht13, C.t.injective.ne ht23,
        C.otherS.injective.ne hs01,
        C.otherS.injective.ne hs02,
        C.otherS.injective.ne hs12,
        t₀, t₁, t₂, t₃, s₀, s₁, s₂])

@[simp] theorem pathTwo_length
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 1 ≤ ℓ) :
    (C.pathTwo hℓ).length = 2 := by
  simp [pathTwo]

@[simp] theorem pathFour_length
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 2 ≤ ℓ) :
    (C.pathFour hℓ).length = 4 := by
  simp [pathFour]

@[simp] theorem pathSix_length
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 3 ≤ ℓ) :
    (C.pathSix hℓ).length = 6 := by
  simp [pathSix]

@[simp] theorem pathEight_length
    (C : PointedTypeThreeSCore G x target ℓ)
    (hℓ : 4 ≤ ℓ) :
    (C.pathEight hℓ).length = 8 := by
  simp [pathEight]

/--
COY Fact 2(1), type 3, for `ℓ = 2`: admissible paths of lengths
`2,4`, after deletion of the represented excluded `T`-vertex.
-/
def factTwoTypeThreeTwo
    (C : PointedTypeThreeSCore G x target 2) :
    AdmissiblePathFamily G x target 2 where
  start := 2
  step := 2
  admissible_step := Or.inr rfl
  start_ge_two := le_rfl
  path := ![C.pathTwo (by omega), C.pathFour (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
COY Fact 2(1), type 3, for `ℓ = 3`: admissible paths of lengths
`2,4,6`.
-/
def factTwoTypeThreeThree
    (C : PointedTypeThreeSCore G x target 3) :
    AdmissiblePathFamily G x target 3 where
  start := 2
  step := 2
  admissible_step := Or.inr rfl
  start_ge_two := le_rfl
  path := ![C.pathTwo (by omega), C.pathFour (by omega),
    C.pathSix (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
COY Fact 2(1), type 3, for `ℓ = 4`: admissible paths of lengths
`2,4,6,8`.
-/
def factTwoTypeThreeFour
    (C : PointedTypeThreeSCore G x target 4) :
    AdmissiblePathFamily G x target 4 where
  start := 2
  step := 2
  admissible_step := Or.inr rfl
  start_ge_two := le_rfl
  path := ![C.pathTwo (by omega), C.pathFour (by omega),
    C.pathSix (by omega), C.pathEight (by omega)]
  length_path := by
    intro i
    fin_cases i <;> simp

/--
The bounded truncation of COY Fact 2(1), type 3.

A nonempty initial segment of at most four members has exact lengths
`2,4,...,2q`.
-/
def factTwoTypeThreeBounded
    (C : PointedTypeThreeSCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ) :
    AdmissiblePathFamily G x target q := by
  interval_cases q
  · exact {
      start := 2
      step := 2
      admissible_step := Or.inr rfl
      start_ge_two := le_rfl
      path := ![C.pathTwo (by omega)]
      length_path := by
        intro i
        fin_cases i
        simp
    }
  · exact {
      start := 2
      step := 2
      admissible_step := Or.inr rfl
      start_ge_two := le_rfl
      path := ![C.pathTwo (by omega), C.pathFour (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 2
      step := 2
      admissible_step := Or.inr rfl
      start_ge_two := le_rfl
      path := ![C.pathTwo (by omega), C.pathFour (by omega),
        C.pathSix (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }
  · exact {
      start := 2
      step := 2
      admissible_step := Or.inr rfl
      start_ge_two := le_rfl
      path := ![C.pathTwo (by omega), C.pathFour (by omega),
        C.pathSix (by omega), C.pathEight (by omega)]
      length_path := by
        intro i
        fin_cases i <;> simp
    }

/--
Every vertex used by the bounded type-3 catalogue to `S` is represented
by its pointed core certificate.
-/
theorem factTwoTypeThreeBounded_support
    (C : PointedTypeThreeSCore G x target ℓ)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hqCore : q ≤ ℓ)
    (i : Fin q) (z : V)
    (hz : z ∈ ((C.factTwoTypeThreeBounded
      hqOne hqFour hqCore).path i).walk.support) :
    z = x ∨ z = target ∨ (∃ j, z = C.otherS j) ∨
      ∃ j, z = C.t j := by
  interval_cases q <;> fin_cases i <;>
    simp [factTwoTypeThreeBounded, pathTwo, pathFour,
      pathSix, pathEight] at hz ⊢
  all_goals aesop

end PointedTypeThreeSCore

end COY

end DeanK5
