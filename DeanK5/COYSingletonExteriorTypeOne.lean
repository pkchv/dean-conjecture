import DeanK5.COYSingletonExterior

/-!
# The type-one singleton-exterior endgame

This file formalizes Case 1.1 of the proof of COY Theorem 3.  Once Claims
3.5 and 3.6 and Fact 3 have reduced the graph to a type-one core together
with the two roots and the exceptional vertex, the degree bound makes that
description rigid.  The resulting graph contains the required paths
explicitly.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/--
The rigidity conclusions used in the terminal type-one construction.

The equality for an ordinary clique vertex says that it is adjacent to
every vertex allowed by the terminal vertex cover.
-/
structure TypeOneSingletonRigidity
    [Fintype V] [DecidableEq V]
    {q : ℕ} {G : SimpleGraph V} {x y z : V} {ℓ : ℕ}
    (C : TypeOneCore G x ℓ) : Prop where
  card_T : C.T.card = q - 1
  exception_not_mem_T : z ∉ C.T
  exception_ne_left : z ≠ x
  exception_ne_right : z ≠ y
  three_le_q : 3 ≤ q
  saturated :
    ∀ v ∈ C.T,
      G.neighborSet v =
        (↑(C.T.erase v ∪ {x, y, z}) : Set V)

namespace TypeOneSingletonRigidity

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V} {ℓ : ℕ}
  {C : TypeOneCore G x ℓ}

/--
The explicit terminal path catalogue.  The first paths run through
successively more vertices of the clique.  The final path replaces one
clique edge by a two-edge detour through the exceptional vertex.
-/
noncomputable def admissiblePaths
    (R : TypeOneSingletonRigidity (q := q) (y := y) (z := z) C)
    (hxy : x ≠ y)
    (hneighborRight :
      G.neighborSet y = (↑C.T : Set V))
    (hqFour : q ≤ 4) :
    AdmissiblePathFamily G x y q := by
  classical
  have hqThree : 3 ≤ q := R.three_le_q
  interval_cases q
  · have hcard : C.T.card = 2 := by
      simpa using R.card_T
    let t : Fin 2 ↪ V :=
      finsetEmbeddingOfCardEq C.T hcard
    have ht (i : Fin 2) : t i ∈ C.T :=
      finsetEmbeddingOfCardEq_mem C.T hcard i
    have hxtAdj (i : Fin 2) : G.Adj x (t i) :=
      C.root_adj (t i) (ht i)
    have hxt (i : Fin 2) : x ≠ t i := (hxtAdj i).ne
    have hty (i : Fin 2) : G.Adj (t i) y := by
      apply Adj.symm
      rw [← SimpleGraph.mem_neighborSet, hneighborRight]
      exact ht i
    have htz (i : Fin 2) : G.Adj (t i) z := by
      rw [← SimpleGraph.mem_neighborSet,
        R.saturated (t i) (ht i)]
      simp
    have htiy (i : Fin 2) : t i ≠ y := (hty i).ne
    have hyt (i : Fin 2) : y ≠ t i := (htiy i).symm
    have htiz (i : Fin 2) : t i ≠ z := (htz i).ne
    have hzt (i : Fin 2) : z ≠ t i := (htiz i).symm
    have hztAdj (i : Fin 2) : G.Adj z (t i) := (htz i).symm
    have hxz : x ≠ z := R.exception_ne_left.symm
    have ht01 : t (0 : Fin 2) ≠ t (1 : Fin 2) :=
      t.injective.ne (by decide)
    have ht01Adj : G.Adj (t 0) (t 1) :=
      C.clique_T (ht 0) (ht 1) ht01
    let p₂ : SimplePath G x y :=
      SimplePath.ofVertexList [t 0]
        (by simp [hxtAdj, hty])
        (by simp [hxy, hxt, htiy])
    let p₃ : SimplePath G x y :=
      SimplePath.ofVertexList [t 0, t 1]
        (by simp [hxtAdj, ht01Adj, hty])
        (by simp [hxy, hxt, htiy, ht01])
    let p₄ : SimplePath G x y :=
      SimplePath.ofVertexList [t 0, z, t 1]
        (by simp [hxtAdj, htz, hztAdj, hty])
        (by
          simp [hxy, hxz, hxt, htiy, hzt, htiz, ht01,
            R.exception_ne_right])
    exact {
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := le_rfl
      path := ![p₂, p₃, p₄]
      length_path := by
        intro i
        fin_cases i <;>
          simp [p₂, p₃, p₄]
    }
  · have hcard : C.T.card = 3 := by
      simpa using R.card_T
    let t : Fin 3 ↪ V :=
      finsetEmbeddingOfCardEq C.T hcard
    have ht (i : Fin 3) : t i ∈ C.T :=
      finsetEmbeddingOfCardEq_mem C.T hcard i
    have hxtAdj (i : Fin 3) : G.Adj x (t i) :=
      C.root_adj (t i) (ht i)
    have hxt (i : Fin 3) : x ≠ t i := (hxtAdj i).ne
    have hty (i : Fin 3) : G.Adj (t i) y := by
      apply Adj.symm
      rw [← SimpleGraph.mem_neighborSet, hneighborRight]
      exact ht i
    have htz (i : Fin 3) : G.Adj (t i) z := by
      rw [← SimpleGraph.mem_neighborSet,
        R.saturated (t i) (ht i)]
      simp
    have htiy (i : Fin 3) : t i ≠ y := (hty i).ne
    have hyt (i : Fin 3) : y ≠ t i := (htiy i).symm
    have htiz (i : Fin 3) : t i ≠ z := (htz i).ne
    have hzt (i : Fin 3) : z ≠ t i := (htiz i).symm
    have hztAdj (i : Fin 3) : G.Adj z (t i) := (htz i).symm
    have hxz : x ≠ z := R.exception_ne_left.symm
    have ht01 : t (0 : Fin 3) ≠ t (1 : Fin 3) :=
      t.injective.ne (by decide)
    have ht02 : t (0 : Fin 3) ≠ t (2 : Fin 3) :=
      t.injective.ne (by decide)
    have ht12 : t (1 : Fin 3) ≠ t (2 : Fin 3) :=
      t.injective.ne (by decide)
    have ht01Adj : G.Adj (t 0) (t 1) :=
      C.clique_T (ht 0) (ht 1) ht01
    have ht12Adj : G.Adj (t 1) (t 2) :=
      C.clique_T (ht 1) (ht 2) ht12
    let p₂ : SimplePath G x y :=
      SimplePath.ofVertexList [t 0]
        (by simp [hxtAdj, hty])
        (by simp [hxy, hxt, htiy])
    let p₃ : SimplePath G x y :=
      SimplePath.ofVertexList [t 0, t 1]
        (by simp [hxtAdj, ht01Adj, hty])
        (by simp [hxy, hxt, htiy, ht01])
    let p₄ : SimplePath G x y :=
      SimplePath.ofVertexList [t 0, t 1, t 2]
        (by simp [hxtAdj, ht01Adj, ht12Adj, hty])
        (by simp [hxy, hxt, htiy, ht01, ht02, ht12])
    let p₅ : SimplePath G x y :=
      SimplePath.ofVertexList [t 0, t 1, z, t 2]
        (by simp [hxtAdj, ht01Adj, htz, hztAdj, hty])
        (by
          simp [hxy, hxz, hxt, htiy, hzt, htiz, ht01, ht02, ht12,
            R.exception_ne_right])
    exact {
      start := 2
      step := 1
      admissible_step := Or.inl rfl
      start_ge_two := le_rfl
      path := ![p₂, p₃, p₄, p₅]
      length_path := by
        intro i
        fin_cases i <;>
          simp [p₂, p₃, p₄, p₅]
    }

end TypeOneSingletonRigidity

namespace OptimalRootedCore

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y} {C : TypeOneCore G x O.rank}

/--
The degree-counting part of COY Case 1.1.

The hypotheses are precisely the outputs used from Claim 3.5
(`N(x)=N(y)=T`), Claim 3.6 (the terminal vertex cover), and Fact 3
(`|T|≤q-1`), together with the source observation that `T-{z}` is
nonempty.  The unmodified optimal core is identified by `hcore`.
-/
theorem typeOne_singleton_rigidity
    (M : MinimalCounterexample q G x y z)
    (O : OptimalRootedCore G x y)
    (C : TypeOneCore G x O.rank)
    (hcore : O.rooted.core = .typeOne C)
    (hneighborLeft :
      G.neighborSet x = (↑C.T : Set V))
    (hneighborRight :
      G.neighborSet y = (↑C.T : Set V))
    (hcover :
      (Finset.univ : Finset V) ⊆ C.T ∪ {x, y, z})
    (hcardUpper : C.T.card ≤ q - 1)
    (hordinary : (C.T \ {z}).Nonempty) :
    TypeOneSingletonRigidity (q := q) (y := y) (z := z) C := by
  classical
  have hxT : x ∉ C.T := C.root_not_mem
  have hyT : y ∉ C.T := by
    intro hy
    apply O.rooted.other_root_not_mem
    rw [hcore]
    simp [Core.carrier, Core.S, Core.T, hy]
  obtain ⟨v, hvOrdinary⟩ := hordinary
  have hvT : v ∈ C.T :=
    (Finset.mem_sdiff.mp hvOrdinary).1
  have hvz : v ≠ z := by
    simpa using (Finset.mem_sdiff.mp hvOrdinary).2
  have hvx : v ≠ x := by
    intro hvx
    exact hxT (hvx ▸ hvT)
  have hvy : v ≠ y := by
    intro hvy
    exact hyT (hvy ▸ hvT)
  let A : Finset V := C.T.erase v ∪ {x, y, z}
  have hneighborSubset :
      G.neighborSet v ⊆ (↑A : Set V) := by
    intro w hvw
    have hwCover := hcover (Finset.mem_univ w)
    change w ∈ C.T ∪ {x, y, z} at hwCover
    change w ∈ A
    rcases Finset.mem_union.mp hwCover with hwT | hwProtected
    · apply Finset.mem_union_left
      exact Finset.mem_erase.mpr ⟨hvw.ne.symm, hwT⟩
    · exact Finset.mem_union_right _ hwProtected
  have hdegreeUpper :
      finiteDegree G v ≤ A.card := by
    unfold finiteDegree
    calc
      (G.neighborSet v).ncard ≤ (↑A : Set V).ncard :=
        Set.ncard_le_ncard hneighborSubset
      _ = A.card := Set.ncard_coe_finset A
  have hdegreeLower :
      q + 1 ≤ finiteDegree G v :=
    M.degree_lower v hvx hvy hvz
  have heraseCard :
      (C.T.erase v).card = C.T.card - 1 :=
    Finset.card_erase_of_mem hvT
  have hTpos : 1 ≤ C.T.card :=
    Finset.card_pos.mpr ⟨v, hvT⟩
  have hqTwo : 2 ≤ q := M.two_le_q
  have hprotectedCard :
      ({x, y, z} : Finset V).card ≤ 3 := by
    have hyzCard : ({y, z} : Finset V).card ≤ 2 := by
      calc
        ({y, z} : Finset V).card ≤
            ({z} : Finset V).card + 1 :=
          Finset.card_insert_le y {z}
        _ = 2 := by simp
    calc
      ({x, y, z} : Finset V).card ≤
          ({y, z} : Finset V).card + 1 :=
        Finset.card_insert_le x {y, z}
      _ ≤ 2 + 1 := Nat.add_le_add_right hyzCard 1
      _ = 3 := rfl
  have hAcardUpper :
      A.card ≤ (C.T.erase v).card +
          ({x, y, z} : Finset V).card :=
    Finset.card_union_le (C.T.erase v) {x, y, z}
  have hcardT : C.T.card = q - 1 := by
    omega
  have hprotectedCardEq :
      ({x, y, z} : Finset V).card = 3 := by
    omega
  have hAcard : A.card = q + 1 := by
    omega
  have hinterCard :
      ((C.T.erase v) ∩ {x, y, z}).card = 0 := by
    have hunion :=
      Finset.card_union_add_card_inter
        (C.T.erase v) {x, y, z}
    change A.card +
        ((C.T.erase v) ∩ {x, y, z}).card =
          (C.T.erase v).card +
            ({x, y, z} : Finset V).card at hunion
    omega
  have hdisjoint :
      Disjoint (C.T.erase v) ({x, y, z} : Finset V) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hinterCard
  have hprotectedDistinct :
      x ≠ y ∧ x ≠ z ∧ y ≠ z := by
    constructor
    · exact M.roots_ne
    constructor
    · intro hxz
      have hsubset :
          ({x, y, z} : Finset V) ⊆ {x, y} := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        aesop
      have hpairCard : ({x, y} : Finset V).card ≤ 2 := by
        calc
          ({x, y} : Finset V).card ≤
              ({y} : Finset V).card + 1 :=
            Finset.card_insert_le x {y}
          _ = 2 := by simp
      have := Finset.card_le_card hsubset
      omega
    · intro hyz
      have hsubset :
          ({x, y, z} : Finset V) ⊆ {x, y} := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        aesop
      have hpairCard : ({x, y} : Finset V).card ≤ 2 := by
        calc
          ({x, y} : Finset V).card ≤
              ({y} : Finset V).card + 1 :=
            Finset.card_insert_le x {y}
          _ = 2 := by simp
      have := Finset.card_le_card hsubset
      omega
  have hzT : z ∉ C.T := by
    intro hzT
    have hzErase : z ∈ C.T.erase v :=
      Finset.mem_erase.mpr ⟨hvz.symm, hzT⟩
    exact (Finset.disjoint_left.mp hdisjoint
      hzErase (by simp))
  have hfullDisjoint :
      Disjoint C.T ({x, y, z} : Finset V) := by
    rw [Finset.disjoint_left]
    intro w hwT hwProtected
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwProtected
    rcases hwProtected with rfl | rfl | rfl
    · exact hxT hwT
    · exact hyT hwT
    · exact hzT hwT
  have htripleUnionCard :
      (C.T ∪ {x, y, z}).card = q + 2 := by
    rw [Finset.card_union_of_disjoint hfullDisjoint,
      hcardT, hprotectedCardEq]
    omega
  have hcardVUpper :
      Fintype.card V ≤ q + 2 := by
    rw [← Finset.card_univ, ← htripleUnionCard]
    exact Finset.card_le_card hcover
  have hqThree : 3 ≤ q := by
    have := M.five_le_card
    omega
  have hsaturated :
      ∀ w ∈ C.T,
        G.neighborSet w =
          (↑(C.T.erase w ∪ {x, y, z}) : Set V) := by
    intro w hwT
    have hwx : w ≠ x := by
      intro hwx
      exact hxT (hwx ▸ hwT)
    have hwy : w ≠ y := by
      intro hwy
      exact hyT (hwy ▸ hwT)
    have hwz : w ≠ z := by
      intro hwz
      exact hzT (hwz ▸ hwT)
    let B : Finset V := C.T.erase w ∪ {x, y, z}
    have hsubset :
        G.neighborSet w ⊆ (↑B : Set V) := by
      intro a hwa
      have haCover := hcover (Finset.mem_univ a)
      change a ∈ C.T ∪ {x, y, z} at haCover
      change a ∈ B
      rcases Finset.mem_union.mp haCover with haT | haProtected
      · apply Finset.mem_union_left
        exact Finset.mem_erase.mpr ⟨hwa.ne.symm, haT⟩
      · exact Finset.mem_union_right _ haProtected
    have heraseW :
        (C.T.erase w).card = C.T.card - 1 :=
      Finset.card_erase_of_mem hwT
    have hdisjointW :
        Disjoint (C.T.erase w) ({x, y, z} : Finset V) :=
      hfullDisjoint.mono (Finset.erase_subset _ _) (by rfl)
    have hBcard : B.card = q + 1 := by
      dsimp [B]
      rw [Finset.card_union_of_disjoint hdisjointW,
        heraseW, hcardT, hprotectedCardEq]
      omega
    apply Set.eq_of_subset_of_ncard_le hsubset
    rw [Set.ncard_coe_finset, hBcard]
    exact M.degree_lower w hwx hwy hwz
  exact {
    card_T := hcardT
    exception_not_mem_T := hzT
    exception_ne_left := hprotectedDistinct.2.1.symm
    exception_ne_right := hprotectedDistinct.2.2.symm
    three_le_q := hqThree
    saturated := hsaturated
  }

/--
COY Case 1.1: a natural optimal core of type one cannot have the stated
singleton-exterior terminal data.

The contradiction is witnessed by the explicit family of `q` simple
`x`--`y` paths of lengths `2,3,...,q+1`.
-/
theorem contradiction_of_natural_singleton_typeOne
    (M : MinimalCounterexample q G x y z)
    (O : OptimalRootedCore G x y)
    (C : TypeOneCore G x O.rank)
    (hcore : O.rooted.core = .typeOne C)
    (hneighborLeft :
      G.neighborSet x = (↑C.T : Set V))
    (hneighborRight :
      G.neighborSet y = (↑C.T : Set V))
    (hcover :
      (Finset.univ : Finset V) ⊆ C.T ∪ {x, y, z})
    (hcardUpper : C.T.card ≤ q - 1)
    (hordinary : (C.T \ {z}).Nonempty) :
    False := by
  let R :=
    typeOne_singleton_rigidity M O C hcore
      hneighborLeft hneighborRight hcover
      hcardUpper hordinary
  apply M.no_paths
  exact ⟨R.admissiblePaths M.roots_ne
    hneighborRight M.q_le_four⟩

end OptimalRootedCore

end COY

end DeanK5
