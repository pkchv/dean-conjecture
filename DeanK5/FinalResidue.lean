import DeanK5.Published

/-!
# The final residue contradiction (paper Section 7.3)

This is the internal argument in paper Section 7.3.  Its input contains
three admissible outside paths, three interface paths with distinct residues,
and a grid of *simple-cycle* witnesses obtained by closing one path against
the other.  Requiring `SimpleCycle` here prevents a closed walk with a
repeated vertex from passing as a cycle.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
Attach one edge at each end of an outside path.  The non-membership
hypotheses explicitly rule out reuse of either interface endpoint.
-/
def SimplePath.attachEndpoints
    {G : SimpleGraph V} {x x' y' y : V}
    (P : SimplePath G x' y')
    (hxx' : G.Adj x x') (hy'y : G.Adj y' y)
    (hxy : x ≠ y)
    (hx : x ∉ P.walk.support) (hy : y ∉ P.walk.support) :
    SimplePath G x y where
  walk := (P.walk.cons hxx').concat hy'y
  isPath := (P.isPath.cons hx).concat (by
    simp [hxy.symm, hy]) hy'y

@[simp] theorem SimplePath.attachEndpoints_length
    {G : SimpleGraph V} {x x' y' y : V}
    (P : SimplePath G x' y')
    (hxx' : G.Adj x x') (hy'y : G.Adj y' y)
    (hxy : x ≠ y)
    (hx : x ∉ P.walk.support) (hy : y ∉ P.walk.support) :
    (P.attachEndpoints hxx' hy'y hxy hx hy).length = P.length + 2 := by
  simp [SimplePath.attachEndpoints, SimplePath.length]

/--
The nine cycle closures used in Section 7.3, including the exact length
identity contributed by the two attachment edges.
-/
structure FinalClosureGrid
    (G : SimpleGraph V) {x' y' x y : V}
    (outside : AdmissiblePathFamily G x' y' 3)
    (inside : Fin 3 → SimplePath G x y) where
  /-- The simple cycle obtained from each outside and inside path pair. -/
  cycle : Fin 3 → Fin 3 → SimpleCycle G
  length_cycle : ∀ i j,
    (cycle i j).length =
      (outside.path i).length + 2 + (inside j).length

/--
Construct all nine closure cycles from the two attachment edges.  The
support-disjointness premise is exactly what Mathlib needs to prove that
each closed walk is a simple cycle.
-/
def FinalClosureGrid.ofAttachments
    (G : SimpleGraph V) {x' y' x y : V}
    (outside : AdmissiblePathFamily G x' y' 3)
    (inside : Fin 3 → SimplePath G x y)
    (hxx' : G.Adj x x') (hy'y : G.Adj y' y)
    (hxy : x ≠ y)
    (hx : ∀ i, x ∉ (outside.path i).walk.support)
    (hy : ∀ i, y ∉ (outside.path i).walk.support)
    (hdisj : ∀ i j,
      ((outside.path i).attachEndpoints hxx' hy'y hxy (hx i) (hy i)).walk.support.tail.Disjoint
        (inside j).reverse.walk.support.tail) :
    FinalClosureGrid G outside inside where
  cycle i j :=
    cycleOfDisjointPaths
      ((outside.path i).attachEndpoints hxx' hy'y hxy (hx i) (hy i))
      (inside j).reverse (hdisj i j)
      (Or.inl (by
        rw [SimplePath.attachEndpoints_length]
        omega))
  length_cycle i j := by
    rw [cycleOfDisjointPaths_length,
      SimplePath.attachEndpoints_length, SimplePath.reverse_length]

/--
Paper Section 7.3: the outside `3`-term admissible family and the three
distinct interface residues force one of the nine certified simple cycles
to have length divisible by five.
-/
theorem final_residue_argument
    (G : SimpleGraph V) {x' y' x y : V}
    (outside : AdmissiblePathFamily G x' y' 3)
    (inside : Fin 3 → SimplePath G x y)
    (hres : ∀ i j, i ≠ j →
      ((inside i).length : ZMod 5) ≠ ((inside j).length : ZMod 5))
    (closures : FinalClosureGrid G outside inside) :
    HasCycleDivisibleBy G 5 := by
  let residue : Fin 3 → ZMod 5 :=
    fun j => ((inside j).length : ZMod 5)
  have hinj : Function.Injective residue := by
    intro i j hij
    by_contra hne
    exact hres i j hne hij
  let R : Finset (ZMod 5) := Finset.univ.image residue
  have hR : R.card = 3 := by
    dsimp [R]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  obtain ⟨i, r, hrR, hzero⟩ :=
    three_add_three_mod_five
      (outside.start + 2) outside.step outside.admissible_step R hR
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hrR
  refine ⟨closures.cycle i j, ?_⟩
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
  calc
    ((closures.cycle i j).length : ZMod 5) =
        ((outside.path i).length : ZMod 5) + 2 +
          ((inside j).length : ZMod 5) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using
              congrArg (fun n : ℕ => (n : ZMod 5))
                (closures.length_cycle i j)
    _ = (outside.start + 2 : ℕ) +
        (i.val : ZMod 5) * (outside.step : ZMod 5) +
          residue j := by
            rw [outside.length_path]
            simp only [residue]
            push_cast
            ring
    _ = (outside.start + 2 : ℕ) +
        (i.val : ZMod 5) * (outside.step : ZMod 5) + r := by
            rw [hj]
    _ = 0 := hzero

/--
Section 7.3 with the closure certificates constructed from attachment and
support-disjointness hypotheses.
-/
theorem final_residue_argument_of_attachments
    (G : SimpleGraph V) {x' y' x y : V}
    (outside : AdmissiblePathFamily G x' y' 3)
    (inside : Fin 3 → SimplePath G x y)
    (hres : ∀ i j, i ≠ j →
      ((inside i).length : ZMod 5) ≠ ((inside j).length : ZMod 5))
    (hxx' : G.Adj x x') (hy'y : G.Adj y' y)
    (hxy : x ≠ y)
    (hx : ∀ i, x ∉ (outside.path i).walk.support)
    (hy : ∀ i, y ∉ (outside.path i).walk.support)
    (hdisj : ∀ i j,
      ((outside.path i).attachEndpoints hxx' hy'y hxy (hx i) (hy i)).walk.support.tail.Disjoint
        (inside j).reverse.walk.support.tail) :
    HasCycleDivisibleBy G 5 :=
  final_residue_argument G outside inside hres
    (FinalClosureGrid.ofAttachments G outside inside hxx' hy'y hxy hx hy hdisj)

end DeanK5
