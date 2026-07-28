import DeanK5.COYCoreAdapters

/-!
# Bounded COY core inequalities

These lemmas isolate the numerical content of COY Fact 3.  A fixed
connector from a selected core vertex to the second root, together with a
large enough bounded Fact 2 catalogue, would produce the forbidden rooted
path family by Fact 1.  Therefore the relevant core catalogue must be
smaller than `q`.

The remaining component argument must supply the connector and its
support-disjointness certificate; no informal path concatenation is used
here.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/--
If every hypothesized `q`-term inner catalogue can be joined to one fixed
outer path, then absence of `q` admissible root paths forces the catalogue
capacity `n` to be smaller than `q`.
-/
theorem catalog_capacity_lt_of_no_paths
    {G : SimpleGraph V} {x y u : V} {q n : ℕ}
    (hq : 1 ≤ q)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (outer : SimplePath G u y)
    (catalog :
      q ≤ n → SemiAdmissiblePathFamily G x u q)
    (havoid : ∀ hcapacity i,
      ((catalog hcapacity).path i).walk.support.Disjoint
        outer.walk.support.tail)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    n < q := by
  by_contra hcapacity
  have hqn : q ≤ n := Nat.le_of_not_gt hcapacity
  exact hno
    (fact_one_single_outer hq hxy hxu hyu outer
      (catalog hqn) (havoid hqn))

namespace TypeOneCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x y : V} {ℓ q : ℕ}

/-- The `T`-attachment case gives the stronger bound `ℓ+1 < q`. -/
theorem rank_add_one_lt_of_no_paths_to_t
    (C : TypeOneCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hxy : x ≠ y) (hyTarget : y ≠ target)
    (outer : SimplePath G target y)
    (havoid : ∀ hcapacity i,
      ((C.semiAdmissiblePathsTo target htarget q
        hqOne hqFour hcapacity).path i).walk.support.Disjoint
          outer.walk.support.tail)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ + 1 < q := by
  refine catalog_capacity_lt_of_no_paths
    (G := G) (x := x) (y := y) (u := target)
    (q := q) (n := ℓ + 1)
    hqOne hxy ?_ hyTarget outer
    (fun hcapacity =>
      C.semiAdmissiblePathsTo target htarget q
        hqOne hqFour hcapacity)
    havoid hno
  intro h
  apply C.root_not_mem
  simpa [h] using htarget

end TypeOneCore

namespace TypeTwoCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x y : V} {ℓ q : ℕ}

/-- An attachment in `S` forces `ℓ < q`. -/
theorem rank_lt_of_no_paths_to_s
    (C : TypeTwoCore G x ℓ)
    (target : V) (htarget : target ∈ C.S)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hxy : x ≠ y) (hyTarget : y ≠ target)
    (outer : SimplePath G target y)
    (havoid : ∀ hcapacity i,
      ((SemiAdmissiblePathFamily.ofAdmissible
        (C.admissiblePathsToS target htarget q
          hqOne hqFour hcapacity)).path i
        ).walk.support.Disjoint outer.walk.support.tail)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ < q := by
  refine catalog_capacity_lt_of_no_paths
    (G := G) (x := x) (y := y) (u := target)
    (q := q) (n := ℓ)
    hqOne hxy ?_ hyTarget outer
    (fun hcapacity =>
      SemiAdmissiblePathFamily.ofAdmissible
      (C.admissiblePathsToS target htarget q
        hqOne hqFour hcapacity))
    havoid hno
  intro h
  apply C.root_not_mem_S
  simpa [h] using htarget

/-- An attachment in `T` forces the stronger bound `ℓ+1 < q`. -/
theorem rank_add_one_lt_of_no_paths_to_t
    (C : TypeTwoCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hxy : x ≠ y) (hyTarget : y ≠ target)
    (outer : SimplePath G target y)
    (havoid : ∀ hcapacity i,
      ((C.semiAdmissiblePathsToT target htarget q
        hqOne hqFour hcapacity).path i).walk.support.Disjoint
          outer.walk.support.tail)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ + 1 < q := by
  refine catalog_capacity_lt_of_no_paths
    (G := G) (x := x) (y := y) (u := target)
    (q := q) (n := ℓ + 1)
    hqOne hxy ?_ hyTarget outer
    (fun hcapacity =>
      C.semiAdmissiblePathsToT target htarget q
        hqOne hqFour hcapacity)
    havoid hno
  intro h
  apply C.root_not_mem_T
  simpa [h] using htarget

end TypeTwoCore

namespace TypeThreeCore

variable [DecidableEq V] {G : SimpleGraph V}
  {x y : V} {ℓ q : ℕ}

/-- An `S`-attachment, with one deleted `T`-vertex, forces `ℓ < q`. -/
theorem rank_lt_of_no_paths_to_s_after_deleting
    (C : TypeThreeCore G x ℓ)
    (target deleted : V)
    (htarget : target ∈ C.S)
    (hdeleted : deleted ∈ C.T)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hxy : x ≠ y) (hyTarget : y ≠ target)
    (outer : SimplePath G target y)
    (havoid : ∀ hcapacity i,
      ((SemiAdmissiblePathFamily.ofAdmissible
        (C.admissiblePathsToSAfterDeleting
          target deleted htarget hdeleted q
          hqOne hqFour hcapacity)).path i
        ).walk.support.Disjoint outer.walk.support.tail)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ < q := by
  refine catalog_capacity_lt_of_no_paths
    (G := G) (x := x) (y := y) (u := target)
    (q := q) (n := ℓ)
    hqOne hxy ?_ hyTarget outer
    (fun hcapacity =>
      SemiAdmissiblePathFamily.ofAdmissible
      (C.admissiblePathsToSAfterDeleting
        target deleted htarget hdeleted q
        hqOne hqFour hcapacity))
    havoid hno
  intro h
  apply C.root_not_mem_S
  simpa [h] using htarget

/-- A `T`-attachment forces the stronger bound `ℓ+1 < q`. -/
theorem rank_add_one_lt_of_no_paths_to_t
    (C : TypeThreeCore G x ℓ)
    (target : V) (htarget : target ∈ C.T)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hxy : x ≠ y) (hyTarget : y ≠ target)
    (outer : SimplePath G target y)
    (havoid : ∀ hcapacity i,
      ((C.semiAdmissiblePathsToT target htarget q
        hqOne hqFour hcapacity).path i).walk.support.Disjoint
          outer.walk.support.tail)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ + 1 < q := by
  refine catalog_capacity_lt_of_no_paths
    (G := G) (x := x) (y := y) (u := target)
    (q := q) (n := ℓ + 1)
    hqOne hxy ?_ hyTarget outer
    (fun hcapacity =>
      C.semiAdmissiblePathsToT target htarget q
        hqOne hqFour hcapacity)
    havoid hno
  intro h
  apply C.root_not_mem_T
  simpa [h] using htarget

end TypeThreeCore

end COY

end DeanK5
