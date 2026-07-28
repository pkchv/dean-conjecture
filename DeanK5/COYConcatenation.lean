import DeanK5.Graph.Basic

/-!
# COY semi-admissible concatenation

This file formalizes the path-concatenation device called Fact 1 in
Chiba--Ota--Yamashita.  The graph-theoretic input is packaged as a
certificate: in particular, every inner path is required to avoid the
outer path after its joining endpoint.  Thus the concatenated objects are
constructed with `SimplePath.appendDisjoint`; simplicity is not inferred
from an informal concatenation.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/-- The first index of a provably nonempty finite family. -/
def firstFin {q : ℕ} (hq : 1 ≤ q) : Fin q :=
  ⟨0, hq⟩

/--
A semi-admissible family is an arithmetic progression of simple-path
lengths with common difference one or two and first length at least one.
It differs from `AdmissiblePathFamily` only in permitting a one-edge first
path.
-/
structure SemiAdmissiblePathFamily
    (G : SimpleGraph V) (x y : V) (q : ℕ) where
  /-- The length of the first path. -/
  start : ℕ
  /-- The common difference between consecutive path lengths. -/
  step : ℕ
  admissible_step : IsAdmissibleStep step
  start_ge_one : 1 ≤ start
  /-- The indexed simple paths. -/
  path : Fin q → SimplePath G x y
  length_path : ∀ i, (path i).length = start + i.val * step

namespace SemiAdmissiblePathFamily

/-- Forget the stronger lower bound carried by an admissible family. -/
def ofAdmissible
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : AdmissiblePathFamily G x y q) :
    SemiAdmissiblePathFamily G x y q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_one := (by omega : 1 ≤ 2).trans F.start_ge_two
  path := F.path
  length_path := F.length_path

/-- Recover an admissible family when the first semi-admissible path has
length at least two. -/
def toAdmissible
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : SemiAdmissiblePathFamily G x y q)
    (hstart : 2 ≤ F.start) :
    AdmissiblePathFamily G x y q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := hstart
  path := F.path
  length_path := F.length_path

/-- Map a semi-admissible family along an injective graph homomorphism. -/
def mapInjectiveHom
    {W : Type*} {H : SimpleGraph W}
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : SemiAdmissiblePathFamily G x y q)
    (f : G →g H) (hinj : Function.Injective f) :
    SemiAdmissiblePathFamily H (f x) (f y) q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_one := F.start_ge_one
  path i := (F.path i).mapInjectiveHom f hinj
  length_path i := by
    simp [F.length_path i]

/-- Reverse every path in a semi-admissible family. -/
def reverse
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : SemiAdmissiblePathFamily G x y q) :
    SemiAdmissiblePathFamily G y x q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_one := F.start_ge_one
  path i := (F.path i).reverse
  length_path i := by
    simp [F.length_path i]

/-- Retain the first `r` paths of a semi-admissible family. -/
def take
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : SemiAdmissiblePathFamily G x y q)
    (r : ℕ) (hr : r ≤ q) :
    SemiAdmissiblePathFamily G x y r where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_one := F.start_ge_one
  path i := F.path (Fin.castLE hr i)
  length_path i := by
    simpa using F.length_path (Fin.castLE hr i)

end SemiAdmissiblePathFamily

/--
A semi-admissible family of `(U,y)`-paths.  Each path starts at its
designated vertex of `U`, and that vertex is its unique vertex in `U`.
-/
structure SemiAdmissibleSetPathFamily
    (G : SimpleGraph V) (U : Set V) (y : V) (q : ℕ) where
  /-- The length of the first path. -/
  start : ℕ
  /-- The common difference between consecutive path lengths. -/
  step : ℕ
  admissible_step : IsAdmissibleStep step
  start_ge_one : 1 ≤ start
  /-- The unique `U`-vertex on each path. -/
  endpoint : Fin q → V
  endpoint_mem : ∀ i, endpoint i ∈ U
  /-- The indexed paths, oriented from `U` towards `y`. -/
  path : ∀ i, SimplePath G (endpoint i) y
  length_path : ∀ i, (path i).length = start + i.val * step
  unique_endpoint : ∀ i z,
    z ∈ (path i).walk.support → z ∈ U → z = endpoint i

namespace SemiAdmissibleSetPathFamily

/-- A single nontrivial path viewed as a set-path family from `{u}`. -/
def singleton
    {G : SimpleGraph V} {u y : V}
    (P : SimplePath G u y) (huy : u ≠ y) :
    SemiAdmissibleSetPathFamily G ({u} : Set V) y 1 where
  start := P.length
  step := 1
  admissible_step := Or.inl rfl
  start_ge_one := by
    have hnonzero : P.length ≠ 0 := by
      intro hzero
      exact huy (P.walk.eq_of_length_eq_zero hzero)
    omega
  endpoint _ := u
  endpoint_mem _ := by simp
  path _ := P
  length_path i := by
    fin_cases i
    simp
  unique_endpoint _ z _ hz := by
    simpa using hz

/-- Retain the first `r` paths of a semi-admissible set-path family. -/
def take
    {G : SimpleGraph V} {U : Set V} {y : V} {q : ℕ}
    (F : SemiAdmissibleSetPathFamily G U y q)
    (r : ℕ) (hr : r ≤ q) :
    SemiAdmissibleSetPathFamily G U y r where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_one := F.start_ge_one
  endpoint i := F.endpoint (Fin.castLE hr i)
  endpoint_mem i := F.endpoint_mem (Fin.castLE hr i)
  path i := F.path (Fin.castLE hr i)
  length_path i := by
    simpa using F.length_path (Fin.castLE hr i)
  unique_endpoint i z hz hU :=
    F.unique_endpoint (Fin.castLE hr i) z hz hU

end SemiAdmissibleSetPathFamily

/--
A source-faithful certificate for the hypotheses of COY Fact 1.

`avoid_outer` is the certified version of saying that the inner
`(x,uᵢ)`-paths lie in `G - (V(Pᵢ) \ {uᵢ})`.  Since the outer path is
oriented from `uᵢ` to `y`, its support tail is precisely
`V(Pᵢ) \ {uᵢ}`.  `equal_inner_length` records the source hypothesis that
the `j`th inner paths have equal orders for all `i`; for simple paths this
is equivalent to equality of their edge lengths.
-/
structure FactOneCertificate
    (G : SimpleGraph V) (x y : V) (U : Set V)
    (s t : ℕ) where
  /-- The outer family is nonempty. -/
  hs : 1 ≤ s
  /-- Every inner family is nonempty. -/
  ht : 1 ≤ t
  /-- The two ultimate roots are distinct. -/
  x_ne_y : x ≠ y
  /-- The first root lies outside the interface set. -/
  x_not_mem : x ∉ U
  /-- The second root lies outside the interface set. -/
  y_not_mem : y ∉ U
  /-- The semi-admissible family from the interface set to `y`. -/
  outer : SemiAdmissibleSetPathFamily G U y s
  /-- The semi-admissible family from `x` to each outer endpoint. -/
  inner : ∀ i, SemiAdmissiblePathFamily G x (outer.endpoint i) t
  /-- Corresponding inner paths have the same length in every family. -/
  equal_inner_length : ∀ i j,
    ((inner i).path j).length =
      ((inner (firstFin hs)).path j).length
  /--
  Each inner path avoids the outer path after their prescribed common
  endpoint, certifying that their concatenation is simple.
  -/
  avoid_outer : ∀ i j,
    ((inner i).path j).walk.support.Disjoint
      (outer.path i).walk.support.tail

namespace FactOneCertificate

variable {G : SimpleGraph V} {x y : V} {U : Set V}
  {s t : ℕ}

/-- The first inner family, used to record the common inner length list. -/
def firstInner (C : FactOneCertificate G x y U s t) :
    SemiAdmissiblePathFamily G x
      (C.outer.endpoint (firstFin C.hs)) t :=
  C.inner (firstFin C.hs)

/--
Concatenate an inner path with its corresponding outer path.  The
certificate's avoidance condition proves that the result is a simple
path.
-/
def joined (C : FactOneCertificate G x y U s t)
    (i : Fin s) (j : Fin t) :
    SimplePath G x y :=
  ((C.inner i).path j).appendDisjoint
    (C.outer.path i) (C.avoid_outer i j)

@[simp] theorem joined_length
    (C : FactOneCertificate G x y U s t)
    (i : Fin s) (j : Fin t) :
    (C.joined i j).length =
      C.outer.start + C.firstInner.start +
        i.val * C.outer.step + j.val * C.firstInner.step := by
  rw [joined, SimplePath.appendDisjoint_length,
    C.equal_inner_length i j]
  change (C.firstInner.path j).length +
      (C.outer.path i).length =
    C.outer.start + C.firstInner.start +
      i.val * C.outer.step + j.val * C.firstInner.step
  rw [(C.firstInner.length_path j),
    C.outer.length_path i]
  omega

end FactOneCertificate

/--
An arithmetic choice of pairs from an `s × t` grid.  The selected grid
entries form an arithmetic progression of length `q`.
-/
structure SumSelection
    (s t q leftStep rightStep : ℕ) where
  /-- The common difference of the selected sums. -/
  step : ℕ
  admissible_step : IsAdmissibleStep step
  /-- The selected row and column. -/
  index : Fin q → Fin s × Fin t
  sum_index : ∀ k,
    (index k).1.val * leftStep +
        (index k).2.val * rightStep =
      k.val * step

namespace SumSelection

/-- Every integer below `s+t-1` is a sum of bounded row and column indices. -/
private theorem same_step_representation
    {s t k : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hk : k < s + t - 1) :
    ∃ i < s, ∃ j < t, i + j = k := by
  by_cases hks : k < s
  · exact ⟨k, hks, 0, ht, by omega⟩
  · refine ⟨s - 1, by omega, k - (s - 1), ?_, by omega⟩
    omega

/--
When the row step is one and there are at least two rows, every integer
below `s+t-1` has the form `i+2j` in the required rectangle.
-/
private theorem one_two_representation
    {s t k : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t)
    (hk : k < s + t - 1) :
    ∃ i < s, ∃ j < t, i + 2 * j = k := by
  let j := min (k / 2) (t - 1)
  let i := k - 2 * j
  have hjt : j < t := by
    dsimp [j]
    have hle := Nat.min_le_right (k / 2) (t - 1)
    omega
  have hjdiv : j ≤ k / 2 :=
    Nat.min_le_left _ _
  have htwice : 2 * j ≤ k := by
    have hmul := Nat.mul_le_mul_left 2 hjdiv
    exact hmul.trans (Nat.mul_div_le k 2)
  have hieq : i + 2 * j = k := by
    dsimp [i]
    omega
  have his : i < s := by
    by_cases hhalf : k / 2 ≤ t - 1
    · have hj : j = k / 2 := by
        simp [j, Nat.min_eq_left hhalf]
      have hmodEq := Nat.mod_add_div k 2
      have hmodLt := Nat.mod_lt k (by omega : 0 < 2)
      dsimp [i]
      rw [hj]
      omega
    · have hle : t - 1 ≤ k / 2 :=
        (Nat.lt_of_not_ge hhalf).le
      have hj : j = t - 1 := by
        simp [j, Nat.min_eq_right hle]
      dsimp [i]
      rw [hj]
      omega
  exact ⟨i, his, j, hjt, hieq⟩

/--
The transposed bounded representation used when the row step is two and
the column step is one.
-/
private theorem two_one_representation
    {s t k : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t)
    (hk : k < s + t - 1) :
    ∃ i < s, ∃ j < t, 2 * i + j = k := by
  have hk' : k < t + s - 1 := by omega
  obtain ⟨j, hj, i, hi, heq⟩ :=
    one_two_representation (s := t) (t := s) ht hs hk'
  exact ⟨i, hi, j, hj, by omega⟩

/-- Equal admissible steps admit the usual diagonal selection. -/
theorem same_step
    {s t d : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hd : IsAdmissibleStep d) :
    Nonempty (SumSelection s t (s + t - 1) d d) := by
  classical
  choose i hi j hj hij using fun k : Fin (s + t - 1) =>
    same_step_representation hs ht k.isLt
  exact ⟨{
    step := d
    admissible_step := hd
    index := fun k => (⟨i k, hi k⟩, ⟨j k, hj k⟩)
    sum_index := by
      intro k
      rw [← Nat.add_mul, hij k]
  }⟩

/-- A `1`-step row family and a `2`-step column family. -/
theorem one_two
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    Nonempty (SumSelection s t (s + t - 1) 1 2) := by
  classical
  by_cases hsOne : s = 1
  · subst s
    exact ⟨{
      step := 2
      admissible_step := Or.inr rfl
      index := fun k =>
        (⟨0, by omega⟩, ⟨k.val, by simpa using k.isLt⟩)
      sum_index := by
        intro k
        simp
    }⟩
  · have hsTwo : 2 ≤ s := by omega
    choose i hi j hj hij using fun k : Fin (s + t - 1) =>
      one_two_representation hsTwo ht k.isLt
    exact ⟨{
      step := 1
      admissible_step := Or.inl rfl
      index := fun k => (⟨i k, hi k⟩, ⟨j k, hj k⟩)
      sum_index := by
        intro k
        simpa [Nat.mul_comm] using hij k
    }⟩

/-- A `2`-step row family and a `1`-step column family. -/
theorem two_one
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    Nonempty (SumSelection s t (s + t - 1) 2 1) := by
  classical
  by_cases htOne : t = 1
  · subst t
    exact ⟨{
      step := 2
      admissible_step := Or.inr rfl
      index := fun k =>
        (⟨k.val, by omega⟩, ⟨0, by omega⟩)
      sum_index := by
        intro k
        simp
    }⟩
  · have htTwo : 2 ≤ t := by omega
    choose i hi j hj hij using fun k : Fin (s + t - 1) =>
      two_one_representation hs htTwo k.isLt
    exact ⟨{
      step := 1
      admissible_step := Or.inl rfl
      index := fun k => (⟨i k, hi k⟩, ⟨j k, hj k⟩)
      sum_index := by
        intro k
        simpa [Nat.mul_comm] using hij k
    }⟩

/--
Any two nonempty admissible progressions have an admissible
`s+t-1`-term selection in their rectangular sum table.
-/
theorem exists_of_admissible
    {s t leftStep rightStep : ℕ}
    (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hleft : IsAdmissibleStep leftStep)
    (hright : IsAdmissibleStep rightStep) :
    Nonempty
      (SumSelection s t (s + t - 1) leftStep rightStep) := by
  rcases hleft with rfl | rfl <;>
    rcases hright with rfl | rfl
  · exact same_step hs ht (Or.inl rfl)
  · exact one_two hs ht
  · exact two_one hs ht
  · exact same_step hs ht (Or.inr rfl)

end SumSelection

/--
COY Fact 1, with every path concatenation certified simple.

The conclusion is general in the two positive family sizes, and hence in
particular covers every use producing two, three, or four paths in the
remaining COY formalization.
-/
theorem fact_one
    (C : FactOneCertificate G x y U s t) :
    Nonempty (AdmissiblePathFamily G x y (s + t - 1)) := by
  obtain ⟨selection⟩ :=
    SumSelection.exists_of_admissible
      C.hs C.ht C.outer.admissible_step
        C.firstInner.admissible_step
  exact ⟨{
    start := C.outer.start + C.firstInner.start
    step := selection.step
    admissible_step := selection.admissible_step
    start_ge_two := by
      have hout := C.outer.start_ge_one
      have hin := C.firstInner.start_ge_one
      omega
    path := fun k =>
      C.joined (selection.index k).1 (selection.index k).2
    length_path := by
      intro k
      rw [C.joined_length]
      have hsum := selection.sum_index k
      omega
  }⟩

/--
The one-outer-path specialization of COY Fact 1.

This is the form used in COY Fact 3: a fixed connector from a core
endpoint `u` to `y` is concatenated with every member of a
semi-admissible `x`--`u` family.  The explicit support condition certifies
that each result is a simple path.
-/
theorem fact_one_single_outer
    {q : ℕ} (hq : 1 ≤ q)
    {u : V}
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (outer : SimplePath G u y)
    (inner : SemiAdmissiblePathFamily G x u q)
    (hdisjoint : ∀ i,
      (inner.path i).walk.support.Disjoint
        outer.walk.support.tail) :
    Nonempty (AdmissiblePathFamily G x y q) := by
  let certificate :
      FactOneCertificate G x y ({u} : Set V) 1 q := {
    hs := le_rfl
    ht := hq
    x_ne_y := hxy
    x_not_mem := by simpa using hxu
    y_not_mem := by simpa using hyu
    outer :=
      SemiAdmissibleSetPathFamily.singleton outer hyu.symm
    inner := fun _ => inner
    equal_inner_length := by
      intro i j
      fin_cases i
      rfl
    avoid_outer := by
      intro i j
      fin_cases i
      exact hdisjoint j
  }
  simpa using fact_one certificate

end COY

end DeanK5
