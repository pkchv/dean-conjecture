import DeanK5.StandingSetup
import DeanK5.FinalResidue

/-!
# Boundary-root lifting (paper Section 6.1)

This module formalizes the path-level operation in paper Lemma 6.2.
The two artificial roots are removed, the remaining path is induced onto
the old carrier, and two genuine ambient boundary edges are attached.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {U : Type u} {V : Type v}

/--
An admissible length progression whose paths may have different endpoint
pairs.  This is the precise meaning of the paper's admissible
`(S,T)`-paths after artificial boundary roots have been replaced.
-/
structure AdmissiblePathSequence
    (G : SimpleGraph V) (q : ℕ) where
  /-- The length of the first path in the sequence. -/
  start : ℕ
  /-- The common difference between successive path lengths. -/
  step : ℕ
  admissible_step : IsAdmissibleStep step
  start_ge_two : 2 ≤ start
  /-- The initial endpoint of each path. -/
  x : Fin q → V
  /-- The terminal endpoint of each path. -/
  y : Fin q → V
  endpoints_ne : ∀ i, x i ≠ y i
  /-- The simple path at each index. -/
  path : ∀ i, SimplePath G (x i) (y i)
  length_path : ∀ i, (path i).length = start + i.val * step

/--
The result of deleting the first and last edges of a simple rooted path.
The middle path is explicitly carried by the graph with both roots deleted.
It is allowed to be nil: this is precisely the paper's `u = v` case.
-/
structure TrimmedPath
    (G : SimpleGraph U) (α β : U)
    (P : SimplePath G α β) where
  /-- The first vertex of `P` after `α`. -/
  u : U
  /-- The last vertex of `P` before `β`. -/
  v : U
  u_ne_alpha : u ≠ α
  u_ne_beta : u ≠ β
  v_ne_alpha : v ≠ α
  v_ne_beta : v ≠ β
  first_adj : G.Adj α u
  last_adj : G.Adj v β
  /--
  The remaining path, viewed in the graph induced after deleting both
  roots.
  -/
  middle : SimplePath
    (G.induce {z | z ≠ α ∧ z ≠ β})
    ⟨u, u_ne_alpha, u_ne_beta⟩
    ⟨v, v_ne_alpha, v_ne_beta⟩
  length_eq : P.length = middle.length + 2

/--
Every simple path of length at least two admits the endpoint trimming
described above.  Simplicity is used both to exclude the roots from the
middle and to handle the possible one-vertex middle path.
-/
theorem trim_simple_path_endpoints
    {G : SimpleGraph U} {α β : U}
    (P : SimplePath G α β)
    (hαβ : α ≠ β)
    (hlen : 2 ≤ P.length) :
    Nonempty (TrimmedPath G α β P) := by
  obtain ⟨u, hαu, tail, hwalk⟩ :=
    P.walk.exists_eq_cons_of_ne hαβ
  have hconsPath : (SimpleGraph.Walk.cons hαu tail).IsPath := by
    have h := P.isPath
    rw [hwalk] at h
    exact h
  have htailPath : tail.IsPath := hconsPath.of_cons
  have hαTail : α ∉ tail.support :=
    (SimpleGraph.Walk.cons_isPath_iff hαu tail).1 hconsPath |>.2
  have huβ : u ≠ β := by
    intro huβ
    subst u
    have hnil : tail.Nil :=
      SimpleGraph.Walk.isPath_iff_nil.mp htailPath
    have htailZero : tail.length = 0 :=
      hnil.length_eq_zero
    have hPone : P.length = 1 := by
      simp [SimplePath.length, hwalk, htailZero]
    omega
  obtain ⟨v, hβv, middleReverse, hreverse⟩ :=
    tail.reverse.exists_eq_cons_of_ne huβ.symm
  have hreversePath :
      (SimpleGraph.Walk.cons hβv middleReverse).IsPath := by
    have h := htailPath.reverse
    rw [hreverse] at h
    exact h
  have hmiddleReversePath : middleReverse.IsPath :=
    hreversePath.of_cons
  have hβMiddleReverse : β ∉ middleReverse.support :=
    (SimpleGraph.Walk.cons_isPath_iff hβv middleReverse).1
      hreversePath |>.2
  let middleWalk := middleReverse.reverse
  have hmiddlePath : middleWalk.IsPath := by
    exact hmiddleReversePath.reverse
  have htailDecomposition :
      tail = middleWalk.append
        (SimpleGraph.Walk.cons hβv.symm .nil) := by
    have h := congrArg SimpleGraph.Walk.reverse hreverse
    simpa [middleWalk] using h
  have hmiddleSub :
      ∀ z ∈ middleWalk.support, z ∈ tail.support := by
    intro z hz
    rw [htailDecomposition]
    simp [hz]
  have hαMiddle : α ∉ middleWalk.support := by
    intro hα
    exact hαTail (hmiddleSub α hα)
  have hβMiddle : β ∉ middleWalk.support := by
    simpa [middleWalk, SimpleGraph.Walk.support_reverse] using
      hβMiddleReverse
  have huα : u ≠ α := by
    intro huα
    subst u
    exact G.loopless.irrefl α hαu
  have hvβ : v ≠ β := by
    intro hvβ
    subst v
    exact G.loopless.irrefl β hβv
  have hvα : v ≠ α := by
    intro hvα
    apply hαMiddle
    simpa [hvα] using middleWalk.end_mem_support
  have hmiddleOld :
      ∀ z ∈ middleWalk.support,
        z ∈ {z | z ≠ α ∧ z ≠ β} := by
    intro z hz
    exact ⟨fun hzα => hαMiddle (hzα ▸ hz),
      fun hzβ => hβMiddle (hzβ ▸ hz)⟩
  let middleInduced :=
    middleWalk.induce {z | z ≠ α ∧ z ≠ β} hmiddleOld
  let middle : SimplePath
      (G.induce {z | z ≠ α ∧ z ≠ β})
      ⟨u, huα, huβ⟩ ⟨v, hvα, hvβ⟩ := {
    walk := middleInduced
    isPath := by
      apply SimpleGraph.Walk.IsPath.of_map
        (f := (Embedding.induce {z | z ≠ α ∧ z ≠ β}).toHom)
      rw [SimpleGraph.Walk.map_induce]
      exact hmiddlePath
  }
  have hmiddleLength :
      middle.length = middleWalk.length := by
    have h := congrArg SimpleGraph.Walk.length
      (SimpleGraph.Walk.map_induce middleWalk hmiddleOld)
    rw [SimpleGraph.Walk.length_map] at h
    change middleInduced.length = middleWalk.length
    exact h
  have htailLength :
      tail.length = middleWalk.length + 1 := by
    rw [htailDecomposition]
    simp
  have hlengthEq : P.length = middle.length + 2 := by
    have hPtail : P.length = tail.length + 1 := by
      simp [SimplePath.length, hwalk]
    omega
  exact ⟨{
    u := u
    v := v
    u_ne_alpha := huα
    u_ne_beta := huβ
    v_ne_alpha := hvα
    v_ne_beta := hvβ
    first_adj := hαu
    last_adj := hβv.symm
    middle := middle
    length_eq := hlengthEq
  }⟩

/--
Data sufficient to replace the two artificial boundary edges of a trimmed
path by genuine ambient edges.  Non-membership in the range is the precise
condition that prevents either new endpoint from already occurring on the
mapped middle path.
-/
structure BoundaryReplacement
    {G : SimpleGraph U} {α β : U}
    {P : SimplePath G α β}
    (T : TrimmedPath G α β P)
    (B : SimpleGraph V)
    (φ : G.induce {z | z ≠ α ∧ z ≠ β} →g B) where
  /-- The genuine ambient endpoint replacing the left artificial root. -/
  x : V
  /-- The genuine ambient endpoint replacing the right artificial root. -/
  y : V
  x_ne_y : x ≠ y
  x_not_range : x ∉ Set.range φ
  y_not_range : y ∉ Set.range φ
  first_adj : B.Adj x (φ ⟨T.u, T.u_ne_alpha, T.u_ne_beta⟩)
  last_adj : B.Adj
    (φ ⟨T.v, T.v_ne_alpha, T.v_ne_beta⟩) y

/--
Replace both artificial boundary edges.  The resulting path is simple and
has exactly the same length as the original rooted path.
-/
def TrimmedPath.replaceBoundary
    {G : SimpleGraph U} {α β : U}
    {P : SimplePath G α β}
    (T : TrimmedPath G α β P)
    {B : SimpleGraph V}
    (φ : G.induce {z | z ≠ α ∧ z ≠ β} →g B)
    (hφ : Function.Injective φ)
    (R : BoundaryReplacement T B φ) :
    SimplePath B R.x R.y :=
  let middleB := T.middle.mapInjectiveHom φ hφ
  middleB.attachEndpoints
    R.first_adj R.last_adj R.x_ne_y
    (by
      intro hx
      exact R.x_not_range
        (by
          change R.x ∈ (T.middle.walk.map φ).support at hx
          rw [SimpleGraph.Walk.support_map] at hx
          obtain ⟨z, -, hz⟩ := List.mem_map.mp hx
          exact ⟨z, hz⟩))
    (by
      intro hy
      exact R.y_not_range
        (by
          change R.y ∈ (T.middle.walk.map φ).support at hy
          rw [SimpleGraph.Walk.support_map] at hy
          obtain ⟨z, -, hz⟩ := List.mem_map.mp hy
          exact ⟨z, hz⟩))

@[simp] theorem TrimmedPath.replaceBoundary_length
    {G : SimpleGraph U} {α β : U}
    {P : SimplePath G α β}
    (T : TrimmedPath G α β P)
    {B : SimpleGraph V}
    (φ : G.induce {z | z ≠ α ∧ z ≠ β} →g B)
    (hφ : Function.Injective φ)
    (R : BoundaryReplacement T B φ) :
    (T.replaceBoundary φ hφ R).length = P.length := by
  rw [TrimmedPath.replaceBoundary,
    SimplePath.attachEndpoints_length,
    SimplePath.mapInjectiveHom_length,
    T.length_eq]

theorem TrimmedPath.replaceBoundary_support_cases
    {G : SimpleGraph U} {α β : U}
    {P : SimplePath G α β}
    (T : TrimmedPath G α β P)
    {B : SimpleGraph V}
    (φ : G.induce {z | z ≠ α ∧ z ≠ β} →g B)
    (hφ : Function.Injective φ)
    (R : BoundaryReplacement T B φ)
    {z : V}
    (hz : z ∈ (T.replaceBoundary φ hφ R).walk.support) :
    z = R.x ∨ z = R.y ∨ z ∈ Set.range φ := by
  have hz' := hz
  simp only [TrimmedPath.replaceBoundary,
    SimplePath.attachEndpoints,
    SimplePath.mapInjectiveHom,
    SimpleGraph.Walk.support_concat,
    SimpleGraph.Walk.support_cons,
    List.mem_cons, List.mem_append,
    SimpleGraph.Walk.support_map] at hz'
  rcases hz' with (hzx | hmiddle) | hzy | hnil
  · exact Or.inl hzx
  · obtain ⟨w, -, hw⟩ := List.mem_map.mp hmiddle
    exact Or.inr (Or.inr ⟨w, hw⟩)
  · exact Or.inr (Or.inl hzy)
  · simp at hnil

/--
All choices needed to lift an admissible rooted family through one fixed
old-vertex embedding.  Keeping each trimmed witness and each replacement
certificate explicit prevents endpoint choices from being silently reused
between different paths.
-/
structure BoundaryFamilyReplacement
    {G : SimpleGraph U} {α β : U} {q : ℕ}
    (F : AdmissiblePathFamily G α β q)
    (B : SimpleGraph V)
    (φ : G.induce {z | z ≠ α ∧ z ≠ β} →g B) where
  /-- The endpoint-trimming certificate for each path in `F`. -/
  trimmed : ∀ i, TrimmedPath G α β (F.path i)
  /-- The boundary-replacement data for each trimmed path. -/
  replacement : ∀ i, BoundaryReplacement (trimmed i) B φ

/--
Replacing the two artificial edges in every member of an admissible rooted
family preserves the entire length progression.  Endpoints may vary with
the member, so the result is an `AdmissiblePathSequence`.
-/
def BoundaryFamilyReplacement.lift
    {G : SimpleGraph U} {α β : U} {q : ℕ}
    (F : AdmissiblePathFamily G α β q)
    {B : SimpleGraph V}
    (φ : G.induce {z | z ≠ α ∧ z ≠ β} →g B)
    (hφ : Function.Injective φ)
    (R : BoundaryFamilyReplacement F B φ) :
    AdmissiblePathSequence B q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := F.start_ge_two
  x i := (R.replacement i).x
  y i := (R.replacement i).y
  endpoints_ne i := (R.replacement i).x_ne_y
  path i :=
    (R.trimmed i).replaceBoundary φ hφ (R.replacement i)
  length_path i := by
    rw [TrimmedPath.replaceBoundary_length, F.length_path]

/--
The exact ambient data for the artificial-root clause of Lemma 6.2.
`leftEnds` and `rightEnds` are the paper's sets `L(u)` and `R(v)`.
Their vertices lie outside the old interior and differ from `c`; the final
field is exactly the required distinct-end choice for every possible first
and last old vertex.
-/
structure BoundaryRootAmbient
    [DecidableEq U]
    (H : SimpleGraph U) (α β : U)
    (Z : Finset U)
    (B : SimpleGraph V) (c : V) where
  alpha_ne_beta : α ≠ β
  alpha_not_Z : α ∉ Z
  beta_not_Z : β ∉ Z
  /--
  The homomorphism identifying the old interior with its image in the
  ambient graph.
  -/
  oldHom : H.induce {z | z ≠ α ∧ z ≠ β} →g B
  oldHom_injective : Function.Injective oldHom
  c_not_old_range : c ∉ Set.range oldHom
  c_adjacent_Z :
    ∀ (z : U) (hz : z ∈ Z),
      B.Adj c (oldHom ⟨z,
        fun h => alpha_not_Z (h ▸ hz),
        fun h => beta_not_Z (h ▸ hz)⟩)
  /-- The candidate genuine left endpoints available at each old vertex. -/
  leftEnds : {z : U // z ≠ α ∧ z ≠ β} → Finset V
  /-- The candidate genuine right endpoints available at each old vertex. -/
  rightEnds : {z : U // z ≠ α ∧ z ≠ β} → Finset V
  left_adjacent :
    ∀ u x, x ∈ leftEnds u → B.Adj x (oldHom u)
  right_adjacent :
    ∀ v y, y ∈ rightEnds v → B.Adj (oldHom v) y
  left_not_c : ∀ u x, x ∈ leftEnds u → x ≠ c
  right_not_c : ∀ v y, y ∈ rightEnds v → y ≠ c
  left_not_old_range :
    ∀ u x, x ∈ leftEnds u → x ∉ Set.range oldHom
  right_not_old_range :
    ∀ v y, y ∈ rightEnds v → y ∉ Set.range oldHom
  distinct_ends :
    ∀ u v,
      H.Adj α u.1 → H.Adj v.1 β →
      ∃ x ∈ leftEnds u, ∃ y ∈ rightEnds v, x ≠ y

namespace BoundaryRootAmbient

variable [DecidableEq U]
    {H : SimpleGraph U} {α β : U} {Z : Finset U}
    {B : SimpleGraph V} {c : V}

/-- Vertex map underlying `interiorHom`. -/
def interiorVertex
    (A : BoundaryRootAmbient H α β Z B c) :
    {z : Option U // z ≠ some α ∧ z ≠ some β} → V
  | ⟨none, _⟩ => c
  | ⟨some u, hu⟩ => A.oldHom ⟨u,
      by
        intro h
        exact hu.1 (by simp [h]),
      by
        intro h
        exact hu.2 (by simp [h])⟩

/-- Map the root-adjoined graph with both artificial roots deleted into
the ambient block. -/
def interiorHom
    (A : BoundaryRootAmbient H α β Z B c) :
    (adjoinRoot H Z).induce
      {z | z ≠ some α ∧ z ≠ some β} →g B where
  toFun := A.interiorVertex
  map_rel' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    change (adjoinRoot H Z).Adj a b at hab
    cases a with
    | none =>
        cases b with
        | none => exact False.elim hab
        | some v =>
            exact A.c_adjacent_Z v hab
    | some u =>
        cases b with
        | none =>
            exact (A.c_adjacent_Z u hab).symm
        | some v =>
            exact A.oldHom.map_rel' hab

theorem interiorHom_injective
    (A : BoundaryRootAmbient H α β Z B c) :
    Function.Injective A.interiorHom := by
  intro a b hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some v =>
          exact False.elim (A.c_not_old_range ⟨⟨v,
            fun hv => hb.1 (by simp [hv]),
            fun hv => hb.2 (by simp [hv])⟩, by
              simpa [interiorHom, interiorVertex] using hab.symm⟩)
  | some u =>
      cases b with
      | none =>
          exact False.elim (A.c_not_old_range ⟨⟨u,
            fun hu => ha.1 (by simp [hu]),
            fun hu => ha.2 (by simp [hu])⟩, by
              simpa [interiorHom, interiorVertex] using hab⟩)
      | some v =>
          apply Subtype.ext
          apply congrArg some
          exact congrArg Subtype.val (A.oldHom_injective (by
            simpa [interiorHom, interiorVertex] using hab))

theorem endpoint_not_range_interiorHom
    (A : BoundaryRootAmbient H α β Z B c)
    {x : V}
    (hc : x ≠ c)
    (hold : x ∉ Set.range A.oldHom) :
    x ∉ Set.range A.interiorHom := by
  rintro ⟨z, hz⟩
  rcases z with ⟨z, hzOld⟩
  cases z with
  | none =>
      exact hc (by
        simpa [interiorHom, interiorVertex] using hz.symm)
  | some u =>
      apply hold
      exact ⟨⟨u,
        fun hu => hzOld.1 (by simp [hu]),
        fun hu => hzOld.2 (by simp [hu])⟩, by
          simpa [interiorHom, interiorVertex] using hz⟩

/-- A boundary replacement together with the old endpoint vertices and
membership in the specified `L` and `R` sets. -/
structure ChosenBoundaryReplacement
    (A : BoundaryRootAmbient H α β Z B c)
    {P : SimplePath (adjoinRoot H Z) (some α) (some β)}
    (T : TrimmedPath (adjoinRoot H Z) (some α) (some β) P) where
  /-- The old vertex incident with the selected left endpoint. -/
  leftOld : {z : U // z ≠ α ∧ z ≠ β}
  /-- The old vertex incident with the selected right endpoint. -/
  rightOld : {z : U // z ≠ α ∧ z ≠ β}
  /-- The selected ambient boundary-replacement certificate. -/
  replacement : BoundaryReplacement T B A.interiorHom
  left_mem : replacement.x ∈ A.leftEnds leftOld
  right_mem : replacement.y ∈ A.rightEnds rightOld

/-- Choose one valid pair of genuine boundary ends for a trimmed path. -/
theorem chooseBoundaryReplacement
    (A : BoundaryRootAmbient H α β Z B c)
    {P : SimplePath (adjoinRoot H Z) (some α) (some β)}
    (T : TrimmedPath (adjoinRoot H Z) (some α) (some β) P) :
    Nonempty (ChosenBoundaryReplacement A T) := by
  classical
  cases hu : T.u with
  | none =>
      exact False.elim (A.alpha_not_Z (by
        have h := T.first_adj
        simpa [hu] using h))
  | some u =>
      cases hv : T.v with
      | none =>
          exact False.elim (A.beta_not_Z (by
            have h := T.last_adj
            simpa [hv] using h))
      | some v =>
          let uOld : {z : U // z ≠ α ∧ z ≠ β} :=
            ⟨u,
              fun h => T.u_ne_alpha (by simp [hu, h]),
              fun h => T.u_ne_beta (by simp [hu, h])⟩
          let vOld : {z : U // z ≠ α ∧ z ≠ β} :=
            ⟨v,
              fun h => T.v_ne_alpha (by simp [hv, h]),
              fun h => T.v_ne_beta (by simp [hv, h])⟩
          have hαu : H.Adj α u := by
            have h := T.first_adj
            simpa [hu] using h
          have hvβ : H.Adj v β := by
            have h := T.last_adj
            simpa [hv] using h
          obtain ⟨x, hx, y, hy, hxy⟩ :=
            A.distinct_ends uOld vOld hαu hvβ
          let R : BoundaryReplacement T B A.interiorHom := by
            refine ⟨x, y, hxy, ?_, ?_, ?_, ?_⟩
            · exact A.endpoint_not_range_interiorHom
                (A.left_not_c uOld x hx)
                (A.left_not_old_range uOld x hx)
            · exact A.endpoint_not_range_interiorHom
                (A.right_not_c vOld y hy)
                (A.right_not_old_range vOld y hy)
            · let uInterior :
                  {z : Option U //
                    z ≠ some α ∧ z ≠ some β} :=
                ⟨some u, by
                  constructor
                  · simpa using uOld.2.1
                  · simpa using uOld.2.2⟩
              have huInterior :
                  (⟨T.u, T.u_ne_alpha,
                    T.u_ne_beta⟩ :
                    {z : Option U //
                      z ≠ some α ∧ z ≠ some β}) =
                    uInterior :=
                Subtype.ext hu
              change B.Adj x
                (A.interiorVertex ⟨T.u,
                  T.u_ne_alpha, T.u_ne_beta⟩)
              rw [huInterior]
              change B.Adj x (A.oldHom uOld)
              exact A.left_adjacent uOld x hx
            · let vInterior :
                  {z : Option U //
                    z ≠ some α ∧ z ≠ some β} :=
                ⟨some v, by
                  constructor
                  · simpa using vOld.2.1
                  · simpa using vOld.2.2⟩
              have hvInterior :
                  (⟨T.v, T.v_ne_alpha,
                    T.v_ne_beta⟩ :
                    {z : Option U //
                      z ≠ some α ∧ z ≠ some β}) =
                    vInterior :=
                Subtype.ext hv
              change B.Adj
                (A.interiorVertex ⟨T.v,
                  T.v_ne_alpha, T.v_ne_beta⟩) y
              rw [hvInterior]
              change B.Adj (A.oldHom vOld) y
              exact A.right_adjacent vOld y hy
          exact ⟨{
            leftOld := uOld
            rightOld := vOld
            replacement := R
            left_mem := hx
            right_mem := hy
          }⟩

/-- The lifted sequence, retaining membership of every selected endpoint
in its represented boundary set. -/
structure BoundaryLiftedSequence
    (A : BoundaryRootAmbient H α β Z B c)
    {q : ℕ}
    (F : AdmissiblePathFamily
      (adjoinRoot H Z) (some α) (some β) q) where
  /-- The trimming and replacement data for the whole family. -/
  replacementData : BoundaryFamilyReplacement F B A.interiorHom
  /-- The old vertex incident with each selected left endpoint. -/
  leftOld : Fin q → {z : U // z ≠ α ∧ z ≠ β}
  /-- The old vertex incident with each selected right endpoint. -/
  rightOld : Fin q → {z : U // z ≠ α ∧ z ≠ β}
  left_mem : ∀ i,
    (replacementData.lift F A.interiorHom
      A.interiorHom_injective).x i ∈ A.leftEnds (leftOld i)
  right_mem : ∀ i,
    (replacementData.lift F A.interiorHom
      A.interiorHom_injective).y i ∈ A.rightEnds (rightOld i)

/--
The admissible path sequence obtained by forgetting the retained
endpoint-membership certificates.
-/
def BoundaryLiftedSequence.family
    (A : BoundaryRootAmbient H α β Z B c)
    {q : ℕ}
    {F : AdmissiblePathFamily
      (adjoinRoot H Z) (some α) (some β) q}
    (R : BoundaryLiftedSequence A F) :
    AdmissiblePathSequence B q :=
  R.replacementData.lift F A.interiorHom
    A.interiorHom_injective

theorem BoundaryLiftedSequence.support_cases
    (A : BoundaryRootAmbient H α β Z B c)
    {q : ℕ}
    {F : AdmissiblePathFamily
      (adjoinRoot H Z) (some α) (some β) q}
    (R : BoundaryLiftedSequence A F)
    (i : Fin q) {z : V}
    (hz : z ∈ ((R.family A).path i).walk.support) :
    z = (R.family A).x i ∨
      z = (R.family A).y i ∨
      z ∈ Set.range A.interiorHom := by
  exact (R.replacementData.trimmed i).replaceBoundary_support_cases
    A.interiorHom A.interiorHom_injective
    (R.replacementData.replacement i) hz

/--
The membership-preserving version of artificial-root family lifting.
-/
theorem lift_family_with_membership
    (A : BoundaryRootAmbient H α β Z B c)
    {q : ℕ}
    (F : AdmissiblePathFamily
      (adjoinRoot H Z) (some α) (some β) q) :
    Nonempty (BoundaryLiftedSequence A F) := by
  classical
  let trimmed (i : Fin q) :
      TrimmedPath (adjoinRoot H Z) (some α) (some β) (F.path i) :=
    Classical.choice (trim_simple_path_endpoints (F.path i)
      (by simpa using A.alpha_ne_beta)
      (by
        rw [F.length_path]
        exact F.start_ge_two.trans
          (Nat.le_add_right F.start (i.val * F.step))))
  let chosen (i : Fin q) : ChosenBoundaryReplacement A (trimmed i) :=
    Classical.choice (A.chooseBoundaryReplacement (trimmed i))
  let replacements :
      BoundaryFamilyReplacement F B A.interiorHom := {
    trimmed := trimmed
    replacement i := (chosen i).replacement
  }
  exact ⟨{
    replacementData := replacements
    leftOld i := (chosen i).leftOld
    rightOld i := (chosen i).rightOld
    left_mem i := by
      exact (chosen i).left_mem
    right_mem i := by
      exact (chosen i).right_mem
  }⟩

end BoundaryRootAmbient

/-- Detailed output of Lemma 6.2, retaining both the rooted family and all
selected boundary-set memberships. -/
def DetailedBoundaryRootLiftResult
    [DecidableEq U]
    (H : SimpleGraph U) (α β : U) (Z : Finset U)
    (B : SimpleGraph V) (c : V)
    (A : BoundaryRootAmbient H α β Z B c)
    (q : ℕ) : Prop :=
  ∃ F : AdmissiblePathFamily
      (adjoinRoot H Z) (some α) (some β) q,
    Nonempty (BoundaryRootAmbient.BoundaryLiftedSequence A F)

/--
Lemma 6.2, artificial-root clause.  The graph-theoretic hypotheses and both
degree bounds are passed unchanged to `root_lifting`; the resulting family
is then lifted through the explicit `L(u),R(v)` boundary data above.
-/
theorem boundary_root_lifting_artificial_detailed
    [Fintype U] [DecidableEq U]
    (q : ℕ) (H : SimpleGraph U) (D Z : Finset U)
    (α β : U)
    (hq : 1 ≤ q)
    (hαβ : α ≠ β)
    (hnotadj : ¬ H.Adj α β)
    (hconn : IsTwoConnected (H ⊔ edge α β))
    (hZD : Z ⊆ D)
    (hαZ : α ∉ Z) (hβZ : β ∉ Z)
    (hdeg : ∀ v, v ≠ α → v ≠ β → v ∉ Z →
      q + 1 ≤ finiteDegree H v)
    (hdegZ : ∀ z ∈ Z, q ≤ finiteDegree H z)
    (horder_one : Z.card = 1 → 4 ≤ Fintype.card U)
    {B : SimpleGraph V} {c : V}
    (A : BoundaryRootAmbient H α β Z B c) :
    DetailedBoundaryRootLiftResult H α β Z B c A q := by
  have lifted : RootLiftResult H Z α β q :=
    root_lifting q H D Z α β hq hαβ hnotadj hconn
      hZD hαZ hβZ hdeg hdegZ horder_one
  obtain ⟨F, -⟩ := lifted
  exact ⟨F, A.lift_family_with_membership F⟩

end DeanK5
