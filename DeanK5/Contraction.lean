import DeanK5.Graph.Separation

/-!
# Simple edge contraction

The contracted vertex is represented by `none`; every other vertex is
represented by `some v`, with the two contracted endpoints excluded from
the subtype.  Loops and parallel edges are suppressed by construction.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
The vertex type obtained by identifying `q` and `r` with `none` and
retaining every other vertex as `some v`.
-/
abbrev ContractPairVertex (V : Type u) (q r : V) :=
  Option {v : V // v ≠ q ∧ v ≠ r}

/-- Send `q` and `r` to the contracted vertex and retain every other vertex. -/
def contractVertex [DecidableEq V] (q r v : V) :
    ContractPairVertex V q r :=
  if hv : v = q ∨ v = r then none
  else some ⟨v, not_or.mp hv⟩

/--
Choose `q` as a representative of the contracted vertex and otherwise
return the retained original vertex.
-/
def uncontractVertex (q : V) {r : V} :
    ContractPairVertex V q r → V
  | none => q
  | some v => v.1

/--
Contract `q` and `r` in `G`, suppressing the resulting loop and any
parallel edges.
-/
def contractPair (G : SimpleGraph V) (q r : V) :
    SimpleGraph (ContractPairVertex V q r) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some v => G.Adj q v.1 ∨ G.Adj r v.1
    | some u, none => G.Adj u.1 q ∨ G.Adj u.1 r
    | some u, some v => G.Adj u.1 v.1
  symm := by
    constructor
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact hab
        | some v =>
            rcases hab with hq | hr
            · exact Or.inl hq.symm
            · exact Or.inr hr.symm
    | some u =>
        cases b with
        | none =>
            rcases hab with hq | hr
            · exact Or.inl hq.symm
            · exact Or.inr hr.symm
        | some v => exact hab.symm
  loopless := by
    constructor
    intro a
    cases a with
    | none => simp
    | some v => exact G.loopless.irrefl v.1

@[simp] theorem contractPair_adj_none_some
    (G : SimpleGraph V) (q r : V)
    (v : {v : V // v ≠ q ∧ v ≠ r}) :
    (contractPair G q r).Adj none (some v) ↔
      G.Adj q v.1 ∨ G.Adj r v.1 :=
  Iff.rfl

@[simp] theorem contractPair_adj_some_none
    (G : SimpleGraph V) (q r : V)
    (v : {v : V // v ≠ q ∧ v ≠ r}) :
    (contractPair G q r).Adj (some v) none ↔
      G.Adj v.1 q ∨ G.Adj v.1 r :=
  Iff.rfl

@[simp] theorem contractPair_adj_some_some
    (G : SimpleGraph V) (q r : V)
    (u v : {v : V // v ≠ q ∧ v ≠ r}) :
    (contractPair G q r).Adj (some u) (some v) ↔
      G.Adj u.1 v.1 :=
  Iff.rfl

@[simp] theorem contractVertex_eq_none_iff
    [DecidableEq V] (q r v : V) :
    contractVertex q r v = none ↔ v = q ∨ v = r := by
  by_cases h : v = q ∨ v = r
  · simp [contractVertex, h]
  · simp [contractVertex, h]

@[simp] theorem contractVertex_uncontractVertex
    [DecidableEq V] (q r : V)
    (v : ContractPairVertex V q r) :
    contractVertex q r (uncontractVertex q v) = v := by
  cases v with
  | none => simp [uncontractVertex, contractVertex]
  | some v =>
      simp [uncontractVertex, contractVertex, v.2.1, v.2.2]

theorem contractVertex_eq_iff
    [DecidableEq V] (q r u v : V) :
    contractVertex q r u = contractVertex q r v ↔
      u = v ∨
        ((u = q ∨ u = r) ∧ (v = q ∨ v = r)) := by
  by_cases hu : u = q ∨ u = r <;>
    by_cases hv : v = q ∨ v = r
  · simp [contractVertex, hu, hv]
  · have huv : u ≠ v := by
      intro huv
      subst v
      exact hv hu
    simp [contractVertex, hu, hv, huv]
  · have huv : u ≠ v := by
      intro huv
      subst v
      exact hu hv
    simp [contractVertex, hu, hv, huv]
  · simp [contractVertex, hu, hv, Subtype.ext_iff]

theorem contractVertex_eq_or_adj
    [DecidableEq V]
    (G : SimpleGraph V) (q r u v : V)
    (huv : G.Adj u v) :
    contractVertex q r u = contractVertex q r v ∨
      (contractPair G q r).Adj
        (contractVertex q r u) (contractVertex q r v) := by
  by_cases huq : u = q
  · subst u
    by_cases hvq : v = q
    · subst v
      exact False.elim (G.loopless.irrefl q huv)
    by_cases hvr : v = r
    · subst v
      exact Or.inl (by simp [contractVertex])
    · right
      simpa [contractVertex, hvq, hvr] using (Or.inl huv)
  by_cases hur : u = r
  · subst u
    by_cases hvq : v = q
    · subst v
      exact Or.inl (by simp [contractVertex])
    by_cases hvr : v = r
    · subst v
      exact False.elim (G.loopless.irrefl r huv)
    · right
      simpa [contractVertex, hvq, hvr] using (Or.inr huv)
  · by_cases hvq : v = q
    · subst v
      right
      simpa [contractVertex, huq, hur] using (Or.inl huv)
    by_cases hvr : v = r
    · subst v
      right
      simpa [contractVertex, huq, hur] using (Or.inr huv)
    · right
      simpa [contractVertex, huq, hur, hvq, hvr] using huv

/-- Contracting two distinct vertices lowers the cardinality of the
vertex type by one. -/
theorem card_contractPairVertex
    [Fintype V] [DecidableEq V]
    (q r : V) (hqr : q ≠ r) :
    Fintype.card (ContractPairVertex V q r) =
      Fintype.card V - 1 := by
  have hmemberCard :
      Fintype.card {v : V // v = q ∨ v = r} = 2 := by
    let e : {v : V // v = q ∨ v = r} ≃
        ↥({q, r} : Finset V) := {
      toFun v := ⟨v.1, by
        simpa only [Finset.mem_insert,
          Finset.mem_singleton] using v.2⟩
      invFun v := ⟨v.1, by
        simpa only [Finset.mem_insert,
          Finset.mem_singleton] using v.2⟩
      left_inv v := by apply Subtype.ext; rfl
      right_inv v := by apply Subtype.ext; rfl
    }
    rw [Fintype.card_congr e, Fintype.card_coe]
    exact Finset.card_pair_eq_two_iff.mpr hqr
  have hremainingCard :
      Fintype.card {v : V // v ≠ q ∧ v ≠ r} =
        Fintype.card V - 2 := by
    have h :=
      Fintype.card_subtype_compl
        (fun v : V => v = q ∨ v = r)
    rw [hmemberCard] at h
    simpa [not_or] using h
  simp only [ContractPairVertex, Fintype.card_option,
    hremainingCard]
  have htwo : 2 ≤ Fintype.card V := by
    have hpair :
        ({q, r} : Finset V).card ≤
          (Finset.univ : Finset V).card :=
      Finset.card_le_card (by simp)
    simpa [Finset.card_pair_eq_two_iff.mpr hqr] using hpair
  omega

theorem card_contractPairVertex_lt
    [Fintype V] [DecidableEq V]
    (q r : V) (hqr : q ≠ r) :
    Fintype.card (ContractPairVertex V q r) <
      Fintype.card V := by
  rw [card_contractPairVertex q r hqr]
  have hpos : 0 < Fintype.card V := by
    exact Fintype.card_pos_iff.mpr ⟨q⟩
  omega

/--
If `v` is not contracted and it is not adjacent to both contracted
endpoints, contraction does not change its degree.
-/
theorem finiteDegree_contractPair_eq
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q r v : V)
    (hvq : v ≠ q) (hvr : v ≠ r)
    (hone : ¬(G.Adj v q ∧ G.Adj v r)) :
    finiteDegree (contractPair G q r) (contractVertex q r v) =
      finiteDegree G v := by
  classical
  let f := contractVertex q r
  let N := G.neighborSet v
  let NC := (contractPair G q r).neighborSet (f v)
  have hfv : f v = some ⟨v, hvq, hvr⟩ := by
    simp [f, contractVertex, hvq, hvr]
  have himage : f '' N = NC := by
    ext a
    constructor
    · rintro ⟨w, hvw, rfl⟩
      rcases contractVertex_eq_or_adj G q r v w hvw with heq | hadj
      · rcases (contractVertex_eq_iff q r v w).1 heq with hvwEq | ⟨hv, -⟩
        · subst w
          exact False.elim (G.loopless.irrefl v hvw)
        · exact False.elim (by tauto)
      · exact hadj
    · intro ha
      cases a with
      | none =>
          change (contractPair G q r).Adj (f v) none at ha
          rw [hfv] at ha
          rcases ha with hvqAdj | hvrAdj
          · exact ⟨q, hvqAdj, by simp [f, contractVertex]⟩
          · exact ⟨r, hvrAdj, by simp [f, contractVertex]⟩
      | some w =>
          change (contractPair G q r).Adj (f v) (some w) at ha
          rw [hfv] at ha
          exact ⟨w.1, ha, by
            simp [f, contractVertex, w.2.1, w.2.2]⟩
  have hinj : Set.InjOn f N := by
    intro a ha b hb hab
    rcases (contractVertex_eq_iff q r a b).1 hab with hab | ⟨haqr, hbqr⟩
    · exact hab
    · rcases haqr with haq | har <;>
        rcases hbqr with hbq | hbr
      · exact haq.trans hbq.symm
      · subst a
        subst b
        exact False.elim (hone ⟨ha, hb⟩)
      · subst a
        subst b
        exact False.elim (hone ⟨hb, ha⟩)
      · exact har.trans hbr.symm
  unfold finiteDegree
  change NC.ncard = N.ncard
  rw [← himage, hinj.ncard_image]

/--
Map a walk along a vertex map that is allowed to contract an edge to an
equality.  Equal consecutive images are suppressed.
-/
def _root_.SimpleGraph.Walk.mapOrContract
    {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableEq W]
    (f : V → W)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → f u = f v ∨ H.Adj (f u) (f v))
  {u v : V} :
    G.Walk u v → H.Walk (f u) (f v)
  | .nil => .nil
  | @SimpleGraph.Walk.cons _ _ u m v huv p =>
      if h : f u = f m then
        (SimpleGraph.Walk.mapOrContract f hedge p).copy
          h.symm rfl
      else
        .cons ((hedge huv).resolve_left h)
          (SimpleGraph.Walk.mapOrContract f hedge p)

/-- Every vertex retained by `mapOrContract` is the image of a vertex of
the original walk. -/
theorem _root_.SimpleGraph.Walk.exists_of_mem_support_mapOrContract
    {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableEq W]
    (f : V → W)
    (hedge : ∀ ⦃u v⦄, G.Adj u v →
      f u = f v ∨ H.Adj (f u) (f v))
    {u v : V} (p : G.Walk u v)
    {z : W}
    (hz : z ∈
      (SimpleGraph.Walk.mapOrContract
        f hedge p).support) :
    ∃ x ∈ p.support, f x = z := by
  induction p with
  | @nil u =>
      simp only [SimpleGraph.Walk.mapOrContract,
        SimpleGraph.Walk.support_nil,
        List.mem_singleton] at hz
      exact ⟨u, by simp, hz.symm⟩
  | @cons u m v hum p ih =>
      unfold SimpleGraph.Walk.mapOrContract at hz
      split at hz
      next h =>
        have hz' :
            z ∈
              (SimpleGraph.Walk.mapOrContract
                f hedge p).support := by
          simpa only [SimpleGraph.Walk.support_copy] using hz
        obtain ⟨x, hx, hfx⟩ := ih hz'
        exact ⟨x, List.mem_cons.mpr (Or.inr hx), hfx⟩
      next h =>
        simp only [SimpleGraph.Walk.support_cons,
          List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨u, by simp, rfl⟩
        · obtain ⟨x, hx, hfx⟩ := ih hz
          exact ⟨x, List.mem_cons.mpr (Or.inr hx), hfx⟩

/-- The full preimage of a finite contracted vertex set. -/
noncomputable def contractionPreimage
    [Fintype V] [DecidableEq V]
    (q r : V) (T : Finset (ContractPairVertex V q r)) :
    Finset V :=
  Finset.univ.filter fun v => contractVertex q r v ∈ T

@[simp] theorem contractionPreimage_mem
    [Fintype V] [DecidableEq V]
    (q r : V) (T : Finset (ContractPairVertex V q r)) (v : V) :
    v ∈ contractionPreimage q r T ↔ contractVertex q r v ∈ T := by
  classical
  simp [contractionPreimage]

theorem contractionPreimage_card_le
    [Fintype V] [DecidableEq V]
    (q r : V)
    (T : Finset (ContractPairVertex V q r)) :
    (contractionPreimage q r T).card ≤
      T.card + if none ∈ T then 1 else 0 := by
  classical
  let R := contractionPreimage q r T
  by_cases hnone : none ∈ T
  · let R' := R.erase q
    have hinj : Set.InjOn (contractVertex q r) R' := by
      intro u hu v hv huv
      have huq : u ≠ q := (Finset.mem_erase.mp hu).1
      have hvq : v ≠ q := (Finset.mem_erase.mp hv).1
      rcases (contractVertex_eq_iff q r u v).1 huv with huv | ⟨hu, hv⟩
      · exact huv
      · have hur : u = r := by tauto
        have hvr : v = r := by tauto
        exact hur.trans hvr.symm
    have himageSub : R'.image (contractVertex q r) ⊆ T := by
      intro w hw
      obtain ⟨v, hvR', rfl⟩ := Finset.mem_image.mp hw
      exact (contractionPreimage_mem q r T v).1
        (Finset.mem_of_mem_erase hvR')
    have hR'le : R'.card ≤ T.card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card himageSub
    have hqR : q ∈ R := by
      apply (contractionPreimage_mem q r T q).2
      simpa [contractVertex] using hnone
    have hRcardEq : R'.card + 1 = R.card := by
      exact Finset.card_erase_add_one hqR
    simp only [hnone, if_pos]
    change (contractionPreimage q r T).card ≤ T.card + 1
    change R.card ≤ T.card + 1
    omega
  · have hinj : Set.InjOn (contractVertex q r) R := by
      intro u hu v hv huv
      rcases (contractVertex_eq_iff q r u v).1 huv with huv | ⟨huvQ, -⟩
      · exact huv
      · have huNone : contractVertex q r u = none :=
          (contractVertex_eq_none_iff q r u).2 huvQ
        have huT := (contractionPreimage_mem q r T u).1 hu
        exact False.elim (hnone (huNone ▸ huT))
    have himageSub : R.image (contractVertex q r) ⊆ T := by
      intro w hw
      obtain ⟨v, hvR, rfl⟩ := Finset.mem_image.mp hw
      exact (contractionPreimage_mem q r T v).1 hvR
    have hRle : R.card ≤ T.card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card himageSub
    simpa [hnone] using hRle

/--
The contraction fact used in Lemma 5.2: contracting an edge in a
4-connected graph leaves a 3-connected graph.
-/
theorem isThreeConnected_contractPair
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q r : V)
    (hqr : q ≠ r) (_hqrAdj : G.Adj q r)
    (hconn : IsKConnected G 4) :
    IsKConnected (contractPair G q r) 3 := by
  classical
  have hmemberCard :
      Fintype.card {v : V // v = q ∨ v = r} = 2 := by
    let e : {v : V // v = q ∨ v = r} ≃
        ↥({q, r} : Finset V) := {
      toFun v := ⟨v.1, by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using v.2⟩
      invFun v := ⟨v.1, by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using v.2⟩
      left_inv v := by apply Subtype.ext; rfl
      right_inv v := by apply Subtype.ext; rfl
    }
    rw [Fintype.card_congr e, Fintype.card_coe]
    exact Finset.card_pair_eq_two_iff.mpr hqr
  have hremainingCard :
      Fintype.card {v : V // v ≠ q ∧ v ≠ r} =
        Fintype.card V - 2 := by
    have h :=
      Fintype.card_subtype_compl (fun v : V => v = q ∨ v = r)
    rw [hmemberCard] at h
    simpa [not_or] using h
  constructor
  · simp only [Fintype.card_option, hremainingCard]
    have horder := hconn.1
    omega
  · intro T hT
    let R := contractionPreimage q r T
    have hRbound :=
      contractionPreimage_card_le q r T
    change R.card ≤ T.card + if none ∈ T then 1 else 0 at hRbound
    have hRcard : R.card < 4 := by
      by_cases hnone : none ∈ T <;> simp [hnone] at hRbound <;> omega
    have hbase := hconn.2 R hRcard
    let f : {v : V // v ∉ R} →
        {w : ContractPairVertex V q r // w ∉ T} :=
      fun v => ⟨contractVertex q r v.1, by
        intro hvT
        exact v.2 ((contractionPreimage_mem q r T v.1).2 hvT)⟩
    have hedge :
        ∀ ⦃u v : {v : V // v ∉ R}⦄,
          (G.induce {v | v ∉ R}).Adj u v →
          f u = f v ∨
            ((contractPair G q r).induce {w | w ∉ T}).Adj (f u) (f v) := by
      intro u v huv
      rcases contractVertex_eq_or_adj G q r u.1 v.1 huv with heq | hadj
      · exact Or.inl (by apply Subtype.ext; exact heq)
      · exact Or.inr hadj
    rw [connected_iff_exists_forall_reachable] at hbase ⊢
    obtain ⟨root, hroot⟩ := hbase
    refine ⟨f root, ?_⟩
    intro w
    let v : V := uncontractVertex q w.1
    have hcontract : contractVertex q r v = w.1 :=
      contractVertex_uncontractVertex q r w.1
    have hvR : v ∉ R := by
      intro hvR
      have hvT :=
        (contractionPreimage_mem q r T v).1 hvR
      exact w.2 (hcontract ▸ hvT)
    let vR : {v : V // v ∉ R} := ⟨v, hvR⟩
    obtain ⟨p⟩ := hroot vR
    have hwalk :=
      SimpleGraph.Walk.mapOrContract f hedge p
    have hreach : ((contractPair G q r).induce {w | w ∉ T}).Reachable
        (f root) (f vR) :=
      ⟨hwalk⟩
    have hfv : f vR = w := by
      apply Subtype.ext
      exact hcontract
    rwa [hfv] at hreach

end DeanK5
