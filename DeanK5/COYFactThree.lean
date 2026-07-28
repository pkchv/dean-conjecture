import DeanK5.COYComponentConnector
import DeanK5.COYCoreBounds

/-!
# COY Fact 3

This file derives the bounded core-rank inequalities used in the
Chiba--Ota--Yamashita induction.  The component containing the second
root supplies one boundary edge and a fixed path through that component;
the explicit support theorems for the core catalogues then discharge the
simplicity premise of Fact 1.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

/--
Component form of the capacity argument behind COY Fact 3.

The inner catalogue is supported on the separator `S`; the fixed outer
path crosses one boundary edge and otherwise stays in the disjoint
component `Q`.  Thus the support-disjointness premise is derived rather
than assumed.
-/
theorem catalog_capacity_lt_of_component
    [DecidableEq V]
    {G : SimpleGraph V} {S Q : Finset V}
    {x y t a : V} {q n : ℕ}
    (hQ : ComponentRegion G S Q)
    (hy : y ∈ Q) (ht : t ∈ S) (ha : a ∈ Q)
    (hta : G.Adj t a)
    (hq : 1 ≤ q) (hxy : x ≠ y) (hxt : x ≠ t)
    (catalog : q ≤ n → SemiAdmissiblePathFamily G x t q)
    (hsupport : ∀ hcapacity i z,
      z ∈ ((catalog hcapacity).path i).walk.support →
        z ∈ S)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    n < q := by
  have hyt : y ≠ t := by
    intro h
    apply hQ.not_mem_separator hy
    simpa [h] using ht
  let outer := hQ.boundaryPath ht ha hy hta
  apply catalog_capacity_lt_of_no_paths
    hq hxy hxt hyt outer catalog
  · intro hcapacity i
    exact hQ.support_disjoint_boundaryPath_tail
      ((catalog hcapacity).path i)
      (hsupport hcapacity i)
      ht ha hy hta
  · exact hno

namespace Core

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x : V} {ℓ : ℕ}

/--
In a 2-connected graph, a component outside a core has an attachment at
a core vertex other than the core root.
-/
theorem exists_nonroot_attachment
    (C : Core G x ℓ) {Q : Finset V}
    (hQ : ComponentRegion G C.carrier Q)
    (hconn : IsKConnected G 2) :
    ∃ a ∈ Q, ∃ t ∈ C.carrier, t ≠ x ∧ G.Adj t a := by
  obtain ⟨r, hrCarrier, hrx⟩ :=
    C.exists_ne_root_mem_carrier
  obtain ⟨a, haQ, t, htCarrier, htx, hat⟩ :=
    hQ.exists_attachment_avoiding_boundary_vertex
      hconn C.root_mem_carrier hrCarrier hrx.symm
  exact ⟨a, haQ, t, htCarrier, htx, hat.symm⟩

/--
The same attachment conclusion under COY's exact rooted-connectivity
hypothesis.  The only additional edge is `xy`; an attachment at a
nonroot core vertex cannot be that artificial edge.
-/
theorem exists_nonroot_attachment_of_rooted
    (C : Core G x ℓ) {Q : Finset V} {y : V}
    (hQ : ComponentRegion G C.carrier Q)
    (hconn : IsKConnected (G ⊔ edge x y) 2) :
    ∃ a ∈ Q, ∃ t ∈ C.carrier, t ≠ x ∧ G.Adj t a := by
  let H := G ⊔ edge x y
  have hQH : ComponentRegion H C.carrier Q := {
    nonempty := hQ.nonempty
    disjoint := hQ.disjoint
    connected := hQ.connected.mono (by
      intro a b hab
      exact Or.inl hab)
    closed := by
      intro a b haQ hab hbCarrier
      rcases hab with hab | hab
      · exact hQ.closed haQ hab hbCarrier
      · simp only [SimpleGraph.edge_adj] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact False.elim
            (hQ.not_mem_separator haQ C.root_mem_carrier)
        · exact False.elim (hbCarrier C.root_mem_carrier)
  }
  obtain ⟨r, hrCarrier, hrx⟩ :=
    C.exists_ne_root_mem_carrier
  obtain ⟨a, haQ, t, htCarrier, htx, hat⟩ :=
    hQH.exists_attachment_avoiding_boundary_vertex
      hconn C.root_mem_carrier hrCarrier hrx.symm
  have hta : G.Adj t a := by
    rcases hat with hat | hat
    · exact hat.symm
    · simp only [SimpleGraph.edge_adj] at hat
      rcases hat with ⟨hax, hty⟩ | ⟨hay, htx'⟩
      · exact False.elim
          (hQ.not_mem_separator haQ (hax ▸ C.root_mem_carrier))
      · exact False.elim (htx htx')
  exact ⟨a, haQ, t, htCarrier, htx, hta⟩

end Core

namespace TypeOneCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y : V} {ℓ q : ℕ}

/--
COY Fact 3 for a type-1 core.  Every nonroot attachment is in `T`, so
the stronger inequality `ℓ+1 < q` always holds.
-/
theorem rank_add_one_lt_of_component
    (C : TypeOneCore G x ℓ) {Q : Finset V}
    (hQ : ComponentRegion G (insert x C.T) Q)
    (hy : y ∈ Q)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ + 1 < q := by
  let core : Core G x ℓ := .typeOne C
  have hcarrier : core.carrier = insert x C.T := by
    simp [core, Core.carrier, Core.S, Core.T]
  have hQcore : ComponentRegion G core.carrier Q := by
    simpa [hcarrier] using hQ
  obtain ⟨a, haQ, t, htCarrier, htx, hta⟩ :=
    core.exists_nonroot_attachment_of_rooted hQcore hconn
  have htT : t ∈ C.T := by
    simpa [core, Core.carrier, Core.S, Core.T, htx] using
      htCarrier
  have hxy : x ≠ y := by
    intro h
    apply hQ.not_mem_separator hy
    simp [h]
  apply catalog_capacity_lt_of_component
    (S := insert x C.T) (Q := Q)
    hQ hy (by simp [htT]) haQ hta
    hqOne hxy htx.symm
    (fun hcapacity =>
      C.semiAdmissiblePathsTo t htT q
        hqOne hqFour hcapacity)
  · intro hcapacity i z hz
    exact C.semiAdmissiblePathsTo_support
      t htT q hqOne hqFour hcapacity i z hz
  · exact hno

end TypeOneCore

namespace TypeTwoCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y : V} {ℓ q : ℕ}

omit [Fintype V] in
/-- A specified type-2 attachment in `T` gives the stronger Fact 3 bound. -/
theorem rank_add_one_lt_of_t_attachment
    (C : TypeTwoCore G x ℓ) {Q : Finset V}
    (hQ : ComponentRegion G (insert x (C.S ∪ C.T)) Q)
    (hy : y ∈ Q)
    {a t : V} (ha : a ∈ Q) (ht : t ∈ C.T)
    (hta : G.Adj t a)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ + 1 < q := by
  have hxy : x ≠ y := by
    intro h
    apply hQ.not_mem_separator hy
    simp [h]
  have hxt : x ≠ t := by
    intro h
    exact C.root_not_mem_T (h ▸ ht)
  apply catalog_capacity_lt_of_component
    (S := insert x (C.S ∪ C.T)) (Q := Q)
    hQ hy (by simp [ht]) ha hta
    hqOne hxy hxt
    (fun hcapacity =>
      C.semiAdmissiblePathsToT t ht q
        hqOne hqFour hcapacity)
  · intro hcapacity i z hz
    exact C.semiAdmissiblePathsToT_support
      t ht q hqOne hqFour hcapacity i z hz
  · exact hno

/-- COY Fact 3(1) for a type-2 core. -/
theorem rank_lt_of_component
    (C : TypeTwoCore G x ℓ) {Q : Finset V}
    (hQ : ComponentRegion G (insert x (C.S ∪ C.T)) Q)
    (hy : y ∈ Q)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ < q := by
  let core : Core G x ℓ := .typeTwo C
  have hcarrier :
      core.carrier = insert x (C.S ∪ C.T) := by
    rfl
  have hQcore : ComponentRegion G core.carrier Q := by
    simpa [hcarrier] using hQ
  obtain ⟨a, haQ, t, htCarrier, htx, hta⟩ :=
    core.exists_nonroot_attachment_of_rooted hQcore hconn
  have hparts : t ∈ C.S ∨ t ∈ C.T := by
    simpa [core, Core.carrier, Core.S, Core.T, htx] using
      htCarrier
  rcases hparts with htS | htT
  · have hxy : x ≠ y := by
      intro h
      apply hQ.not_mem_separator hy
      simp [h]
    have hxt : x ≠ t := htx.symm
    apply catalog_capacity_lt_of_component
      (S := insert x (C.S ∪ C.T)) (Q := Q)
      hQ hy (by simp [htS]) haQ hta
      hqOne hxy hxt
      (fun hcapacity =>
        SemiAdmissiblePathFamily.ofAdmissible
          (C.admissiblePathsToS t htS q
            hqOne hqFour hcapacity))
    · intro hcapacity i z hz
      exact C.admissiblePathsToS_support
        t htS q hqOne hqFour hcapacity i z hz
    · exact hno
  · have hstrong :=
      C.rank_add_one_lt_of_t_attachment
        hQ hy haQ htT hta hqOne hqFour hno
    omega

end TypeTwoCore

namespace TypeThreeCore

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y : V} {ℓ q : ℕ}

omit [Fintype V] in
/-- A specified type-3 attachment in `T` gives the stronger Fact 3 bound. -/
theorem rank_add_one_lt_of_t_attachment
    (C : TypeThreeCore G x ℓ) {Q : Finset V}
    (hQ : ComponentRegion G (insert x (C.S ∪ C.T)) Q)
    (hy : y ∈ Q)
    {a t : V} (ha : a ∈ Q) (ht : t ∈ C.T)
    (hta : G.Adj t a)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ + 1 < q := by
  have hxy : x ≠ y := by
    intro h
    apply hQ.not_mem_separator hy
    simp [h]
  have hxt : x ≠ t := by
    intro h
    exact C.root_not_mem_T (h ▸ ht)
  apply catalog_capacity_lt_of_component
    (S := insert x (C.S ∪ C.T)) (Q := Q)
    hQ hy (by simp [ht]) ha hta
    hqOne hxy hxt
    (fun hcapacity =>
      C.semiAdmissiblePathsToT t ht q
        hqOne hqFour hcapacity)
  · intro hcapacity i z hz
    exact C.semiAdmissiblePathsToT_support
      t ht q hqOne hqFour hcapacity i z hz
  · exact hno

/-- COY Fact 3(1) for a type-3 core. -/
theorem rank_lt_of_component
    (C : TypeThreeCore G x ℓ) {Q : Finset V}
    (hQ : ComponentRegion G (insert x (C.S ∪ C.T)) Q)
    (hy : y ∈ Q)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ < q := by
  let core : Core G x ℓ := .typeThree C
  have hcarrier :
      core.carrier = insert x (C.S ∪ C.T) := by
    rfl
  have hQcore : ComponentRegion G core.carrier Q := by
    simpa [hcarrier] using hQ
  obtain ⟨a, haQ, t, htCarrier, htx, hta⟩ :=
    core.exists_nonroot_attachment_of_rooted hQcore hconn
  have hparts : t ∈ C.S ∨ t ∈ C.T := by
    simpa [core, Core.carrier, Core.S, Core.T, htx] using
      htCarrier
  rcases hparts with htS | htT
  · have hxy : x ≠ y := by
      intro h
      apply hQ.not_mem_separator hy
      simp [h]
    have hxt : x ≠ t := htx.symm
    have hTcard : 0 < C.T.card := by
      have htwo : 2 ≤ C.T.card :=
        (Nat.le_max_right (ℓ + 1) 2).trans C.card_T_lower
      omega
    obtain ⟨deleted, hdeleted⟩ :=
      Finset.card_pos.mp hTcard
    apply catalog_capacity_lt_of_component
      (S := insert x (C.S ∪ C.T)) (Q := Q)
      hQ hy (by simp [htS]) haQ hta
      hqOne hxy hxt
      (fun hcapacity =>
        SemiAdmissiblePathFamily.ofAdmissible
          (C.admissiblePathsToSAfterDeleting
            t deleted htS hdeleted q
            hqOne hqFour hcapacity))
    · intro hcapacity i z hz
      have hzSmall :=
        C.admissiblePathsToSAfterDeleting_support
          t deleted htS hdeleted q
          hqOne hqFour hcapacity i z hz
      have hsubset :
          insert x (C.S ∪ C.T.erase deleted) ⊆
            insert x (C.S ∪ C.T) := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_union,
          Finset.mem_erase] at hv ⊢
        aesop
      exact hsubset hzSmall
    · exact hno
  · have hstrong :=
      C.rank_add_one_lt_of_t_attachment
        hQ hy haQ htT hta hqOne hqFour hno
    omega

end TypeThreeCore

/-- The selected exterior component has an attachment in the core's `T` part. -/
def Core.HasTAttachment
    [DecidableEq V]
    {G : SimpleGraph V} {x : V} {ℓ : ℕ}
    (C : Core G x ℓ) (Q : Finset V) : Prop :=
  ∃ a ∈ Q, ∃ t ∈ C.T, G.Adj t a

/--
COY Fact 3 in the bounded range used by this development.

The graph is only assumed to be rooted two-connected, exactly as in the
source.  The first inequality is `ℓ ≤ q-1`; a `T`-attachment improves it
to `ℓ ≤ q-2`.
-/
theorem RootedCore.factThree
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x y : V} {ℓ q : ℕ}
    (R : RootedCore G x y ℓ) {Q : Finset V}
    (hQ : ComponentRegion G R.core.carrier Q)
    (hy : y ∈ Q)
    (hconn : IsTwoConnected (G ⊔ edge x y))
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hno : ¬Nonempty (AdmissiblePathFamily G x y q)) :
    ℓ < q ∧ (R.core.HasTAttachment Q → ℓ + 1 < q) := by
  cases hcore : R.core with
  | typeOne C =>
      have hQ' :
          ComponentRegion G (insert x C.T) Q := by
        simpa [hcore, Core.carrier, Core.S, Core.T] using hQ
      have hstrong :=
        C.rank_add_one_lt_of_component
          hQ' hy hconn hqOne hqFour hno
      exact ⟨by omega, fun _ => hstrong⟩
  | typeTwo C =>
      have hQ' :
          ComponentRegion G (insert x (C.S ∪ C.T)) Q := by
        simpa [hcore, Core.carrier, Core.S, Core.T] using hQ
      have hbase :=
        C.rank_lt_of_component
          hQ' hy hconn hqOne hqFour hno
      refine ⟨hbase, ?_⟩
      intro hattach
      obtain ⟨a, haQ, t, htT, hta⟩ :
          ∃ a ∈ Q, ∃ t ∈ C.T, G.Adj t a := by
        simpa [Core.HasTAttachment, Core.T] using hattach
      exact C.rank_add_one_lt_of_t_attachment
        hQ' hy haQ htT hta hqOne hqFour hno
  | typeThree C =>
      have hQ' :
          ComponentRegion G (insert x (C.S ∪ C.T)) Q := by
        simpa [hcore, Core.carrier, Core.S, Core.T] using hQ
      have hbase :=
        C.rank_lt_of_component
          hQ' hy hconn hqOne hqFour hno
      refine ⟨hbase, ?_⟩
      intro hattach
      obtain ⟨a, haQ, t, htT, hta⟩ :
          ∃ a ∈ Q, ∃ t ∈ C.T, G.Adj t a := by
        simpa [Core.HasTAttachment, Core.T] using hattach
      exact C.rank_add_one_lt_of_t_attachment
        hQ' hy haQ htT hta hqOne hqFour hno

end COY

end DeanK5
