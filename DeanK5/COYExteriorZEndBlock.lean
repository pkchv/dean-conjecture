import DeanK5.COYCoreAttachment
import DeanK5.COYModifiedExterior
import DeanK5.COYWorkingCoreSelection
import DeanK5.COYZEndBlock
import DeanK5.Graph.ComponentDegree

/-!
# The `z`-end-block inside the selected COY exterior

This file places `ZEndBlockCertificate` in the exterior component of a
`PreferredWorkingCoreData`.  The certificate itself is stated on the graph
induced by the exterior region.  The definitions below retain its subtype
vertices while also exposing the ambient vertices and paths needed by the
later COY argument.

No rank estimate from Claim 3.9 is proved here.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

private theorem predicate_of_walk
    {W : Type*} {D : SimpleGraph W}
    (A : W → Prop)
    (hclosed :
      ∀ ⦃u v : W⦄, A u → D.Adj u v → A v)
    {u v : W} (p : D.Walk u v) (hu : A u) :
    A v := by
  induction p with
  | nil =>
      exact hu
  | @cons a b c hab p ih =>
      exact ih (hclosed hu hab)

namespace TypeThreeModificationChoice

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}
  {O : OptimalRootedCore G x y}
  {T : TypeThreeModificationTrigger (z := z) O}

/--
Every original `T`-vertex other than the removed vertex `t₀` remains in
the `T`-side of the modified core.
-/
theorem mem_core_T_of_mem_original_T_of_ne_t₀
    (K : TypeThreeModificationChoice T)
    {v : V} (hvT : v ∈ T.core.T) (hvt : v ≠ T.t₀) :
    v ∈ K.core.T := by
  cases K with
  | balanced s₀ hs₀ hbalance =>
      simp [core, TypeThreeCore.eraseBalanced, hvT, hvt]
  | terminal hlarge =>
      simp [core, TypeThreeCore.eraseTerminal, hvT, hvt]

/--
In the modified exterior, the only neighbour of the second root is the
removed vertex `t₀`.
-/
theorem other_root_adj_iff_t₀_in_otherRegion
    (K : TypeThreeModificationChoice T)
    (v : {w : V // w ∈ K.rooted.otherRegion}) :
    (G.induce (↑K.rooted.otherRegion : Set V)).Adj
        ⟨y, K.rooted.other_root_mem_otherRegion⟩ v ↔
      v.1 = T.t₀ := by
  constructor
  · intro hyv
    have hvOldT : v.1 ∈ T.core.T :=
      (T.other_root_neighbors v.1).1 hyv
    by_contra hvt
    have hvNewT :
        v.1 ∈ K.core.T :=
      K.mem_core_T_of_mem_original_T_of_ne_t₀ hvOldT hvt
    have hvCarrier :
        v.1 ∈ K.rooted.core.carrier := by
      exact K.rooted.core.T_subset_carrier hvNewT
    exact
      K.rooted.otherRegion_componentRegion.not_mem_separator
        v.2 hvCarrier
  · intro hvt
    change G.Adj y v.1
    rw [hvt]
    exact T.other_root_adj_t₀

end TypeThreeModificationChoice

namespace PreferredWorkingCoreData

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {x y z : V}

/-- The vertex type of the component containing the second root. -/
abbrev ExteriorVertex
    (P : PreferredWorkingCoreData G x y z) :=
  {v : V // v ∈ P.working.rooted.otherRegion}

/-- The graph induced by the component containing the second root. -/
abbrev exteriorGraph
    (P : PreferredWorkingCoreData G x y z) :
    SimpleGraph P.ExteriorVertex :=
  G.induce (↑P.working.rooted.otherRegion : Set V)

/-- The second root as a vertex of the induced exterior graph. -/
def exteriorY
    (P : PreferredWorkingCoreData G x y z) :
    P.ExteriorVertex :=
  ⟨y, P.working.rooted.other_root_mem_otherRegion⟩

/-- The exceptional vertex as a vertex of the induced exterior graph. -/
def exteriorZ
    (P : PreferredWorkingCoreData G x y z)
    (hz : z ∈ P.working.rooted.otherRegion) :
    P.ExteriorVertex :=
  ⟨z, hz⟩

/-- The canonical inclusion of the induced exterior graph into `G`. -/
def exteriorEmbedding
    (P : PreferredWorkingCoreData G x y z) :
    P.exteriorGraph ↪g G :=
  Embedding.induce (↑P.working.rooted.otherRegion : Set V)

/--
A two-vertex `z`-end-block certificate on the exterior component selected by
`P`.  The explicit membership field makes the induced copy of `z` available.
-/
structure ExteriorZEndBlock
    (P : PreferredWorkingCoreData G x y z) where
  /-- The exceptional vertex lies in the selected exterior component. -/
  z_mem_otherRegion : z ∈ P.working.rooted.otherRegion
  /-- The source `z`-end-block data in the induced exterior graph. -/
  certificate :
    ZEndBlockCertificate P.exteriorGraph P.exteriorY
      (P.exteriorZ z_mem_otherRegion)

namespace ExteriorZEndBlock

variable {P : PreferredWorkingCoreData G x y z}

/-- The ambient vertex represented by the cut vertex `b_z`. -/
abbrev bz (E : P.ExteriorZEndBlock) : V :=
  E.certificate.bz.1

/-- The ambient vertex represented by the second neighbour `b'_z`. -/
noncomputable abbrev bPrime (E : P.ExteriorZEndBlock) : V :=
  E.certificate.bPrime.1

/-- The cut vertex belongs to the selected exterior component. -/
theorem bz_mem_otherRegion (E : P.ExteriorZEndBlock) :
    E.bz ∈ P.working.rooted.otherRegion :=
  E.certificate.bz.2

/-- The second neighbour belongs to the selected exterior component. -/
theorem bPrime_mem_otherRegion (E : P.ExteriorZEndBlock) :
    E.bPrime ∈ P.working.rooted.otherRegion :=
  E.certificate.bPrime.2

/-- The two distinguished roots of the exterior certificate are distinct. -/
theorem y_ne_z (E : P.ExteriorZEndBlock) :
    y ≠ z := by
  intro hyz
  apply E.certificate.y_ne_z
  apply Subtype.ext
  exact hyz

/-- The target root is distinct from the ambient cut vertex. -/
theorem y_ne_bz (E : P.ExteriorZEndBlock) :
    y ≠ E.bz := by
  intro hyb
  apply E.certificate.y_ne_bz
  apply Subtype.ext
  exact hyb

/-- The ambient cut vertex is distinct from the target root. -/
theorem bz_ne_y (E : P.ExteriorZEndBlock) :
    E.bz ≠ y :=
  E.y_ne_bz.symm

/-- The exceptional vertex is distinct from the ambient cut vertex. -/
theorem z_ne_bz (E : P.ExteriorZEndBlock) :
    z ≠ E.bz := by
  intro hzb
  apply E.certificate.z_ne_bz
  apply Subtype.ext
  exact hzb

/-- The ambient cut vertex is distinct from the exceptional vertex. -/
theorem bz_ne_z (E : P.ExteriorZEndBlock) :
    E.bz ≠ z :=
  E.z_ne_bz.symm

/-- The second neighbour is distinct from the exceptional vertex. -/
theorem bPrime_ne_z (E : P.ExteriorZEndBlock) :
    E.bPrime ≠ z := by
  intro hpz
  apply E.certificate.bPrime_ne_z
  apply Subtype.ext
  exact hpz

/-- The second neighbour is distinct from the cut vertex. -/
theorem bPrime_ne_bz (E : P.ExteriorZEndBlock) :
    E.bPrime ≠ E.bz := by
  intro hpb
  apply E.certificate.bPrime_ne_bz
  apply Subtype.ext
  exact hpb

/-- The cut vertex is distinct from its second neighbour. -/
theorem bz_ne_bPrime (E : P.ExteriorZEndBlock) :
    E.bz ≠ E.bPrime :=
  E.bPrime_ne_bz.symm

/-- The bridge edge `z b_z`, viewed in the ambient graph. -/
theorem z_adj_bz (E : P.ExteriorZEndBlock) :
    G.Adj z E.bz :=
  E.certificate.z_adj_bz

/-- The edge `b_z b'_z`, viewed in the ambient graph. -/
theorem bz_adj_bPrime (E : P.ExteriorZEndBlock) :
    G.Adj E.bz E.bPrime :=
  E.certificate.bz_adj_bPrime

/--
The ambient degree of `b_z` is its two exterior neighbours plus its
neighbours in the working-core carrier.
-/
theorem finiteDegree_bz_eq_two_add_coreNeighbors
    (E : P.ExteriorZEndBlock) :
    finiteDegree G E.bz =
      2 +
        (G.neighborSet E.bz ∩
          (↑P.working.rooted.core.carrier : Set V)).ncard := by
  have hdegree :=
    ComponentRegion.finiteDegree_eq_induce_add_separatorNeighbors
      P.working.rooted.otherRegion_componentRegion
      E.bz_mem_otherRegion
  have hbz :
      (⟨E.bz, E.bz_mem_otherRegion⟩ : P.ExteriorVertex) =
        E.certificate.bz :=
    Subtype.ext (by rfl)
  rw [hbz, E.certificate.bz_degree_two] at hdegree
  exact hdegree

/-- The two-edge `z-b_z-b'_z` stem, viewed in the ambient graph. -/
noncomputable def stem
    (E : P.ExteriorZEndBlock) :
    SimplePath G z E.bPrime :=
  E.certificate.stem.mapInjectiveHom
    P.exteriorEmbedding.toHom Subtype.val_injective

/-- The ambient stem has two edges. -/
@[simp] theorem stem_length
    (E : P.ExteriorZEndBlock) :
    E.stem.length = 2 := by
  calc
    E.stem.length = E.certificate.stem.length :=
      SimplePath.mapInjectiveHom_length
        E.certificate.stem P.exteriorEmbedding.toHom
          Subtype.val_injective
    _ = 2 := E.certificate.stem_length

/-- The ambient stem has support `[z, b_z, b'_z]`. -/
@[simp] theorem stem_support
    (E : P.ExteriorZEndBlock) :
    E.stem.walk.support = [z, E.bz, E.bPrime] := by
  change
    (E.certificate.stem.walk.map
      P.exteriorEmbedding.toHom).support =
        [z, E.certificate.bz.1, E.certificate.bPrime.1]
  rw [SimpleGraph.Walk.support_map, E.certificate.stem_support]
  rfl

/-- The fixed `b_z`--`y` path, viewed in the ambient graph. -/
noncomputable def pathToY
    (E : P.ExteriorZEndBlock) :
    SimplePath G E.bz y :=
  E.certificate.pathToY.mapInjectiveHom
    P.exteriorEmbedding.toHom Subtype.val_injective

/-- The fixed `b'_z`--`y` tail, viewed in the ambient graph. -/
noncomputable def bPrimeToY
    (E : P.ExteriorZEndBlock) :
    SimplePath G E.bPrime y :=
  E.certificate.bPrimeToY.mapInjectiveHom
    P.exteriorEmbedding.toHom Subtype.val_injective

/-- Every vertex of the ambient `b_z`--`y` path lies in the exterior. -/
theorem pathToY_support_mem_otherRegion
    (E : P.ExteriorZEndBlock)
    {v : V} (hv : v ∈ E.pathToY.walk.support) :
    v ∈ P.working.rooted.otherRegion := by
  have hvRange :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := E.certificate.pathToY)
      (f := P.exteriorEmbedding.toHom)
      (hinj := Subtype.val_injective)
      (by
        change
          v ∈
            (E.certificate.pathToY.mapInjectiveHom
              P.exteriorEmbedding.toHom
              Subtype.val_injective).walk.support at hv
        exact hv)
  obtain ⟨w, rfl⟩ := hvRange
  exact w.2

/-- Every vertex of the ambient `b'_z`--`y` tail lies in the exterior. -/
theorem bPrimeToY_support_mem_otherRegion
    (E : P.ExteriorZEndBlock)
    {v : V} (hv : v ∈ E.bPrimeToY.walk.support) :
    v ∈ P.working.rooted.otherRegion := by
  have hvRange :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := E.certificate.bPrimeToY)
      (f := P.exteriorEmbedding.toHom)
      (hinj := Subtype.val_injective)
      (by
        change
          v ∈
            (E.certificate.bPrimeToY.mapInjectiveHom
              P.exteriorEmbedding.toHom
              Subtype.val_injective).walk.support at hv
        exact hv)
  obtain ⟨w, rfl⟩ := hvRange
  exact w.2

/-- The ambient `b_z`--`y` path avoids `z`. -/
theorem z_not_mem_pathToY_support
    (E : P.ExteriorZEndBlock) :
    z ∉ E.pathToY.walk.support := by
  intro hz
  change
    z ∈
      (E.certificate.pathToY.walk.map
        P.exteriorEmbedding.toHom).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hz
  have hwEq : w = P.exteriorZ E.z_mem_otherRegion := by
    apply Subtype.ext
    exact hwz
  subst w
  exact E.certificate.z_not_mem_pathToY_support hw

/-- The ambient `b'_z`--`y` tail avoids `z`. -/
theorem z_not_mem_bPrimeToY_support
    (E : P.ExteriorZEndBlock) :
    z ∉ E.bPrimeToY.walk.support := by
  intro hz
  change
    z ∈
      (E.certificate.bPrimeToY.walk.map
        P.exteriorEmbedding.toHom).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hz
  have hwEq : w = P.exteriorZ E.z_mem_otherRegion := by
    apply Subtype.ext
    exact hwz
  subst w
  exact E.certificate.z_not_mem_bPrimeToY_support hw

/-- The first vertex after `b_z` on the ambient fixed path is `b'_z`. -/
theorem pathToY_snd_eq_bPrime
    (E : P.ExteriorZEndBlock) :
    E.pathToY.walk.snd = E.bPrime := by
  change
    (E.certificate.pathToY.walk.map
      P.exteriorEmbedding.toHom).getVert 1 =
        E.certificate.bPrime.1
  rw [SimpleGraph.Walk.getVert_map]
  exact congrArg Subtype.val E.certificate.pathToY_snd_eq_bPrime

/--
The cut vertex is not the vertex excluded by Claim 3.3.

In the natural branch the excluded vertex is `y`, and this is a field of
the `z`-end-block certificate.  In the modified branch, if `b_z = t₀`,
then `z-b_z-y` is a neighbour-closed set in the connected exterior:
`z` and `y` have only neighbour `b_z`, while `b_z` has degree two.
Claim 3.4 supplies another exterior vertex, giving a contradiction.
-/
theorem bz_ne_excludedVertex
    (E : P.ExteriorZEndBlock)
    (hxz : ¬G.Adj x z) :
    E.bz ≠ P.working.excludedVertex := by
  rcases P with ⟨orientation, working⟩
  cases working with
  | natural hnot =>
      exact E.bz_ne_y
  | modified T K =>
      intro hbz
      have hbzT : E.bz = T.t₀ := by
        simpa [SelectedWorkingCore.excludedVertex] using hbz
      have hprimeY :
          E.certificate.bPrime =
            ({ orientation := orientation
               working := SelectedWorkingCore.modified T K :
                PreferredWorkingCoreData G x y z }).exteriorY := by
        have hby :
            ({ orientation := orientation
               working := SelectedWorkingCore.modified T K :
                PreferredWorkingCoreData G x y z }).exteriorGraph.Adj
              E.certificate.bz
              ({ orientation := orientation
                 working := SelectedWorkingCore.modified T K :
                  PreferredWorkingCoreData G x y z }).exteriorY := by
          change G.Adj E.bz y
          rw [hbzT]
          exact T.other_root_adj_t₀.symm
        rcases (E.certificate.adj_bz_iff _).mp hby with
          hyz | hyPrime
        · exact False.elim (E.certificate.y_ne_z hyz)
        · exact hyPrime.symm
      have hyAdj :
          ∀ v :
              ({ orientation := orientation
                 working := SelectedWorkingCore.modified T K :
                  PreferredWorkingCoreData G x y z }).ExteriorVertex,
            ({ orientation := orientation
               working := SelectedWorkingCore.modified T K :
                PreferredWorkingCoreData G x y z }).exteriorGraph.Adj
                ({ orientation := orientation
                   working := SelectedWorkingCore.modified T K :
                    PreferredWorkingCoreData G x y z }).exteriorY v ↔
              v = E.certificate.bz := by
        intro v
        have hiff :=
          K.other_root_adj_iff_t₀_in_otherRegion v
        change G.Adj y v.1 ↔ v.1 = T.t₀ at hiff
        change G.Adj y v.1 ↔ v = E.certificate.bz
        rw [hiff]
        constructor
        · intro hvt
          apply Subtype.ext
          exact hvt.trans hbzT.symm
        · intro hvb
          have := congrArg Subtype.val hvb
          exact this.trans hbzT
      let A :
          ({ orientation := orientation
             working := SelectedWorkingCore.modified T K :
              PreferredWorkingCoreData G x y z }).ExteriorVertex → Prop :=
        fun v =>
          v =
              ({ orientation := orientation
                 working := SelectedWorkingCore.modified T K :
                  PreferredWorkingCoreData G x y z }).exteriorZ
                E.z_mem_otherRegion ∨
            v = E.certificate.bz ∨
              v =
                ({ orientation := orientation
                   working := SelectedWorkingCore.modified T K :
                    PreferredWorkingCoreData G x y z }).exteriorY
      have hclosed :
          ∀ ⦃u v :
              ({ orientation := orientation
                 working := SelectedWorkingCore.modified T K :
                  PreferredWorkingCoreData G x y z }).ExteriorVertex⦄,
            A u →
            ({ orientation := orientation
               working := SelectedWorkingCore.modified T K :
                PreferredWorkingCoreData G x y z }).exteriorGraph.Adj u v →
            A v := by
        intro u v hu huv
        rcases hu with huz | hub | huy
        · subst u
          exact Or.inr
            (Or.inl ((E.certificate.adj_z_iff v).mp huv))
        · subst u
          rcases (E.certificate.adj_bz_iff v).mp huv with
            hvz | hvPrime
          · exact Or.inl hvz
          · exact Or.inr (Or.inr (hvPrime.trans hprimeY))
        · subst u
          exact Or.inr (Or.inl ((hyAdj v).mp huv))
      have hall :
          ∀ v :
              ({ orientation := orientation
                 working := SelectedWorkingCore.modified T K :
                  PreferredWorkingCoreData G x y z }).ExteriorVertex,
            A v := by
        intro v
        obtain ⟨p⟩ :=
          E.certificate.connected.preconnected
            (({ orientation := orientation
                working := SelectedWorkingCore.modified T K :
                 PreferredWorkingCoreData G x y z }).exteriorZ
              E.z_mem_otherRegion) v
        exact predicate_of_walk A hclosed p (Or.inl rfl)
      have hsubset :
          K.rooted.otherRegion \ {y, z} ⊆ {E.bz} := by
        intro v hv
        have hvQ : v ∈ K.rooted.otherRegion :=
          (Finset.mem_sdiff.mp hv).1
        have hvAvoid : v ∉ ({y, z} : Finset V) :=
          (Finset.mem_sdiff.mp hv).2
        have hvy : v ≠ y := by
          intro hvy
          apply hvAvoid
          simp [hvy]
        have hvz : v ≠ z := by
          intro hvz
          apply hvAvoid
          simp [hvz]
        rcases hall ⟨v, hvQ⟩ with hvz' | hvb' | hvy'
        · exact False.elim
            (hvz (congrArg Subtype.val hvz'))
        · simpa using congrArg Subtype.val hvb'
        · exact False.elim
            (hvy (congrArg Subtype.val hvy'))
      have htwo :
          2 ≤ (K.rooted.otherRegion \ {y, z}).card :=
        K.two_le_otherRegion_sdiff_protected hxz
      have hcard :=
        Finset.card_le_card hsubset
      simp only [Finset.card_singleton] at hcard
      omega

end ExteriorZEndBlock

end PreferredWorkingCoreData

end COY

end DeanK5
