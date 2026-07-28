import DeanK5.Graph.Blocks
import DeanK5.EndLobeExistence

/-!
# End blocks from cardinality-minimal lobe regions

This file turns the lobe-region minimization used by the structural proof
into a bridge-inclusive block certificate.  A minimal lobe closure is either
a two-vertex bridge block or has order at least three, in which case the
existing pruning argument makes it 2-connected.  Its one-vertex boundary
then proves maximality among all nonseparable carriers in the ambient graph.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

namespace LobeRegion

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
If some ambient vertex lies outside a lobe closure, then the lobe boundary
is a cut vertex of the ambient connected graph.
-/
theorem isCutVertex_of_not_mem_carrier
    (hconnected : G.Connected)
    (L : LobeRegion G)
    {w : V} (hw : w ∉ L.carrier) :
    IsCutVertex G L.cut := by
  obtain ⟨q, hqInner⟩ := L.inner_nonempty
  have hqNeCut : q ≠ L.cut := by
    intro h
    exact L.cut_not_inner (h ▸ hqInner)
  have hwNeCut : w ≠ L.cut := by
    intro h
    apply hw
    rw [h]
    exact Finset.mem_insert_self _ _
  refine
    ⟨q, w, hqNeCut, hwNeCut,
      hconnected.preconnected q w, ?_⟩
  intro hreachable
  obtain ⟨p⟩ := hreachable
  let inclusion :
      deleteVertices G {L.cut} →g G :=
    (Embedding.induce
      {v : V | v ∉ ({L.cut} : Finset V)}).toHom
  let pG : G.Walk q w :=
    p.map inclusion
  have havoid :
      ∀ v ∈ pG.support,
        v ∉ ({L.cut} : Finset V) := by
    intro v hv
    change v ∈ (p.map inclusion).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨a, -, hav⟩ := List.mem_map.mp hv
    change a.1 = v at hav
    have haNeCut : a.1 ≠ L.cut := by
      simpa using a.2
    simpa [hav] using haNeCut
  have hwInner :=
    L.componentRegion.endpoint_mem_of_walk_avoiding_separator
      hqInner pG havoid
  exact hw (Finset.mem_insert.mpr (Or.inr hwInner))

end LobeRegion

namespace EndBlock

variable [DecidableEq V]
  {G : SimpleGraph V}

/--
Deleting an ambient carrier vertex in one step is isomorphic to first
inducing on the carrier and then deleting the corresponding subtype vertex.
-/
private def eraseInduceIso
    (S : Finset V) {v : V} :
    (G.induce (↑S : Set V)).induce
        {w : (↑S : Set V) | w.1 ≠ v} ≃g
      G.induce (↑(S.erase v) : Set V) where
  toEquiv := {
    toFun := fun w =>
      ⟨w.1.1, Finset.mem_erase.mpr ⟨w.2, w.1.2⟩⟩
    invFun := fun w =>
      ⟨⟨w.1, Finset.mem_of_mem_erase w.2⟩,
        (Finset.mem_erase.mp w.2).1⟩
    left_inv := by
      intro w
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro w
      apply Subtype.ext
      rfl
  }
  map_rel_iff' := Iff.rfl

/--
A 2-connected induced graph supplies the carrier-level nonseparability
predicate used by `GraphBlock`.
-/
private theorem nonseparable_of_induce_twoConnected
    (S : Finset V)
    (htwo : IsTwoConnected (G.induce (↑S : Set V))) :
    IsNonseparableCarrier G S := by
  have hcard :
      2 ≤ S.card := by
    have horder := htwo.1
    simpa using (show 2 ≤ Fintype.card (↑S : Set V) by omega)
  refine {
    card_ge_two := hcard
    connected := ?_
    delete_connected := ?_
  }
  · have hempty :=
      htwo.2
        (∅ : Finset (↑S : Set V)) (by simp)
    have hset :
        {w : (↑S : Set V) |
          w ∉ (∅ : Finset (↑S : Set V))} =
            Set.univ := by
      ext w
      simp
    rw [hset] at hempty
    exact
      (SimpleGraph.Iso.connected_iff
        (SimpleGraph.induceUnivIso
          (G.induce (↑S : Set V)))).mp hempty
  · intro v hv
    let vS : (↑S : Set V) := ⟨v, hv⟩
    have hdelete :=
      htwo.2 ({vS} : Finset (↑S : Set V)) (by simp)
    have hset :
        {w : (↑S : Set V) |
          w ∉ ({vS} : Finset (↑S : Set V))} =
            {w : (↑S : Set V) | w.1 ≠ v} := by
      ext w
      simp only [Finset.mem_singleton]
      constructor
      · intro hw hval
        exact hw (Subtype.ext hval)
      · intro hval hw
        exact hval (congrArg Subtype.val hw)
    rw [hset] at hdelete
    exact
      (SimpleGraph.Iso.connected_iff
        (eraseInduceIso (G := G) S)).mp hdelete

variable [Fintype V]

/--
The closure of an interior-cardinality-minimal lobe region is
nonseparable.  This includes the two-vertex bridge case.
-/
theorem minimal_nonseparable
    (L₀ L : LobeRegion G)
    (hwithin : L.Within L₀.inner L₀.cut)
    (hminimal :
      ∀ K : LobeRegion G,
        K.Within L₀.inner L₀.cut →
          L.inner.card ≤ K.inner.card) :
    IsNonseparableCarrier G L.carrier := by
  have hcardTwo :
      2 ≤ L.carrier.card := by
    obtain ⟨q, hqInner⟩ := L.inner_nonempty
    have hpair :
        ({L.cut, q} : Finset V) ⊆ L.carrier := by
      intro w hw
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr hqInner)
    have hpairCard :
        ({L.cut, q} : Finset V).card = 2 := by
      have hcutNeQ : L.cut ≠ q := by
        intro h
        apply L.cut_not_inner
        rw [h]
        exact hqInner
      simp [hcutNeQ]
    calc
      2 = ({L.cut, q} : Finset V).card := hpairCard.symm
      _ ≤ L.carrier.card :=
        Finset.card_le_card hpair
  by_cases hthree : 3 ≤ L.carrier.card
  · have horder :
        3 ≤ Fintype.card (↑L.carrier : Set V) := by
      simpa using hthree
    have htwo :=
      ClassicalGraphTheory.minimal_within_block_two_connected_of_three_le_card
        L₀ L hwithin hminimal horder
    exact nonseparable_of_induce_twoConnected
      L.carrier htwo
  · have hcardEq :
        L.carrier.card = 2 := by
      omega
    obtain ⟨q, hqInner, hcq⟩ :=
      L.cut_adj_inner
    have hpairSubset :
        ({L.cut, q} : Finset V) ⊆ L.carrier := by
      intro w hw
      simp only [Finset.mem_insert,
        Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr hqInner)
    have hpairCard :
        ({L.cut, q} : Finset V).card = 2 := by
      simp [hcq.ne]
    have hcarrierEq :
        L.carrier = {L.cut, q} := by
      symm
      exact Finset.eq_of_subset_of_card_le
        hpairSubset (by omega)
    rw [hcarrierEq]
    exact IsNonseparableCarrier.pair_of_adj hcq

/--
Any nonseparable carrier containing a lobe closure lies inside that closure.
The proof deletes the lobe cut and follows a path from the lobe interior;
the one-vertex boundary prevents that path from leaving the interior.
-/
def maximalOfNonseparable
    (L : LobeRegion G)
    (hL : IsNonseparableCarrier G L.carrier) :
    GraphBlock G := by
  refine {
    carrier := L.carrier
    nonseparable := hL
    maximal := ?_
  }
  intro T hT hLT w hwT
  by_cases hwCut : w = L.cut
  · subst w
    exact Finset.mem_insert_self _ _
  obtain ⟨q, hqInner⟩ := L.inner_nonempty
  have hqCarrier : q ∈ L.carrier :=
    Finset.mem_insert.mpr (Or.inr hqInner)
  have hqT : q ∈ T :=
    hLT hqCarrier
  have hqNeCut : q ≠ L.cut := by
    intro h
    exact L.cut_not_inner (h ▸ hqInner)
  have hqErase : q ∈ T.erase L.cut :=
    Finset.mem_erase.mpr ⟨hqNeCut, hqT⟩
  have hwErase : w ∈ T.erase L.cut :=
    Finset.mem_erase.mpr ⟨hwCut, hwT⟩
  let qD : (↑(T.erase L.cut) : Set V) :=
    ⟨q, hqErase⟩
  let wD : (↑(T.erase L.cut) : Set V) :=
    ⟨w, hwErase⟩
  obtain ⟨p⟩ :=
    (hT.connected_erase L.cut).preconnected qD wD
  let pG : G.Walk q w :=
    p.map
      (Embedding.induce
        (↑(T.erase L.cut) : Set V)).toHom
  have havoid :
      ∀ v ∈ pG.support,
        v ∉ ({L.cut} : Finset V) := by
    intro v hv
    change v ∈
      (p.map
        (Embedding.induce
          (↑(T.erase L.cut) : Set V)).toHom).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨a, -, hav⟩ := List.mem_map.mp hv
    change a.1 = v at hav
    have haNe :
        a.1 ≠ L.cut :=
      (Finset.mem_erase.mp a.2).1
    simpa [hav] using haNe
  have hwInner :=
    L.componentRegion.endpoint_mem_of_walk_avoiding_separator
      hqInner pG havoid
  exact Finset.mem_insert.mpr (Or.inr hwInner)

/-- A cardinality-minimal lobe region determines a global graph block. -/
def minimalGraphBlock
    (L₀ L : LobeRegion G)
    (hwithin : L.Within L₀.inner L₀.cut)
    (hminimal :
      ∀ K : LobeRegion G,
        K.Within L₀.inner L₀.cut →
          L.inner.card ≤ K.inner.card) :
    GraphBlock G :=
  maximalOfNonseparable L
    (minimal_nonseparable L₀ L hwithin hminimal)

/--
If the ambient graph is connected, deleting an inner vertex of a
nonseparable lobe closure leaves the entire ambient graph connected.
-/
theorem delete_inner_connected
    (hconnected : G.Connected)
    (L : LobeRegion G)
    (hL : IsNonseparableCarrier G L.carrier)
    {v : V} (hvInner : v ∈ L.inner) :
    (deleteVertices G {v}).Connected := by
  have hvCarrier : v ∈ L.carrier :=
    Finset.mem_insert.mpr (Or.inr hvInner)
  have hcutNeV : L.cut ≠ v := by
    intro h
    exact L.cut_not_inner (h ▸ hvInner)
  let cutD :
      {w : V // w ∉ ({v} : Finset V)} :=
    ⟨L.cut, by simpa using hcutNeV⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨cutD, ?_⟩
  intro wD
  by_cases hwInner : wD.1 ∈ L.inner
  · have hwCarrier : wD.1 ∈ L.carrier :=
      Finset.mem_insert.mpr (Or.inr hwInner)
    have hcutCarrier : L.cut ∈ L.carrier :=
      Finset.mem_insert_self _ _
    have hcutErase :
        L.cut ∈ L.carrier.erase v :=
      Finset.mem_erase.mpr ⟨hcutNeV, hcutCarrier⟩
    have hwNeV : wD.1 ≠ v := by
      simpa using wD.2
    have hwErase :
        wD.1 ∈ L.carrier.erase v :=
      Finset.mem_erase.mpr ⟨hwNeV, hwCarrier⟩
    let cutB : (↑(L.carrier.erase v) : Set V) :=
      ⟨L.cut, hcutErase⟩
    let wB : (↑(L.carrier.erase v) : Set V) :=
      ⟨wD.1, hwErase⟩
    have hsubset :
        (↑(L.carrier.erase v) : Set V) ⊆
          {w : V | w ∉ ({v} : Finset V)} := by
      intro a ha
      have hav : a ≠ v :=
        (Finset.mem_erase.mp ha).1
      simpa using hav
    have hreach :=
      (hL.delete_connected v hvCarrier).preconnected
        cutB wB
    have hmapped :=
      hreach.map
        (G.induceHomOfLE hsubset).toHom
    have hcutEq :
        (G.induceHomOfLE hsubset) cutB = cutD := by
      apply Subtype.ext
      rfl
    have hwEq :
        (G.induceHomOfLE hsubset) wB = wD := by
      apply Subtype.ext
      rfl
    simpa [hcutEq, hwEq] using hmapped
  · obtain ⟨p, hp⟩ :=
      hconnected.exists_isPath wD.1 L.cut
    let P : SimplePath G wD.1 L.cut :=
      ⟨p, hp⟩
    have havoidInner :=
      L.simplePath_to_cut_avoids_inner
        hwInner P
    have hsupport :
        ∀ a ∈ P.walk.support,
          a ∈ {w : V | w ∉ ({v} : Finset V)} := by
      intro a ha
      have haNotInner :=
        havoidInner a ha
      have hav : a ≠ v := by
        intro h
        exact haNotInner (h ▸ hvInner)
      simpa using hav
    let pD :=
      P.walk.induce
        {w : V | w ∉ ({v} : Finset V)}
        hsupport
    have hstart :
        (⟨wD.1,
          hsupport wD.1 P.walk.start_mem_support⟩ :
            {w : V // w ∉ ({v} : Finset V)}) =
          wD := by
      apply Subtype.ext
      rfl
    have hend :
        (⟨L.cut,
          hsupport L.cut P.walk.end_mem_support⟩ :
            {w : V // w ∉ ({v} : Finset V)}) =
          cutD := by
      apply Subtype.ext
      rfl
    refine ⟨?_⟩
    simpa [hstart, hend] using pD.reverse

/--
An inner vertex of a nonseparable lobe closure is not a cut vertex of the
ambient connected graph.
-/
theorem not_isCutVertex_of_mem_inner
    (hconnected : G.Connected)
    (L : LobeRegion G)
    (hL : IsNonseparableCarrier G L.carrier)
    {v : V} (hvInner : v ∈ L.inner) :
    ¬IsCutVertex G v := by
  have hcutNeV : L.cut ≠ v := by
    intro h
    apply L.cut_not_inner
    rw [h]
    exact hvInner
  have hsurvives :
      Nonempty {w : V // w ≠ v} :=
    ⟨⟨L.cut, hcutNeV⟩⟩
  exact
    (not_isCutVertex_iff_delete_connected
      G v hconnected hsurvives).2
      (delete_inner_connected hconnected L hL hvInner)

/--
A general end-block certificate selected inside an initial lobe region.

The selected region is minimal by inner-vertex cardinality among all lobe
regions within the initial one.  Its closure is a global graph block, and
none of its inner vertices is a cut vertex of the ambient graph.
-/
structure Certificate
    (G : SimpleGraph V) (initial : LobeRegion G) where
  /-- The selected cardinality-minimal lobe region. -/
  region : LobeRegion G
  /-- The selected region lies within the initial lobe region. -/
  withinInitial :
    region.Within initial.inner initial.cut
  /-- The selected region has minimum inner-vertex cardinality. -/
  minimal :
    ∀ K : LobeRegion G,
      K.Within initial.inner initial.cut →
        region.inner.card ≤ K.inner.card
  /-- The global graph block carried by the selected lobe closure. -/
  block : GraphBlock G
  /-- The block carrier is exactly the selected lobe closure. -/
  block_carrier :
    block.carrier = region.carrier
  /-- No inner vertex is a cut vertex of the ambient graph. -/
  inner_not_cut :
    ∀ ⦃v : V⦄, v ∈ region.inner →
      ¬IsCutVertex G v

namespace Certificate

variable {initial : LobeRegion G}

/-- The certified block carrier is the cut vertex adjoined to the interior. -/
@[simp]
theorem carrier_eq_insert
    (C : Certificate G initial) :
    C.block.carrier =
      insert C.region.cut C.region.inner := by
  rw [C.block_carrier]
  rfl

/-- A certified end block has a nonempty interior. -/
theorem inner_nonempty
    (C : Certificate G initial) :
    C.region.inner.Nonempty :=
  C.region.inner_nonempty

/--
If the certified block has at most two vertices, then its nonempty interior
has exactly one vertex.
-/
theorem inner_card_eq_one_of_block_card_le_two
    (C : Certificate G initial)
    (hcard : C.block.carrier.card ≤ 2) :
    C.region.inner.card = 1 := by
  have hcarrierCard :
      C.block.carrier.card =
        C.region.inner.card + 1 := by
    rw [C.carrier_eq_insert,
      Finset.card_insert_of_notMem
        C.region.cut_not_inner]
  have hinnerPos :
      1 ≤ C.region.inner.card :=
    Finset.card_pos.mpr C.inner_nonempty
  omega

/--
Every edge leaving the certified interior has its other endpoint either
inside the interior or at the distinguished cut vertex.
-/
theorem inner_closed
    (C : Certificate G initial)
    {x y : V} (hx : x ∈ C.region.inner)
    (hxy : G.Adj x y) :
    y ∈ C.region.inner ∨ y = C.region.cut :=
  C.region.closed hx hxy

/--
The distinguished boundary vertex is the only possible ambient cut vertex
in the certified block carrier.
-/
theorem cutVertex_eq_cut
    (C : Certificate G initial)
    {v : V} (hv : v ∈ C.block.carrier)
    (hcut : IsCutVertex G v) :
    v = C.region.cut := by
  rw [C.block_carrier] at hv
  rcases Finset.mem_insert.mp hv with hvCut | hvInner
  · exact hvCut
  · exact False.elim (C.inner_not_cut hvInner hcut)

end Certificate

/--
Package a chosen minimal lobe region as a general end-block certificate.
-/
def certificateOfMinimal
    (hconnected : G.Connected)
    (L₀ L : LobeRegion G)
    (hwithin : L.Within L₀.inner L₀.cut)
    (hminimal :
      ∀ K : LobeRegion G,
        K.Within L₀.inner L₀.cut →
          L.inner.card ≤ K.inner.card) :
    Certificate G L₀ := by
  have hnonseparable :=
    minimal_nonseparable L₀ L hwithin hminimal
  exact {
    region := L
    withinInitial := hwithin
    minimal := hminimal
    block := maximalOfNonseparable L hnonseparable
    block_carrier := rfl
    inner_not_cut := by
      intro v hv
      exact
        not_isCutVertex_of_mem_inner
          hconnected L hnonseparable hv
  }

/--
Every lobe region of a finite connected graph contains a general end-block
certificate.
-/
theorem exists_certificate
    (hconnected : G.Connected)
    (L₀ : LobeRegion G) :
    Nonempty (Certificate G L₀) := by
  obtain ⟨L, hwithin, hminimal⟩ :=
    L₀.exists_minimal_within
  exact
    ⟨certificateOfMinimal
      hconnected L₀ L hwithin hminimal⟩

end EndBlock

end DeanK5
