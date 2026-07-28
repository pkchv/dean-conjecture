import DeanK5.Graph.CutVertices
import Mathlib.Order.Preorder.Finite

/-!
# Blocks of a finite simple graph

This file provides the carrier-level block theory needed by the structural
part of the proof.  A nonseparable carrier has at least two vertices, induces
a connected graph, and remains connected after any one of its vertices is
deleted.  Thus a bridge together with its two ends is allowed, as are the
usual vertex sets of 2-connected blocks.

A `GraphBlock` is an inclusion-maximal nonseparable carrier.  Working with
finite vertex carriers keeps maximal extension elementary and makes the
intersection theorem independent of any later block-cut-tree encoding.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
A finite vertex carrier is nonseparable when it has at least two vertices,
is connected, and has no cut vertex relative to its induced graph.

The deletion condition is deliberately imposed only on vertices of the
carrier.  On a two-vertex carrier it says that each surviving singleton is
connected, so an edge is a nonseparable carrier.
-/
structure IsNonseparableCarrier
    [DecidableEq V] (G : SimpleGraph V) (S : Finset V) : Prop where
  /-- A block carrier has at least two vertices. -/
  card_ge_two : 2 ≤ S.card
  /-- The induced graph on the carrier is connected. -/
  connected : (G.induce (↑S : Set V)).Connected
  /-- Deleting any carrier vertex leaves a connected induced graph. -/
  delete_connected :
    ∀ v ∈ S, (G.induce (↑(S.erase v) : Set V)).Connected

namespace IsNonseparableCarrier

variable [DecidableEq V] {G : SimpleGraph V} {S T : Finset V}

/-- Deleting a vertex outside a nonseparable carrier changes nothing. -/
theorem connected_erase
    (hS : IsNonseparableCarrier G S) (v : V) :
    (G.induce (↑(S.erase v) : Set V)).Connected := by
  by_cases hv : v ∈ S
  · exact hS.delete_connected v hv
  · rw [Finset.erase_eq_of_notMem hv]
    exact hS.connected

/-- The endpoints of an edge form a nonseparable carrier. -/
theorem pair_of_adj
    {u v : V} (huv : G.Adj u v) :
    IsNonseparableCarrier G {u, v} := by
  have huvNe : u ≠ v := huv.ne
  refine {
    card_ge_two := by simp [huvNe]
    connected := by
      have hset :
          (↑({u, v} : Finset V) : Set V) =
            ({u, v} : Set V) := by
        ext a
        simp
      rw [hset]
      exact G.induce_pair_connected_of_adj huv
    delete_connected := ?_
  }
  intro w hw
  let R : Finset V := ({u, v} : Finset V).erase w
  have hpairCard : ({u, v} : Finset V).card = 2 := by
    simp [huvNe]
  have hRCard : R.card = 1 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hw, hpairCard]
  letI : Nonempty (↑R : Set V) := by
    have hRNonempty : R.Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hRNonempty
    exact ⟨⟨a, ha⟩⟩
  letI : Subsingleton (↑R : Set V) := by
    constructor
    intro a b
    apply Subtype.ext
    exact
      (Finset.card_le_one.mp (by omega))
        a.1 a.2 b.1 b.2
  change (G.induce (↑R : Set V)).Connected
  exact SimpleGraph.Connected.of_subsingleton

/--
Two nonseparable carriers with at least two common vertices have a
nonseparable union.

After deleting any one vertex, at least one common vertex remains.  The two
connected deletions can therefore still be joined across their intersection.
-/
theorem union
    (hS : IsNonseparableCarrier G S)
    (hT : IsNonseparableCarrier G T)
    (hinter : 2 ≤ (S ∩ T).card) :
    IsNonseparableCarrier G (S ∪ T) := by
  have hinterNonempty : ((↑S : Set V) ∩ (↑T : Set V)).Nonempty := by
    obtain ⟨w, hw⟩ :=
      Finset.card_pos.mp (by omega :
        0 < (S ∩ T).card)
    exact ⟨w, by simpa using hw⟩
  refine {
    card_ge_two := hS.card_ge_two.trans
      (Finset.card_le_card (Finset.subset_union_left))
    connected := by
      have hset :
          (↑(S ∪ T) : Set V) =
            (↑S : Set V) ∪ (↑T : Set V) := by
        ext a
        simp
      rw [hset]
      exact G.induce_union_connected
        hS.connected.preconnected hT.connected.preconnected
        hinterNonempty
    delete_connected := ?_
  }
  intro v hv
  obtain ⟨w, hwST, hwv⟩ :=
    Finset.exists_mem_ne hinter v
  have hwS : w ∈ S := (Finset.mem_inter.mp hwST).1
  have hwT : w ∈ T := (Finset.mem_inter.mp hwST).2
  have hwSErase : w ∈ S.erase v := by
    exact Finset.mem_erase.mpr ⟨hwv, hwS⟩
  have hwTErase : w ∈ T.erase v := by
    exact Finset.mem_erase.mpr ⟨hwv, hwT⟩
  have hinterErase :
      ((↑(S.erase v) : Set V) ∩
        (↑(T.erase v) : Set V)).Nonempty :=
    ⟨w, hwSErase, hwTErase⟩
  have hconnected :=
    G.induce_union_connected
      (hS.connected_erase v).preconnected
      (hT.connected_erase v).preconnected
      hinterErase
  have hset :
      (↑((S ∪ T).erase v) : Set V) =
        (↑(S.erase v) : Set V) ∪
          (↑(T.erase v) : Set V) := by
    ext a
    simp only [Set.mem_union]
    aesop
  rw [hset]
  exact hconnected

end IsNonseparableCarrier

/-- An inclusion-maximal nonseparable finite vertex carrier. -/
structure GraphBlock
    [DecidableEq V] (G : SimpleGraph V) where
  /-- The vertices of the block. -/
  carrier : Finset V
  /-- The carrier is nonseparable. -/
  nonseparable : IsNonseparableCarrier G carrier
  /-- No strictly larger nonseparable carrier contains this one. -/
  maximal :
    ∀ ⦃T : Finset V⦄,
      IsNonseparableCarrier G T →
      carrier ⊆ T →
      T ⊆ carrier

namespace GraphBlock

variable [DecidableEq V] {G : SimpleGraph V}

/-- Graph blocks are determined by their carriers. -/
@[ext]
theorem ext {B C : GraphBlock G}
    (hcarrier : B.carrier = C.carrier) :
    B = C := by
  cases B
  cases C
  cases hcarrier
  rfl

/-- A block carrier has at least two vertices. -/
theorem card_ge_two (B : GraphBlock G) :
    2 ≤ B.carrier.card :=
  B.nonseparable.card_ge_two

/-- A block induces a connected graph. -/
theorem connected (B : GraphBlock G) :
    (G.induce (↑B.carrier : Set V)).Connected :=
  B.nonseparable.connected

/-- Deleting a vertex of a block leaves its induced carrier connected. -/
theorem delete_connected (B : GraphBlock G)
    {v : V} (hv : v ∈ B.carrier) :
    (G.induce (↑(B.carrier.erase v) : Set V)).Connected :=
  B.nonseparable.delete_connected v hv

/--
Every nonseparable carrier of a finite graph extends to a graph block.
-/
theorem exists_extension
    [Fintype V]
    {S : Finset V}
    (hS : IsNonseparableCarrier G S) :
    ∃ B : GraphBlock G, S ⊆ B.carrier := by
  classical
  obtain ⟨T, hST, hTmax⟩ :=
    Finite.exists_le_maximal (p := IsNonseparableCarrier G) hS
  refine ⟨{
    carrier := T
    nonseparable := hTmax.1
    maximal := ?_
  }, hST⟩
  intro U hU hTU
  exact hTmax.2 hU hTU

/-- Every edge of a finite graph lies in a graph block. -/
theorem exists_of_adj
    [Fintype V]
    {u v : V} (huv : G.Adj u v) :
    ∃ B : GraphBlock G, u ∈ B.carrier ∧ v ∈ B.carrier := by
  obtain ⟨B, hpair⟩ :=
    exists_extension
      (IsNonseparableCarrier.pair_of_adj huv)
  exact ⟨B, hpair (by simp), hpair (by simp)⟩

/--
If the whole graph is connected, has at least two vertices, and has no
vertex whose deletion disconnects it, then the whole carrier is a block.
-/
def univ
    [Fintype V]
    (hcard : 2 ≤ Fintype.card V)
    (hconnected : G.Connected)
    (hdelete :
      ∀ v : V, (G.induce {w : V | w ≠ v}).Connected) :
    GraphBlock G where
  carrier := Finset.univ
  nonseparable := {
    card_ge_two := by simpa using hcard
    connected := by
      have hset :
          (↑(Finset.univ : Finset V) : Set V) =
            Set.univ := by
        ext v
        simp
      rw [hset]
      exact
        (SimpleGraph.Iso.connected_iff
          (SimpleGraph.induceUnivIso G)).2 hconnected
    delete_connected := by
      intro v hv
      have hset :
          (↑((Finset.univ : Finset V).erase v) : Set V) =
            {w : V | w ≠ v} := by
        ext w
        simp [eq_comm]
      rw [hset]
      exact hdelete v
  }
  maximal := by
    intro T hT hsub
    exact Finset.subset_univ T

@[simp] theorem univ_carrier
    [Fintype V]
    (hcard : 2 ≤ Fintype.card V)
    (hconnected : G.Connected)
    (hdelete :
      ∀ v : V, (G.induce {w : V | w ≠ v}).Connected) :
    (GraphBlock.univ hcard hconnected hdelete).carrier =
      Finset.univ :=
  rfl

/--
A finite connected graph of order at least two with no cut vertex is itself
a block.
-/
def ofConnectedHasNoCutVertex
    [Fintype V]
    (hcard : 2 ≤ Fintype.card V)
    (hconnected : G.Connected)
    (hnoCut : HasNoCutVertex G) :
    GraphBlock G :=
  GraphBlock.univ hcard hconnected fun v => by
    have hsurvives :
        Nonempty {w : V // w ≠ v} := by
      have honeLt :
          1 < (Finset.univ : Finset V).card := by
        rw [Finset.card_univ]
        omega
      obtain ⟨w, -, hwv⟩ :=
        Finset.exists_mem_ne honeLt v
      exact ⟨⟨w, hwv⟩⟩
    have hdelete :
        (deleteVertices G {v}).Connected :=
      (not_isCutVertex_iff_delete_connected
        G v hconnected hsurvives).1 (hnoCut v)
    have hset :
        {w : V | w ∉ ({v} : Finset V)} =
          {w : V | w ≠ v} := by
      ext w
      simp
    change
      (G.induce {w : V | w ∉ ({v} : Finset V)}).Connected
        at hdelete
    rw [hset] at hdelete
    exact hdelete

@[simp] theorem ofConnectedHasNoCutVertex_carrier
    [Fintype V]
    (hcard : 2 ≤ Fintype.card V)
    (hconnected : G.Connected)
    (hnoCut : HasNoCutVertex G) :
    (GraphBlock.ofConnectedHasNoCutVertex
      hcard hconnected hnoCut).carrier =
        Finset.univ :=
  rfl

/--
Distinct blocks of a finite graph share at most one vertex.
-/
theorem inter_card_le_one
    (B C : GraphBlock G) (hne : B ≠ C) :
    (B.carrier ∩ C.carrier).card ≤ 1 := by
  by_contra hnot
  have hinter :
      2 ≤ (B.carrier ∩ C.carrier).card := by
    omega
  have hunion :
      IsNonseparableCarrier G (B.carrier ∪ C.carrier) :=
    B.nonseparable.union C.nonseparable hinter
  have hunionB :
      B.carrier ∪ C.carrier ⊆ B.carrier :=
    B.maximal hunion Finset.subset_union_left
  have hCB : C.carrier ⊆ B.carrier := by
    intro v hv
    exact hunionB (Finset.mem_union_right _ hv)
  have hBC : B.carrier ⊆ C.carrier :=
    C.maximal B.nonseparable hCB
  have hcarrier : B.carrier = C.carrier :=
    Finset.Subset.antisymm hBC hCB
  exact hne (GraphBlock.ext hcarrier)

end GraphBlock

end DeanK5
