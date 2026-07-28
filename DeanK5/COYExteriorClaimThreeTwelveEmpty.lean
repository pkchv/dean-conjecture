import DeanK5.COYCoreInitialPath
import DeanK5.COYExteriorClaimThreeTwelveBoundary
import DeanK5.COYComponentConnector
import DeanK5.Graph.BlockCutSides

/-!
# The empty-boundary branch of COY Claim 3.12

If `B - b` has no neighbour in `{x} ∪ S`, Claim 3.12(1) says that it has
no neighbour in the working core at all.  Two-connectivity then forces the
second distinguished block vertex `zPrime` to be a genuine exterior cut
vertex distinct from `b`.  This is the source content hidden behind the
statement that only cases (B2)(i) and (B3) can occur.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {P : PreferredWorkingCoreData G x y z}

/-- Data for the empty alternative of the initial boundary. -/
structure EmptyInitialBoundary
    (C : P.ExteriorFeasibleBlockChoice) : Prop where
  /-- No vertex of `{x} ∪ S` meets `B - b`. -/
  boundary_eq : C.initialBoundary = ∅

namespace EmptyInitialBoundary

variable {C : P.ExteriorFeasibleBlockChoice}

/-- In the empty-boundary branch no core vertex meets `B - b`. -/
theorem not_adj_core_interior
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {d v : V}
    (hd : d ∈ C.compressionInterior)
    (hvCore : v ∈ P.working.rooted.core.carrier) :
    ¬G.Adj d v := by
  intro hdv
  have hvBoundary :
      v ∈ C.initialBoundary :=
    C.core_attachment_mem_initialBoundary
      M hvCore hd hdv.symm
  rw [D.boundary_eq] at hvBoundary
  simp at hvBoundary

/--
If a vertex of `B - b` is not an exterior cut vertex, every neighbour
that survives deletion of `b` remains in `B - b`.
-/
theorem neighbor_mem_interior_of_not_cut
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z)
    {d v : V}
    (hd : d ∈ C.compressionInterior)
    (hdNotCut :
      ¬IsCutVertex P.exteriorGraph
        (C.exteriorVertex
          (Finset.mem_of_mem_erase hd)))
    (hdv : G.Adj d v)
    (hvb : v ≠ C.b) :
    v ∈ C.compressionInterior := by
  have hdB : d ∈ C.ambientCarrier :=
    Finset.mem_of_mem_erase hd
  have hvNotCore :
      v ∉ P.working.rooted.core.carrier := by
    intro hvCore
    exact D.not_adj_core_interior M hd hvCore hdv
  have hvRegion :
      v ∈ P.working.rooted.otherRegion :=
    P.working.rooted.otherRegion_componentRegion.closed
      (C.ambientCarrier_subset_otherRegion hdB)
      hdv hvNotCore
  let vE : P.ExteriorVertex := ⟨v, hvRegion⟩
  have hdvExterior :
      P.exteriorGraph.Adj
        (C.exteriorVertex hdB) vE :=
    hdv
  have hvBlock : vE ∈ C.block.carrier := by
    by_contra hvOutside
    exact hdNotCut
      (C.block.isCutVertex_of_adj_outside
        P.exteriorGraph_connected
        (C.exteriorVertex_mem_block hdB)
        hdvExterior hvOutside)
  have hvB : v ∈ C.ambientCarrier := by
    apply C.mem_ambientCarrier.mpr
    exact ⟨vE, hvBlock, rfl⟩
  exact Finset.mem_erase.mpr ⟨hvb, hvB⟩

/--
The empty boundary forces a cut vertex in `B - b`; feasibility then
identifies it with `zPrime`.
-/
theorem zPrime_mem_interior_and_isCutVertex
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    C.zPrime ∈ C.compressionInterior ∧
      IsCutVertex P.exteriorGraph
        (C.exteriorVertex C.zPrime_mem_ambientCarrier) := by
  classical
  have hxb : x ≠ C.b := by
    intro h
    have hbCore :
        C.b ∈ P.working.rooted.core.carrier := by
      rw [← h]
      exact P.working.rooted.core.root_mem_carrier
    exact
      Finset.disjoint_left.mp
        C.ambientCarrier_disjoint_core
        C.b_mem_ambientCarrier hbCore
  let ordinaryDeleted :
      {v : V // v ∉ ({C.b} : Finset V)} :=
    ⟨C.ordinary, by
      simpa using C.ordinary_ne_b⟩
  let xDeleted :
      {v : V // v ∉ ({C.b} : Finset V)} :=
    ⟨x, by simpa using hxb⟩
  have hdeletedConnected :
      (G.induce
        {v : V | v ∉ ({C.b} : Finset V)}).Connected :=
    M.underlying_two_connected.2
      {C.b} (by simp)
  obtain ⟨p⟩ :=
    hdeletedConnected.preconnected
      ordinaryDeleted xDeleted
  by_contra hconclusion
  push Not at hconclusion
  have hnoCut :
      ∀ (d : V) (hd : d ∈ C.compressionInterior),
        ¬IsCutVertex P.exteriorGraph
          (C.exteriorVertex
            (Finset.mem_of_mem_erase hd)) := by
    intro d hd hdCut
    have hdB : d ∈ C.ambientCarrier :=
      Finset.mem_of_mem_erase hd
    have hdBlock :
        C.exteriorVertex hdB ∈ C.block.carrier :=
      C.exteriorVertex_mem_block hdB
    have hdSpecial :
        C.exteriorVertex hdB ∈
          cutVertices P.exteriorGraph ∪
            P.exteriorProtected :=
      Finset.mem_union_left _
        ((mem_cutVertices_iff _ _).2 hdCut)
    have hcovered :=
      C.anchor.special_subset
        (Finset.mem_inter.mpr
          ⟨hdBlock, hdSpecial⟩)
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hcovered
    rcases hcovered with hdb | hdz
    · exact (Finset.mem_erase.mp hd).1
        (congrArg Subtype.val hdb)
    · have hdzAmbient : d = C.zPrime :=
        congrArg Subtype.val hdz
      have hzInterior :
          C.zPrime ∈ C.compressionInterior := by
        rw [← hdzAmbient]
        exact hd
      have hzCut :
          IsCutVertex P.exteriorGraph
            (C.exteriorVertex
              C.zPrime_mem_ambientCarrier) := by
        have hvertexEq :
            C.exteriorVertex hdB =
              C.exteriorVertex
                C.zPrime_mem_ambientCarrier := by
          apply Subtype.ext
          exact hdzAmbient
        exact hvertexEq ▸ hdCut
      exact hconclusion hzInterior hzCut
  have hclosed :
      ∀ {u v :
          {w : V // w ∉ ({C.b} : Finset V)}},
        u.1 ∈ C.compressionInterior →
        (G.induce
          {w : V | w ∉ ({C.b} : Finset V)}).Adj u v →
        v.1 ∈ C.compressionInterior := by
    intro u v hu huv
    apply D.neighbor_mem_interior_of_not_cut
      M hu (hnoCut u.1 hu) huv
    intro hvb
    apply v.2
    simpa [hvb]
  have hwalkClosed :
      ∀ {u v :
          {w : V // w ∉ ({C.b} : Finset V)}},
        (G.induce
          {w : V | w ∉ ({C.b} : Finset V)}).Walk u v →
        u.1 ∈ C.compressionInterior →
        v.1 ∈ C.compressionInterior := by
    intro u v W hu
    induction W with
    | nil =>
        exact hu
    | @cons a b c hab W ih =>
        exact ih (hclosed hu hab)
  have hxInterior :
      x ∈ C.compressionInterior :=
    hwalkClosed p C.ordinary_mem_compressionInterior
  have hxB : x ∈ C.ambientCarrier :=
    Finset.mem_of_mem_erase hxInterior
  exact
    Finset.disjoint_left.mp
      C.ambientCarrier_disjoint_core
      hxB P.working.rooted.core.root_mem_carrier

theorem zPrime_ne_b
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    C.zPrime ≠ C.b :=
  (Finset.mem_erase.mp
    (D.zPrime_mem_interior_and_isCutVertex M).1).1

theorem zPrime_isCutVertex
    (D : EmptyInitialBoundary C)
    (M : MinimalCounterexample q G x y z) :
    IsCutVertex P.exteriorGraph
      (C.exteriorVertex C.zPrime_mem_ambientCarrier) :=
  (D.zPrime_mem_interior_and_isCutVertex M).2

end EmptyInitialBoundary

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
