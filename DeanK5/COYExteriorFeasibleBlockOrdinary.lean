import DeanK5.COYExteriorFeasibleBlockCompression
import DeanK5.COYCoreAttachment

/-!
# Ordinary vertices of the selected feasible block

Apart from the anchor `b` and the possible second exception `zPrime`, a
vertex of the selected block is neither protected nor a cut vertex of the
exterior.  In the modified-core branch this also excludes the removed
vertex `t₀`, which is an exterior cut vertex.
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

/-- An ambient block vertex, regarded as a vertex of the exterior graph. -/
def exteriorVertex
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier) :
    P.ExteriorVertex :=
  ⟨v, C.ambientCarrier_subset_otherRegion hv⟩

@[simp] theorem exteriorVertex_val
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier) :
    (C.exteriorVertex hv).1 = v :=
  rfl

theorem exteriorVertex_mem_block
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier) :
    C.exteriorVertex hv ∈ C.block.carrier := by
  rw [C.mem_ambientCarrier] at hv
  obtain ⟨w, hwB, hwv⟩ := hv
  have heq :
      w = C.exteriorVertex
        (C.mem_ambientCarrier.mpr
          ⟨w, hwB, hwv⟩) := by
    apply Subtype.ext
    exact hwv
  exact heq ▸ hwB

theorem exteriorVertex_not_special
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier)
    (hvb : v ≠ C.b) (hvz : v ≠ C.zPrime) :
    C.exteriorVertex hv ∉
      cutVertices P.exteriorGraph ∪ P.exteriorProtected := by
  intro hspecial
  have hcovered :=
    C.anchor.special_subset
      (Finset.mem_inter.mpr
        ⟨C.exteriorVertex_mem_block hv, hspecial⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcovered
  rcases hcovered with hb | hz
  · exact hvb (congrArg Subtype.val hb)
  · exact hvz (congrArg Subtype.val hz)

theorem exteriorVertex_not_cut
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier)
    (hvb : v ≠ C.b) (hvz : v ≠ C.zPrime) :
    ¬IsCutVertex P.exteriorGraph (C.exteriorVertex hv) := by
  intro hcut
  apply C.exteriorVertex_not_special hv hvb hvz
  exact Finset.mem_union_left _
    ((mem_cutVertices_iff _ _).2 hcut)

theorem exteriorVertex_not_protected
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier)
    (hvb : v ≠ C.b) (hvz : v ≠ C.zPrime) :
    C.exteriorVertex hv ∉ P.exteriorProtected := by
  intro hprotected
  apply C.exteriorVertex_not_special hv hvb hvz
  exact Finset.mem_union_right _ hprotected

theorem ordinary_block_vertex_ne_y
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier)
    (hvb : v ≠ C.b) (hvz : v ≠ C.zPrime) :
    v ≠ y := by
  intro hvy
  apply C.exteriorVertex_not_protected hv hvb hvz
  rw [P.mem_exteriorProtected]
  exact Or.inl (by simpa using hvy)

theorem ordinary_block_vertex_ne_z
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier)
    (hvb : v ≠ C.b) (hvz : v ≠ C.zPrime) :
    v ≠ z := by
  intro hvz'
  apply C.exteriorVertex_not_protected hv hvb hvz
  rw [P.mem_exteriorProtected]
  exact Or.inr (by simpa using hvz')

/--
Every block vertex other than `b,zPrime` avoids the extra vertex excluded
from the working-core attachment estimate.
-/
theorem ordinary_block_vertex_ne_excluded
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier)
    (hvb : v ≠ C.b) (hvz : v ≠ C.zPrime) :
    v ≠ P.working.excludedVertex := by
  rcases P.working.excludedVertex_eq_otherRoot_or_exteriorCut with
    heq | ⟨hmem, hcut⟩
  · simpa [heq] using
      C.ordinary_block_vertex_ne_y hv hvb hvz
  · intro hve
    apply C.exteriorVertex_not_cut hv hvb hvz
    have hsubtype :
        C.exteriorVertex hv =
          (⟨P.working.excludedVertex, hmem⟩ :
            P.ExteriorVertex) := by
      apply Subtype.ext
      exact hve
    exact hsubtype ▸ hcut

/--
An exterior neighbour of a nonexceptional block vertex cannot leave the
block: otherwise that vertex would be an exterior cut vertex.
-/
theorem exterior_neighbor_mem_block
    (C : P.ExteriorFeasibleBlockChoice)
    {v : V} (hv : v ∈ C.ambientCarrier)
    (hvb : v ≠ C.b) (hvz : v ≠ C.zPrime)
    {w : P.ExteriorVertex}
    (hvw : P.exteriorGraph.Adj (C.exteriorVertex hv) w) :
    w ∈ C.block.carrier := by
  by_contra hw
  exact C.exteriorVertex_not_cut hv hvb hvz
    (C.block.isCutVertex_of_adj_outside
      P.exteriorGraph_connected
      (C.exteriorVertex_mem_block hv) hvw hw)

end PreferredWorkingCoreData.ExteriorFeasibleBlockChoice

end COY

end DeanK5
