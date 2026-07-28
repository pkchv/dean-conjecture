import DeanK5.COYComponentConnector
import DeanK5.COYPathOperations
import DeanK5.COYSideInstance

/-!
# Lifting the COY cut-side recursive family

The recursive call in COY Claim 3.2 produces admissible paths from the
root on one side of a cut vertex to that cut vertex.  This file maps the
family into the ambient graph and appends one fixed path through the
opposite component.  Explicit support statements certify that every
concatenation is still a simple path.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY

namespace CutSide

variable [Fintype V] [DecidableEq V]
  {q : ℕ} {G : SimpleGraph V} {Q R : Finset V}
  {c x y : V}

/-- Map an admissible family in an induced cut side back to the ambient graph. -/
def mapFamily
    (hx : x ∈ Q)
    (F : AdmissiblePathFamily
      (graph G Q c) (root Q c x hx) (cut Q c) q) :
    AdmissiblePathFamily G x c q := by
  change AdmissiblePathFamily G
    ((root Q c x hx : Vertex Q c) : V)
    ((cut Q c : Vertex Q c) : V) q
  exact
    F.mapInjectiveHom
      (embedding G Q c).toHom
      (embedding G Q c).injective

omit [Fintype V] in
/-- Every vertex of a mapped cut-side path remains in that cut side. -/
theorem mapFamily_support_subset
    (hx : x ∈ Q)
    (F : AdmissiblePathFamily
      (graph G Q c) (root Q c x hx) (cut Q c) q)
    (i : Fin q) {v : V}
    (hv : v ∈ ((mapFamily hx F).path i).walk.support) :
    v ∈ vertices Q c := by
  change v ∈
    ((F.path i).mapInjectiveHom
      (embedding G Q c).toHom
      (embedding G Q c).injective).walk.support at hv
  have hvRange :=
    SimplePath.mem_range_of_mem_mapInjectiveHom_support
      (P := F.path i)
      (f := (embedding G Q c).toHom)
      (hinj := (embedding G Q c).injective)
      hv
  obtain ⟨w, rfl⟩ := hvRange
  exact w.2

/--
Append one path through a disjoint opposite component to every member of
the recursively obtained cut-side family.
-/
theorem lift_across_disjoint_component
    (hQ : ComponentRegion G {c} Q)
    (hR : ComponentRegion G {c} R)
    (hQR : Disjoint Q R)
    (hconn : G.Connected)
    (hx : x ∈ Q) (hy : y ∈ R)
    (F : AdmissiblePathFamily
      (graph G Q c) (root Q c x hx) (cut Q c) q) :
    Nonempty (AdmissiblePathFamily G x y q) := by
  obtain ⟨P, hPtail⟩ :=
    hR.exists_path_from_singleton_boundary hconn hy
  let mapped := mapFamily hx F
  have hdisjoint :
      ∀ i,
        (mapped.path i).walk.support.Disjoint
          P.walk.support.tail := by
    intro i
    apply List.disjoint_left.mpr
    intro v hvMapped hvP
    have hvSide : v ∈ vertices Q c :=
      mapFamily_support_subset hx F i
        (by simpa [mapped] using hvMapped)
    have hvR : v ∈ R := hPtail v hvP
    have hvClass : v = c ∨ v ∈ Q := by
      simpa [vertices] using hvSide
    rcases hvClass with rfl | hvQ
    · exact hR.not_mem_separator hvR (by simp)
    · exact Finset.disjoint_left.mp hQR hvQ hvR
  exact ⟨mapped.appendFixed P hdisjoint⟩

end CutSide

end COY

end DeanK5
