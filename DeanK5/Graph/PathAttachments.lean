import DeanK5.Graph.Basic

/-!
# Endpoint attachments for simple paths

This module records the low-level operation of attaching one edge at each
end of a simple path while preserving simplicity.
-/

open SimpleGraph

namespace DeanK5

universe u

variable {V : Type u}

/--
Attach one edge at each end of an outside path.  The non-membership
hypotheses explicitly rule out reuse of either interface endpoint.
-/
def SimplePath.attachEndpoints
    {G : SimpleGraph V} {x x' y' y : V}
    (P : SimplePath G x' y')
    (hxx' : G.Adj x x') (hy'y : G.Adj y' y)
    (hxy : x ≠ y)
    (hx : x ∉ P.walk.support) (hy : y ∉ P.walk.support) :
    SimplePath G x y where
  walk := (P.walk.cons hxx').concat hy'y
  isPath := (P.isPath.cons hx).concat (by
    simp [hxy.symm, hy]) hy'y

@[simp] theorem SimplePath.attachEndpoints_length
    {G : SimpleGraph V} {x x' y' y : V}
    (P : SimplePath G x' y')
    (hxx' : G.Adj x x') (hy'y : G.Adj y' y)
    (hxy : x ≠ y)
    (hx : x ∉ P.walk.support) (hy : y ∉ P.walk.support) :
    (P.attachEndpoints hxx' hy'y hxy hx hy).length = P.length + 2 := by
  simp [SimplePath.attachEndpoints, SimplePath.length]

end DeanK5
