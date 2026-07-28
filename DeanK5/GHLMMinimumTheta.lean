import DeanK5.ThetaMinimumAttachment

/-!
# Internal proof of the GHLM minimum-theta structure lemma

This module assembles the three conclusions of GHLM Lemma 5.10 from the
internally proved minimum-theta results:

* a minimum-order theta in girth at least six is induced;
* each outside vertex with two theta neighbors extends it to an induced
  one-subdivision of `K₄`;
* the subdivision-attachment argument permits at most one such outside
  vertex when ten-cycles are excluded.
-/

open SimpleGraph

namespace DeanK5

universe u

namespace GHLM

/--
GHLM Lemma 5.10, proved internally with the same hypotheses and conclusions
as the former published-theorem dependency.
-/
theorem minimum_theta_structure_internal
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hgirth : GirthAtLeast G 6)
    (h10 : HasNoCycleLength G 10)
    (T : Theta G) (hmin : T.IsMinimumOrder) :
    T.IsInduced ∧
      Set.Subsingleton
        {v : V | v ∉ T.verts ∧
          2 ≤ (G.neighborSet v ∩
            (↑T.verts : Set V)).ncard} ∧
      ∀ v : V, v ∉ T.verts →
        2 ≤ (G.neighborSet v ∩
          (↑T.verts : Set V)).ncard →
        InducesOneSubdivisionK4 G (insert v T.verts) := by
  have hsubdivision :
      ∀ v : V, v ∉ T.verts →
        2 ≤ (G.neighborSet v ∩
          (↑T.verts : Set V)).ncard →
        InducesOneSubdivisionK4 G (insert v T.verts) := by
    intro v hv hdegree
    exact
      T.minimumOrder_attachment_induces_oneSubdivisionK4
        hgirth hmin v hv hdegree
  refine ⟨T.minimumOrder_isInduced hmin hgirth, ?_,
    hsubdivision⟩
  exact multiNeighborSet_subsingleton_of_induces
    G hgirth h10 T.verts hsubdivision

end GHLM

end DeanK5
