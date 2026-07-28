import DeanK5.COYBoundaryCompressionBlock

/-!
# Selected-neighbour degree bounds for boundary compression

For Claim 3.12 only a chosen subset of the ambient neighbours belongs to
the compression carrier.  Injectivity of the collapse map on that subset
is enough to retain all of them as distinct neighbours in the quotient.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace COY.BoundaryCompression

variable [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Q T A : Finset V} {t d : V}

/--
A finite set of neighbours that lies in the compression source and remains
distinct after collapsing injects into the compressed neighbour set.
-/
theorem selectedNeighbors_card_le_finiteDegree
    (hd : d ∈ Q)
    (hAadj : ∀ ⦃v : V⦄, v ∈ A → G.Adj d v)
    (hAmem : A ⊆ Q ∪ T)
    (hinj :
      Set.InjOn (collapse Q t) (↑A : Set V)) :
    A.card ≤
      finiteDegree (graph G Q T t) (inner ⟨d, hd⟩) := by
  let f := collapse Q t
  have himage :
      f '' (↑A : Set V) ⊆
        (graph G Q T t).neighborSet (inner ⟨d, hd⟩) := by
    rintro w ⟨v, hvA, rfl⟩
    have hvA' : v ∈ A := by simpa using hvA
    have hvN : G.Adj d v := hAadj hvA'
    have hvUnion : v ∈ Q ∪ T := hAmem hvA'
    have hdUnion : d ∈ Q ∪ T :=
      Finset.mem_union_left T hd
    have hcollapseD :
        collapse Q t d = inner ⟨d, hd⟩ :=
      collapse_of_mem_component Q t hd
    have hne :
        collapse Q t d ≠ collapse Q t v := by
      intro h
      have hdv :
          d = v :=
        ((collapse_eq_inner_iff Q t ⟨d, hd⟩ v).1
          (h.symm.trans hcollapseD)).symm
      exact hvN.ne hdv
    have hadj :=
      graph_adj_of_adj hdUnion hvUnion hvN hne
    simpa [hcollapseD] using hadj
  unfold finiteDegree
  calc
    A.card = (↑A : Set V).ncard := by simp
    _ = (f '' (↑A : Set V)).ncard :=
      (hinj.ncard_image).symm
    _ ≤
        ((graph G Q T t).neighborSet
          (inner ⟨d, hd⟩)).ncard :=
      Set.ncard_le_ncard himage

end COY.BoundaryCompression

end DeanK5
