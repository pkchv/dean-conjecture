import DeanK5.Graph.Separation

/-!
# Exact degree bookkeeping in a component region

For a vertex inside a component region of `G - S`, every ambient neighbour
lies either in the region or in the deleted separator.  These two classes are
disjoint, so the ambient degree is the induced degree plus the number of
separator neighbours.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V : Type u}

namespace ComponentRegion

variable [DecidableEq V]
  {G : SimpleGraph V} {S Q : Finset V}

/--
The ambient neighbours of a vertex in a component region split into its
neighbours inside the region and its neighbours in the separator.
-/
theorem neighborSet_eq_inside_union_separator
    (hQ : ComponentRegion G S Q)
    {v : V} (hv : v ∈ Q) :
    G.neighborSet v =
      (G.neighborSet v ∩ (↑Q : Set V)) ∪
        (G.neighborSet v ∩ (↑S : Set V)) := by
  ext w
  constructor
  · intro hvw
    by_cases hwS : w ∈ S
    · exact Or.inr ⟨hvw, hwS⟩
    · exact Or.inl ⟨hvw, hQ.closed hv hvw hwS⟩
  · rintro (⟨hvw, -⟩ | ⟨hvw, -⟩)
    · exact hvw
    · exact hvw

/--
Inside neighbours and separator neighbours of a component vertex are
disjoint.
-/
theorem insideNeighbors_disjoint_separatorNeighbors
    (hQ : ComponentRegion G S Q)
    {v : V} :
    Disjoint
      (G.neighborSet v ∩ (↑Q : Set V))
      (G.neighborSet v ∩ (↑S : Set V)) := by
  rw [Set.disjoint_left]
  intro w hwInside hwSeparator
  exact hQ.not_mem_separator hwInside.2 hwSeparator.2

omit [DecidableEq V] in
/--
Under the subtype embedding, the neighbour set in the graph induced on
`Q` is exactly the set of ambient neighbours that lie in `Q`.
-/
theorem image_induced_neighborSet
    {v : V} (hv : v ∈ Q) :
    Subtype.val ''
        ((G.induce (↑Q : Set V)).neighborSet
          (⟨v, hv⟩ : (↑Q : Set V))) =
      G.neighborSet v ∩ (↑Q : Set V) := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.2⟩
  · rintro ⟨hvw, hwQ⟩
    exact ⟨⟨w, hwQ⟩, hvw, rfl⟩

/--
Exact degree decomposition for a vertex of a component region: its degree
in `G` is its degree in the graph induced on `Q`, plus its number of
neighbours in the separator `S`.
-/
theorem finiteDegree_eq_induce_add_separatorNeighbors
    [Fintype V]
    (hQ : ComponentRegion G S Q)
    {v : V} (hv : v ∈ Q) :
    finiteDegree G v =
      finiteDegree (G.induce (↑Q : Set V))
          (⟨v, hv⟩ : (↑Q : Set V)) +
        (G.neighborSet v ∩ (↑S : Set V)).ncard := by
  let inside := G.neighborSet v ∩ (↑Q : Set V)
  let separator := G.neighborSet v ∩ (↑S : Set V)
  have hpartition :
      G.neighborSet v = inside ∪ separator := by
    simpa [inside, separator] using
      hQ.neighborSet_eq_inside_union_separator hv
  have hdisjoint : Disjoint inside separator := by
    simpa [inside, separator] using
      (hQ.insideNeighbors_disjoint_separatorNeighbors (v := v))
  have himage :
      Subtype.val ''
          ((G.induce (↑Q : Set V)).neighborSet
            (⟨v, hv⟩ : (↑Q : Set V))) =
        inside := by
    simpa [inside] using
      (image_induced_neighborSet (G := G) hv)
  unfold finiteDegree
  calc
    (G.neighborSet v).ncard =
        (inside ∪ separator).ncard :=
      congrArg Set.ncard hpartition
    _ = inside.ncard + separator.ncard :=
      Set.ncard_union_eq hdisjoint
    _ =
        ((G.induce (↑Q : Set V)).neighborSet
          (⟨v, hv⟩ : (↑Q : Set V))).ncard +
          separator.ncard := by
      rw [← himage,
        Set.ncard_image_of_injective _ Subtype.val_injective]

end ComponentRegion

end DeanK5
