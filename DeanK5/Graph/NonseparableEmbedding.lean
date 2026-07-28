import DeanK5.Graph.Blocks

/-!
# Transporting nonseparable carriers through graph embeddings

A graph embedding identifies its domain with the graph induced on its range.
Consequently, the injective image of a nonseparable carrier is again a
nonseparable carrier.  This is useful when a block is first constructed in an
induced subgraph and then viewed in the ambient graph.
-/

open SimpleGraph

namespace DeanK5

universe u v

variable {V : Type u} {W : Type v}

namespace IsNonseparableCarrier

variable [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} {S : Finset V}

/--
The injective image of a nonseparable carrier under a graph embedding is
nonseparable in the target graph.
-/
theorem map_embedding
    (hS : IsNonseparableCarrier G S)
    (f : G ↪g H) :
    IsNonseparableCarrier H (S.image f) := by
  classical
  refine {
    card_ge_two := ?_
    connected := ?_
    delete_connected := ?_
  }
  · rw [Finset.card_image_of_injective S f.injective]
    exact hS.card_ge_two
  · let fS : G.induce (↑S : Set V) ↪g H :=
      f.comp (Embedding.induce (↑S : Set V))
    have hRange :
        Set.range fS = (↑(S.image f) : Set W) := by
      ext w
      constructor
      · rintro ⟨a, rfl⟩
        exact Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩
      · intro hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [← hRange]
    exact (fS.isoInduceRange.connected_iff).mp hS.connected
  · intro w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    let fErase : G.induce (↑(S.erase a) : Set V) ↪g H :=
      f.comp (Embedding.induce (↑(S.erase a) : Set V))
    have hRange :
        Set.range fErase =
          (↑((S.erase a).image f) : Set W) := by
      ext w
      constructor
      · rintro ⟨b, rfl⟩
        exact Finset.mem_image.mpr ⟨b.1, b.2, rfl⟩
      · intro hw
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨⟨b, hb⟩, rfl⟩
    rw [← Finset.image_erase f.injective, ← hRange]
    exact
      (fErase.isoInduceRange.connected_iff).mp
        (hS.delete_connected a ha)

end IsNonseparableCarrier

namespace GraphBlock

variable [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W}

/--
The image of a block carrier under a graph embedding is a nonseparable
carrier in the target graph.  Maximality is intentionally not asserted:
ambient vertices may extend the image to a larger block.
-/
theorem image_nonseparable
    (B : GraphBlock G)
    (f : G ↪g H) :
    IsNonseparableCarrier H (B.carrier.image f) :=
  B.nonseparable.map_embedding f

end GraphBlock

end DeanK5
