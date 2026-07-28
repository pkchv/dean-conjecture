import DeanK5.Contraction
import DeanK5.Graph.Separation

/-!
# The two-vertex `z`-end-block in COY Claim 3.9

COY Subsection 2.2 defines a `z`-end-block as an end block whose vertex
set is exactly `{z, b_z}`.  This is a bridge block, not one of the
nontrivial 2-connected end lobes represented elsewhere by `EndLobe`.

The certificate below therefore records `{z}` as a component region after
deleting `b_z`, together with the bridge edge `z b_z`.  Its degree field is
explicitly the degree of `b_z` in the exterior graph `D`, as in Claim 3.9.
The rest of this file derives only the elementary structural consequences
used there: the second neighbour `b'_z`, the exact neighbour pair at `b_z`,
the two-edge stem, and a fixed `b_z`--`y` path avoiding `z`.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {W : Type u}

namespace COY

/--
Source-faithful data for the two-vertex `z`-end-block used in COY
Claim 3.9.

The field `leaf_component` says that `{z}` is a component region of
`D - b_z`; together with `z_adj_bz`, this encodes the bridge block
`B_z` with vertex set `{z, b_z}`.  The equality in `bz_degree_two`
is degree inside `D`, not degree in any larger ambient graph.
-/
structure ZEndBlockCertificate
    [Fintype W] [DecidableEq W]
    (D : SimpleGraph W) (y z : W) where
  /-- The exterior graph containing the end block is connected. -/
  connected : D.Connected
  /-- The cut vertex `b_z` of the two-vertex end block. -/
  bz : W
  /-- Claim 3.9 assumes that the target vertex is not `z`. -/
  y_ne_z : y ≠ z
  /-- Claim 3.9 assumes that the target vertex is not `b_z`. -/
  y_ne_bz : y ≠ bz
  /-- The unique edge of the two-vertex block `B_z`. -/
  z_adj_bz : D.Adj z bz
  /--
  After deleting `b_z`, the singleton `{z}` is a component region.
  This is the component-side encoding of `V(B_z) = {z, b_z}`.
  -/
  leaf_component : ComponentRegion D {bz} {z}
  /-- The cut vertex has degree two in the exterior graph `D`. -/
  bz_degree_two : finiteDegree D bz = 2

namespace ZEndBlockCertificate

variable [Fintype W] [DecidableEq W]
  {D : SimpleGraph W} {y z : W}

/-- The cut vertex `b_z` is distinct from the leaf `z`. -/
theorem bz_ne_z (E : ZEndBlockCertificate D y z) :
    E.bz ≠ z :=
  E.z_adj_bz.ne.symm

/-- The leaf `z` is distinct from the cut vertex `b_z`. -/
theorem z_ne_bz (E : ZEndBlockCertificate D y z) :
    z ≠ E.bz :=
  E.z_adj_bz.ne

/--
Inside the exterior graph `D`, the only neighbour of `z` is the cut
vertex `b_z`.
-/
theorem adj_z_iff (E : ZEndBlockCertificate D y z) (v : W) :
    D.Adj z v ↔ v = E.bz := by
  constructor
  · intro hzv
    by_cases hv : v = E.bz
    · exact hv
    · have hvLeaf : v ∈ ({z} : Finset W) :=
        E.leaf_component.closed (by simp) hzv (by simpa)
      have hvz : v = z := by simpa using hvLeaf
      subst v
      exact False.elim (D.loopless.irrefl z hzv)
  · rintro rfl
    exact E.z_adj_bz

/-- The neighbour set of `z` in `D` is the singleton `{b_z}`. -/
theorem neighborSet_z_eq_singleton
    (E : ZEndBlockCertificate D y z) :
    D.neighborSet z = {E.bz} := by
  ext v
  simp [E.adj_z_iff]

/-- The leaf `z` has degree one in the exterior graph `D`. -/
theorem finiteDegree_z_eq_one
    (E : ZEndBlockCertificate D y z) :
    finiteDegree D z = 1 := by
  simp [finiteDegree, E.neighborSet_z_eq_singleton]

/--
There is a neighbour of `b_z` other than `z`; this is the source's
vertex `b'_z` when `d_D(b_z) = 2`.
-/
theorem exists_other_neighbor
    (E : ZEndBlockCertificate D y z) :
    ∃ w : W, D.Adj E.bz w ∧ w ≠ z := by
  have hzMem : z ∈ D.neighborSet E.bz :=
    E.z_adj_bz.symm
  have hcard : (D.neighborSet E.bz).ncard = 2 := by
    simpa [finiteDegree] using E.bz_degree_two
  obtain ⟨u, v, huv, hneighbors⟩ :=
    Set.ncard_eq_two.mp hcard
  have hzPair : z = u ∨ z = v := by
    simpa [hneighbors] using hzMem
  rcases hzPair with hzu | hzv
  · refine ⟨v, ?_, ?_⟩
    · have : v ∈ D.neighborSet E.bz := by
        rw [hneighbors]
        simp
      exact this
    · intro hvz
      exact huv (hzu.symm.trans hvz.symm)
  · refine ⟨u, ?_, ?_⟩
    · have : u ∈ D.neighborSet E.bz := by
        rw [hneighbors]
        simp
      exact this
    · intro huz
      exact huv (huz.trans hzv)

/--
The source's vertex `b'_z`: the unique neighbour of `b_z` in `D`
other than `z`.
-/
noncomputable def bPrime
    (E : ZEndBlockCertificate D y z) : W :=
  Classical.choose E.exists_other_neighbor

/-- The vertex `b'_z` is adjacent to `b_z` in `D`. -/
theorem bz_adj_bPrime
    (E : ZEndBlockCertificate D y z) :
    D.Adj E.bz E.bPrime :=
  (Classical.choose_spec E.exists_other_neighbor).1

/-- The vertex `b'_z` is distinct from `z`. -/
theorem bPrime_ne_z
    (E : ZEndBlockCertificate D y z) :
    E.bPrime ≠ z :=
  (Classical.choose_spec E.exists_other_neighbor).2

/-- The vertex `b'_z` is distinct from `b_z`. -/
theorem bPrime_ne_bz
    (E : ZEndBlockCertificate D y z) :
    E.bPrime ≠ E.bz :=
  E.bz_adj_bPrime.ne.symm

/-- The two neighbours of `b_z` in `D` are exactly `z` and `b'_z`. -/
theorem neighborSet_bz_eq_pair
    (E : ZEndBlockCertificate D y z) :
    D.neighborSet E.bz = {z, E.bPrime} := by
  have hsubset :
      ({z, E.bPrime} : Set W) ⊆ D.neighborSet E.bz := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact E.z_adj_bz.symm
    · exact E.bz_adj_bPrime
  have hpairCard : ({z, E.bPrime} : Set W).ncard = 2 :=
    Set.ncard_pair E.bPrime_ne_z.symm
  have hneighborCard : (D.neighborSet E.bz).ncard = 2 := by
    simpa [finiteDegree] using E.bz_degree_two
  exact
    (Set.eq_of_subset_of_ncard_le hsubset
      (by rw [hneighborCard, hpairCard])).symm

/-- Adjacency to `b_z` is equivalent to being `z` or `b'_z`. -/
theorem adj_bz_iff
    (E : ZEndBlockCertificate D y z) (v : W) :
    D.Adj E.bz v ↔ v = z ∨ v = E.bPrime := by
  change v ∈ D.neighborSet E.bz ↔ _
  rw [E.neighborSet_bz_eq_pair]
  simp

/--
The degree-two stem of the end block is the simple path
`z - b_z - b'_z`.
-/
noncomputable def stem
    (E : ZEndBlockCertificate D y z) :
    SimplePath D z E.bPrime where
  walk :=
    .cons E.z_adj_bz
      (.cons E.bz_adj_bPrime .nil)
  isPath := by
    simp [SimpleGraph.Walk.isPath_def, E.z_ne_bz,
      E.bPrime_ne_z.symm, E.bPrime_ne_bz.symm]

/-- The degree-two stem has exactly two edges. -/
@[simp] theorem stem_length
    (E : ZEndBlockCertificate D y z) :
    E.stem.length = 2 := by
  simp [stem, SimplePath.length]

/-- The degree-two stem has support exactly `[z, b_z, b'_z]`. -/
@[simp] theorem stem_support
    (E : ZEndBlockCertificate D y z) :
    E.stem.walk.support = [z, E.bz, E.bPrime] := by
  simp [stem]

/--
A surjective vertex map that sends each edge either to an equality or to
an edge preserves connectedness after contracted repetitions are removed.
-/
private theorem connected_of_surjective_mapOrContract
    {A B : Type*} [DecidableEq B]
    {H : SimpleGraph A} {K : SimpleGraph B}
    (hH : H.Connected)
    (f : A → B) (hsurj : Function.Surjective f)
    (hedge : ∀ ⦃u v⦄, H.Adj u v →
      f u = f v ∨ K.Adj (f u) (f v)) :
    K.Connected := by
  rw [connected_iff_exists_forall_reachable] at hH ⊢
  obtain ⟨r, hr⟩ := hH
  refine ⟨f r, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := hsurj w
  obtain ⟨p⟩ := hr v
  exact ⟨p.mapOrContract f hedge⟩

/-- The graph `D` induced on the vertices other than `z`. -/
abbrev withoutZ
    (_E : ZEndBlockCertificate D y z) :
    SimpleGraph {v : W // v ≠ z} :=
  D.induce {v | v ≠ z}

/-- The surviving copy of `b_z` in `D - z`. -/
def bzWithoutZ
    (E : ZEndBlockCertificate D y z) :
    {v : W // v ≠ z} :=
  ⟨E.bz, E.bz_ne_z⟩

/-- The surviving copy of `y` in `D - z`. -/
def yWithoutZ
    (E : ZEndBlockCertificate D y z) :
    {v : W // v ≠ z} :=
  ⟨y, E.y_ne_z⟩

/--
Deleting the leaf `z` leaves `D` connected.  The proof retracts `z`
onto its unique neighbour `b_z` and contracts that final leaf edge.
-/
theorem withoutZ_connected
    (E : ZEndBlockCertificate D y z) :
    E.withoutZ.Connected := by
  let f : W → {v : W // v ≠ z} := fun v =>
    if hv : v = z then E.bzWithoutZ else ⟨v, hv⟩
  apply connected_of_surjective_mapOrContract E.connected f
  · intro v
    refine ⟨v.1, ?_⟩
    simp [f, v.2]
  · intro u v huv
    by_cases huz : u = z
    · subst u
      have hvbz : v = E.bz :=
        (E.adj_z_iff v).mp huv
      subst v
      left
      simp [f, bzWithoutZ, E.bz_ne_z]
    · by_cases hvz : v = z
      · subst v
        have hubz : u = E.bz :=
          (E.adj_z_iff u).mp huv.symm
        subst u
        left
        simp [f, bzWithoutZ, E.bz_ne_z]
      · right
        simp only [f, dif_neg huz, dif_neg hvz]
        exact huv

/-- A fixed simple `b_z`--`y` path in the connected graph `D - z`. -/
noncomputable def pathWithoutZ
    (E : ZEndBlockCertificate D y z) :
    SimplePath E.withoutZ E.bzWithoutZ E.yWithoutZ :=
  let existence :=
    E.withoutZ_connected.exists_isPath E.bzWithoutZ E.yWithoutZ
  ⟨Classical.choose existence, Classical.choose_spec existence⟩

/--
The fixed `b_z`--`y` path, viewed in the original exterior graph `D`.
-/
noncomputable def pathToY
    (E : ZEndBlockCertificate D y z) :
    SimplePath D E.bz y :=
  E.pathWithoutZ.mapInjectiveHom
    (Embedding.induce {v : W | v ≠ z}).toHom
    Subtype.val_injective

/-- Every vertex on the fixed `b_z`--`y` path is different from `z`. -/
theorem pathToY_support_ne_z
    (E : ZEndBlockCertificate D y z)
    {v : W} (hv : v ∈ E.pathToY.walk.support) :
    v ≠ z := by
  change v ∈
    (E.pathWithoutZ.walk.map
      (Embedding.induce {v : W | v ≠ z}).toHom).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
  exact w.2

/-- The fixed `b_z`--`y` path avoids `z`. -/
theorem z_not_mem_pathToY_support
    (E : ZEndBlockCertificate D y z) :
    z ∉ E.pathToY.walk.support :=
  fun hz => E.pathToY_support_ne_z hz rfl

/--
The first vertex after `b_z` on the fixed path in `D - z` is `b'_z`.
-/
theorem pathWithoutZ_snd_eq_bPrime
    (E : ZEndBlockCertificate D y z) :
    E.pathWithoutZ.walk.snd.1 = E.bPrime := by
  have hstartEnd : E.bzWithoutZ ≠ E.yWithoutZ := by
    intro h
    exact E.y_ne_bz (congrArg Subtype.val h).symm
  have hnotNil :
      ¬E.pathWithoutZ.walk.Nil :=
    E.pathWithoutZ.walk.not_nil_of_ne hstartEnd
  have hadjInduced :
      E.withoutZ.Adj E.bzWithoutZ
        E.pathWithoutZ.walk.snd :=
    E.pathWithoutZ.walk.adj_snd hnotNil
  have hadj :
      D.Adj E.bz E.pathWithoutZ.walk.snd.1 := by
    exact hadjInduced
  rcases (E.adj_bz_iff _).mp hadj with hz | hprime
  · exact False.elim (E.pathWithoutZ.walk.snd.2 hz)
  · exact hprime

/-- The first vertex after `b_z` on the ambient fixed path is `b'_z`. -/
theorem pathToY_snd_eq_bPrime
    (E : ZEndBlockCertificate D y z) :
    E.pathToY.walk.snd = E.bPrime := by
  change
    (E.pathWithoutZ.walk.map
      (Embedding.induce {v : W | v ≠ z}).toHom).getVert 1 =
        E.bPrime
  rw [SimpleGraph.Walk.getVert_map]
  exact E.pathWithoutZ_snd_eq_bPrime

/--
The fixed tail `b'_z`--`y` obtained by deleting the first edge of the
fixed `b_z`--`y` path.
-/
noncomputable def bPrimeToY
    (E : ZEndBlockCertificate D y z) :
    SimplePath D E.bPrime y :=
  (E.pathToY.drop 1).castStart E.pathToY_snd_eq_bPrime

/-- Every vertex on the fixed `b'_z`--`y` tail is different from `z`. -/
theorem bPrimeToY_support_ne_z
    (E : ZEndBlockCertificate D y z)
    {v : W} (hv : v ∈ E.bPrimeToY.walk.support) :
    v ≠ z := by
  apply E.pathToY_support_ne_z
  apply E.pathToY.mem_support_of_mem_drop 1
  simpa [bPrimeToY, SimplePath.castStart_support] using hv

/-- The fixed `b'_z`--`y` tail avoids `z`. -/
theorem z_not_mem_bPrimeToY_support
    (E : ZEndBlockCertificate D y z) :
    z ∉ E.bPrimeToY.walk.support :=
  fun hz => E.bPrimeToY_support_ne_z hz rfl

end ZEndBlockCertificate

end COY

end DeanK5
