import DeanK5.Arithmetic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Graph-theoretic vocabulary for the conditional formalization

The paper uses paths and cycles in the strict graph-theoretic sense.
Accordingly, `SimplePath` stores Mathlib's `Walk.IsPath`, and `SimpleCycle`
stores `Walk.IsCycle`; neither can silently be a walk with repeated vertices.
-/

open Function
open scoped Sym2

namespace DeanK5

open SimpleGraph

universe u v

variable {V : Type u} {W : Type v}

/-- A path together with the proof that it repeats no vertex. -/
structure SimplePath (G : SimpleGraph V) (x y : V) where
  /-- The underlying walk from `x` to `y`. -/
  walk : G.Walk x y
  isPath : walk.IsPath

namespace SimplePath

variable {G : SimpleGraph V} {x y : V}

/-- The number of edges in a simple path. -/
def length (P : SimplePath G x y) : ℕ := P.walk.length

/-- The internal vertices, in their path order. -/
def internalSupport (P : SimplePath G x y) : List V :=
  P.walk.support.tail.dropLast

/-- The one-edge simple path determined by an adjacency. -/
def ofAdj (hxy : G.Adj x y) : SimplePath G x y where
  walk := .cons hxy .nil
  isPath := by
    simp [hxy.ne]

@[simp] theorem ofAdj_length (hxy : G.Adj x y) :
    (ofAdj hxy).length = 1 := by
  simp [ofAdj, length]

@[simp] theorem ofAdj_support (hxy : G.Adj x y) :
    (ofAdj hxy).walk.support = [x, y] := by
  simp [ofAdj]

/-- Reverse a simple path. -/
def reverse (P : SimplePath G x y) : SimplePath G y x :=
  ⟨P.walk.reverse, P.isPath.reverse⟩

@[simp] lemma reverse_length (P : SimplePath G x y) :
    P.reverse.length = P.length := by
  simp [reverse, length]

/-- The initial segment containing the first `n` edges of a simple path. -/
def take (P : SimplePath G x y) (n : ℕ) :
    SimplePath G x (P.walk.getVert n) :=
  ⟨P.walk.take n, P.isPath.take n⟩

/-- The terminal segment obtained after deleting the first `n` edges. -/
def drop (P : SimplePath G x y) (n : ℕ) :
    SimplePath G (P.walk.getVert n) y :=
  ⟨P.walk.drop n, P.isPath.drop n⟩

@[simp] theorem take_length (P : SimplePath G x y) (n : ℕ) :
    (P.take n).length = min n P.length := by
  simp [take, length]

@[simp] theorem drop_length (P : SimplePath G x y) (n : ℕ) :
    (P.drop n).length = P.length - n := by
  simp [drop, length]

theorem mem_support_of_mem_take
    (P : SimplePath G x y) (n : ℕ) {z : V}
    (hz : z ∈ (P.take n).walk.support) :
    z ∈ P.walk.support := by
  rw [take, SimpleGraph.Walk.support_take] at hz
  exact List.mem_of_mem_take hz

theorem mem_support_of_mem_drop
    (P : SimplePath G x y) (n : ℕ) {z : V}
    (hz : z ∈ (P.drop n).walk.support) :
    z ∈ P.walk.support := by
  rw [drop,
    SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
  exact List.mem_of_mem_drop hz

/-- A strict initial segment of a simple path omits the old endpoint. -/
theorem end_not_mem_take
    (P : SimplePath G x y) {n : ℕ}
    (hn : n < P.length) :
    y ∉ (P.take n).walk.support := by
  intro hy
  obtain ⟨k, hk, hkle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
  have hk_le_n : k ≤ n := by
    have hkmin : k ≤ min n P.length := by
      simpa [take, length] using hkle
    exact (le_min_iff.mp hkmin).1
  have hk_le_length : k ≤ P.walk.length := by
    simpa [length] using hk_le_n.trans hn.le
  have hk_end : P.walk.getVert k = y := by
    simpa [take, Nat.min_eq_right hk_le_n] using hk
  have : k = P.walk.length :=
    (P.isPath.getVert_eq_end_iff hk_le_length).1 hk_end
  change n < P.walk.length at hn
  omega

/-- Deleting a positive initial segment of a simple path omits the old start. -/
theorem start_not_mem_drop
    (P : SimplePath G x y) {n : ℕ}
    (hnpos : 0 < n) (hn : n ≤ P.length) :
    x ∉ (P.drop n).walk.support := by
  intro hx
  obtain ⟨k, hk, hkle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  have hsum_le : n + k ≤ P.walk.length := by
    simp only [drop, SimpleGraph.Walk.drop_length] at hkle
    simp only [length] at hn
    omega
  have hstart : P.walk.getVert (n + k) = x := by
    simpa [drop] using hk
  have : n + k = 0 :=
    (P.isPath.getVert_eq_start_iff hsum_le).1 hstart
  omega

/--
Append two simple paths when the second path, after its initial joining
vertex, avoids the entire first path.
-/
def appendDisjoint
    {z : V}
    (P : SimplePath G x y) (Q : SimplePath G y z)
    (hdisj : P.walk.support.Disjoint Q.walk.support.tail) :
    SimplePath G x z where
  walk := P.walk.append Q.walk
  isPath := by
    rw [SimpleGraph.Walk.isPath_def,
      SimpleGraph.Walk.support_append,
      List.nodup_append]
    refine ⟨P.isPath.support_nodup,
      Q.isPath.support_nodup.tail, ?_⟩
    intro a ha b hb hab
    exact (List.disjoint_left.mp hdisj ha)
      (hab ▸ hb)

@[simp] theorem appendDisjoint_length
    {z : V}
    (P : SimplePath G x y) (Q : SimplePath G y z)
    (hdisj) :
    (P.appendDisjoint Q hdisj).length =
      P.length + Q.length := by
  simp [appendDisjoint, length,
    SimpleGraph.Walk.length_append]

/--
Change only the indexed endpoint of a simple path along an equality.
Keeping this transport named prevents dependent endpoint casts from
obscuring the underlying walk in later support and length arguments.
-/
def castEnd {z : V} (P : SimplePath G x y) (h : y = z) :
    SimplePath G x z := by
  subst z
  exact P

/-- Change only the indexed starting point of a path along an equality. -/
def castStart {z : V} (P : SimplePath G x y) (h : x = z) :
    SimplePath G z y := by
  subst z
  exact P

@[simp] lemma castEnd_length {z : V}
    (P : SimplePath G x y) (h : y = z) :
    (P.castEnd h).length = P.length := by
  subst z
  rfl

@[simp] lemma castStart_length {z : V}
    (P : SimplePath G x y) (h : x = z) :
    (P.castStart h).length = P.length := by
  subst z
  rfl

@[simp] lemma castEnd_support {z : V}
    (P : SimplePath G x y) (h : y = z) :
    (P.castEnd h).walk.support = P.walk.support := by
  subst z
  rfl

@[simp] lemma castStart_support {z : V}
    (P : SimplePath G x y) (h : x = z) :
    (P.castStart h).walk.support = P.walk.support := by
  subst z
  rfl

/-- Map a simple path along an injective graph homomorphism. -/
def mapInjectiveHom
    {H : SimpleGraph W}
    (P : SimplePath G x y) (f : G →g H)
    (hinj : Function.Injective f) :
    SimplePath H (f x) (f y) :=
  ⟨P.walk.map f, P.isPath.map hinj⟩

@[simp] theorem mapInjectiveHom_length
    {H : SimpleGraph W}
    (P : SimplePath G x y) (f : G →g H)
    (hinj : Function.Injective f) :
    (P.mapInjectiveHom f hinj).length = P.length := by
  simp [mapInjectiveHom, length]

theorem mem_range_of_mem_mapInjectiveHom_support
    {H : SimpleGraph W}
    (P : SimplePath G x y) (f : G →g H)
    (hinj : Function.Injective f)
    {z : W}
    (hz : z ∈ (P.mapInjectiveHom f hinj).walk.support) :
    z ∈ Set.range f := by
  change z ∈ (P.walk.map f).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w, -, hw⟩ := List.mem_map.mp hz
  exact ⟨w, hw⟩

theorem start_not_mem_tail (P : SimplePath G x y) :
    x ∉ P.walk.support.tail := by
  have hnodup := P.isPath.support_nodup
  rw [← P.walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

/--
A vertex of a simple path other than its two indexed endpoints is an
internal vertex.
-/
theorem mem_internalSupport_of_mem_support
    (P : SimplePath G x y) {z : V}
    (hz : z ∈ P.walk.support)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    z ∈ P.internalSupport := by
  have hztail : z ∈ P.walk.support.tail :=
    (P.walk.mem_support_iff).1 hz |>.resolve_left hzx
  have htail : P.walk.support.tail ≠ [] :=
    List.ne_nil_of_mem hztail
  apply List.mem_dropLast_of_mem_of_ne_getLast hztail
  simpa [P.walk.cons_tail_support, htail] using hzy

end SimplePath

/-- A nonempty simple cycle, with a chosen base vertex. -/
structure SimpleCycle (G : SimpleGraph V) where
  /-- The chosen base vertex of the cyclic walk. -/
  base : V
  /-- The underlying closed walk based at `base`. -/
  walk : G.Walk base base
  isCycle : walk.IsCycle

namespace SimpleCycle

variable {G : SimpleGraph V}

/-- The number of edges in a simple cycle. -/
def length (C : SimpleCycle G) : ℕ := C.walk.length

lemma three_le_length (C : SimpleCycle G) : 3 ≤ C.length := by
  exact C.isCycle.three_le_length

/-- Map a certified simple cycle along an injective graph homomorphism. -/
def mapInjectiveHom
    {W : Type*} {H : SimpleGraph W}
    (C : SimpleCycle G) (f : G →g H)
    (hinj : Function.Injective f) :
    SimpleCycle H where
  base := f C.base
  walk := C.walk.map f
  isCycle := C.isCycle.map hinj

@[simp] theorem mapInjectiveHom_length
    {W : Type*} {H : SimpleGraph W}
    (C : SimpleCycle G) (f : G →g H)
    (hinj : Function.Injective f) :
    (C.mapInjectiveHom f hinj).length = C.length := by
  simp [mapInjectiveHom, length]

end SimpleCycle

/--
An admissible family of `q` rooted paths.  The equation on `length` records
the enumeration order; `start_ge_two` is the extra condition in the
published definition of admissible *paths*.
-/
structure AdmissiblePathFamily
    (G : SimpleGraph V) (x y : V) (q : ℕ) where
  /-- The length of the first path in the family. -/
  start : ℕ
  /-- The common difference between consecutive path lengths. -/
  step : ℕ
  admissible_step : IsAdmissibleStep step
  start_ge_two : 2 ≤ start
  /-- The indexed simple paths from `x` to `y`. -/
  path : Fin q → SimplePath G x y
  length_path : ∀ i, (path i).length = start + i.val * step

namespace AdmissiblePathFamily

/-- Transport an admissible family along an injective graph homomorphism. -/
def mapInjectiveHom
    {W : Type*} {H : SimpleGraph W}
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : AdmissiblePathFamily G x y q)
    (f : G →g H) (hinj : Function.Injective f) :
    AdmissiblePathFamily H (f x) (f y) q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := F.start_ge_two
  path i := (F.path i).mapInjectiveHom f hinj
  length_path i := by simp [F.length_path i]

/-- Reverse every path in an admissible family. -/
def reverse
    {G : SimpleGraph V} {x y : V} {q : ℕ}
    (F : AdmissiblePathFamily G x y q) :
    AdmissiblePathFamily G y x q where
  start := F.start
  step := F.step
  admissible_step := F.admissible_step
  start_ge_two := F.start_ge_two
  path i := (F.path i).reverse
  length_path i := by simp [F.length_path i]

end AdmissiblePathFamily

/-- An admissible family of `q` simple cycles. -/
structure AdmissibleCycleFamily (G : SimpleGraph V) (q : ℕ) where
  /-- The length of the first cycle in the family. -/
  start : ℕ
  /-- The common difference between consecutive cycle lengths. -/
  step : ℕ
  admissible_step : IsAdmissibleStep step
  /-- The indexed simple cycles. -/
  cycle : Fin q → SimpleCycle G
  length_cycle : ∀ i, (cycle i).length = start + i.val * step

/-- The graph contains a simple cycle of exactly the given length. -/
def HasCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ C : SimpleCycle G, C.length = n

/-- The graph contains a simple cycle whose length is divisible by `k`. -/
def HasCycleDivisibleBy (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ C : SimpleCycle G, C.length % k = 0

/-- The degree of a vertex in a graph on a finite carrier. -/
@[nolint unusedArguments]
noncomputable def finiteDegree [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborSet v).ncard

/-- A pointwise finite-degree lower bound, avoiding ambiguity about isolated carriers. -/
def MinDegreeAtLeast [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v, d ≤ finiteDegree G v

/--
Vertex `k`-connectivity, following the convention quoted in BGLP:
the graph has order at least `k+1`, and deletion of fewer than `k` vertices
leaves a connected graph.
-/
def IsKConnected [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  k + 1 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card < k →
      (G.induce {v | v ∉ S}).Connected

/-- Vertex 2-connectivity under the project's finite-graph convention. -/
abbrev IsTwoConnected [Fintype V]
    (G : SimpleGraph V) : Prop := IsKConnected G 2

/--
An exact rational lower bound on vertex connectivity.  This formulation
avoids rounding away BGLP's half-integral bound: `κ(G) ≥ q` means every
integer `n < q` is a valid connectivity level.
-/
def ConnectivityAtLeast [Fintype V]
    (G : SimpleGraph V) (q : ℚ) : Prop :=
  ∀ n : ℕ, (n : ℚ) < q → IsKConnected G (n + 1)

/-- Every simple cycle has length at least `g`. -/
def GirthAtLeast (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ C : SimpleCycle G, g ≤ C.length

/-- There is no simple cycle of the specified length. -/
def HasNoCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ C : SimpleCycle G, C.length ≠ n

/--
A theta graph represented by its three internally vertex-disjoint paths.
This is the path formulation of a subdivision of `K₄⁻` used by GHLM.
-/
structure Theta (G : SimpleGraph V) where
  /-- The first branch vertex shared by all three paths. -/
  x : V
  /-- The second branch vertex shared by all three paths. -/
  y : V
  roots_ne : x ≠ y
  /-- The three constituent simple paths from `x` to `y`. -/
  path : Fin 3 → SimplePath G x y
  paths_ne : ∀ i j, i ≠ j → (path i).walk ≠ (path j).walk
  internal_disjoint : ∀ i j, i ≠ j →
    (path i).internalSupport.Disjoint (path j).internalSupport

namespace Theta

variable {G : SimpleGraph V}

/--
Two distinct constituent paths of a theta can meet only at the two roots.
-/
theorem eq_root_of_mem_two_paths
    (T : Theta G) {i j : Fin 3} (hij : i ≠ j) {z : V}
    (hzi : z ∈ (T.path i).walk.support)
    (hzj : z ∈ (T.path j).walk.support) :
    z = T.x ∨ z = T.y := by
  by_contra hroots
  push Not at hroots
  have hzi' :
      z ∈ (T.path i).internalSupport :=
    (T.path i).mem_internalSupport_of_mem_support
      hzi hroots.1 hroots.2
  have hzj' :
      z ∈ (T.path j).internalSupport :=
    (T.path j).mem_internalSupport_of_mem_support
      hzj hroots.1 hroots.2
  exact (List.disjoint_left.mp
    (T.internal_disjoint i j hij) hzi') hzj'

/-- The vertices occurring on the three constituent paths. -/
def verts [DecidableEq V] (T : Theta G) : Finset V :=
  Finset.univ.biUnion fun i => (T.path i).walk.support.toFinset

/-- The edges occurring on the three constituent paths. -/
def edges [DecidableEq V] (T : Theta G) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i => (T.path i).walk.edges.toFinset

/-- No ambient edge between theta vertices is omitted by the theta. -/
def IsInduced [DecidableEq V] (T : Theta G) : Prop :=
  ∀ ⦃u v⦄, u ∈ T.verts → v ∈ T.verts → G.Adj u v → s(u, v) ∈ T.edges

/-- `T` has minimum order among all theta subgraphs of `G`. -/
def IsMinimumOrder [DecidableEq V] (T : Theta G) : Prop :=
  ∀ U : Theta G, T.verts.card ≤ U.verts.card

/-- A path uses only edges belonging to the theta. -/
def ContainsPath [DecidableEq V] (T : Theta G)
    {u v : V} (P : SimplePath G u v) : Prop :=
  ∀ e ∈ P.walk.edges, e ∈ T.edges

/-- Each defining path of a theta is, tautologically, contained in it. -/
theorem containsPath_path
    [DecidableEq V] (T : Theta G) (i : Fin 3) :
    T.ContainsPath (T.path i) := by
  intro e he
  simp only [Theta.edges, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, by simpa using he⟩

theorem ContainsPath.reverse
    [DecidableEq V] {T : Theta G}
    {a b : V} {P : SimplePath G a b}
    (hP : T.ContainsPath P) :
    T.ContainsPath P.reverse := by
  intro e he
  apply hP e
  simpa [SimplePath.reverse] using he

theorem ContainsPath.take
    [DecidableEq V] {T : Theta G}
    {a b : V} {P : SimplePath G a b}
    (hP : T.ContainsPath P) (n : ℕ) :
    T.ContainsPath (P.take n) := by
  intro e he
  apply hP e
  rw [SimplePath.take,
    SimpleGraph.Walk.edges_take] at he
  exact List.mem_of_mem_take he

theorem ContainsPath.drop
    [DecidableEq V] {T : Theta G}
    {a b : V} {P : SimplePath G a b}
    (hP : T.ContainsPath P) (n : ℕ) :
    T.ContainsPath (P.drop n) := by
  intro e he
  apply hP e
  rw [SimplePath.drop,
    SimpleGraph.Walk.edges_drop] at he
  exact List.mem_of_mem_drop he

theorem ContainsPath.appendDisjoint
    [DecidableEq V] {T : Theta G}
    {a b c : V}
    {P : SimplePath G a b} {Q : SimplePath G b c}
    (hP : T.ContainsPath P) (hQ : T.ContainsPath Q)
    (hdisj) :
    T.ContainsPath (P.appendDisjoint Q hdisj) := by
  intro e he
  simp only [SimplePath.appendDisjoint,
    SimpleGraph.Walk.edges_append,
    List.mem_append] at he
  exact he.elim (hP e) (hQ e)

end Theta

/-- The edges of `K₄`, used as the subdivision-vertex type. -/
abbrev K4Edge := (completeGraph (Fin 4)).edgeSet

/-- The canonical graph obtained by subdividing every edge of `K₄` exactly once. -/
def oneSubdivisionK4 : SimpleGraph (Fin 4 ⊕ K4Edge) where
  Adj a b :=
    match a, b with
    | Sum.inl v, Sum.inr e => v ∈ (e : Sym2 (Fin 4))
    | Sum.inr e, Sum.inl v => v ∈ (e : Sym2 (Fin 4))
    | _, _ => False
  symm := by
    constructor
    intro a b
    cases a <;> cases b <;> simp_all
  loopless := by
    constructor
    intro a
    cases a <;> simp

/-- The vertices in `S` induce exactly a one-subdivision of `K₄`. -/
def InducesOneSubdivisionK4
    (G : SimpleGraph V) (S : Finset V) : Prop :=
  Nonempty (G.induce (↑S : Set V) ≃g oneSubdivisionK4)

/--
One nontrivial end lobe of a connected graph.  `inner` is the part of the
end block away from its unique cut vertex.  The fields record precisely
the properties used in Section 7, without developing a global block-cut
tree API.
-/
structure EndLobe [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The vertices of the lobe away from its cut vertex. -/
  inner : Finset V
  /-- The unique cut vertex through which the lobe meets the rest of the graph. -/
  cut : V
  inner_nonempty : inner.Nonempty
  cut_not_inner : cut ∉ inner
  block_two_connected :
    IsTwoConnected
      (G.induce
        (↑(insert cut inner) : Set V))
  inner_connected :
    (G.induce (↑inner : Set V)).Connected
  closed :
    ∀ ⦃u v : V⦄, u ∈ inner → G.Adj u v →
      v ∈ inner ∨ v = cut

/--
The two end lobes and the middle connector supplied by the standard
block-cut-tree argument.  The avoidance fields are the exact data needed
to certify later path unions as simple cycles.
-/
structure EndLobePair [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The first selected end lobe. -/
  left : EndLobe G
  /-- The second selected end lobe. -/
  right : EndLobe G
  inner_disjoint : Disjoint left.inner right.inner
  left_cut_not_right_inner : left.cut ∉ right.inner
  right_cut_not_left_inner : right.cut ∉ left.inner
  /-- A simple path joining the two cut vertices outside both lobe interiors. -/
  connector : SimplePath G left.cut right.cut
  connector_avoids_left :
    ∀ v ∈ connector.walk.support,
      v ∉ left.inner
  connector_avoids_right :
    ∀ v ∈ connector.walk.support,
      v ∉ right.inner

/-- `G` is a complete graph of the specified order. -/
def IsCompleteGraphOfOrder (G : SimpleGraph V) (n : ℕ) : Prop :=
  Nonempty (G ≃g completeGraph (Fin n))

/-- `G` is a complete bipartite graph with the specified part sizes. -/
def IsCompleteBipartiteOfParts (G : SimpleGraph V) (s t : ℕ) : Prop :=
  Nonempty (G ≃g completeBipartiteGraph (Fin s) (Fin t))

/--
The low-level concatenation certificate used by paper Lemma 2.2.

The hypotheses state exactly what is needed to prevent a union of two paths
from being merely a closed walk.  The result is a Mathlib `IsCycle`.
-/
def cycleOfDisjointPaths
    {G : SimpleGraph V} {x y : V}
    (P : SimplePath G x y) (Q : SimplePath G y x)
    (hdisj : P.walk.support.tail.Disjoint Q.walk.support.tail)
    (hlong : 1 < P.length ∨ 1 < Q.length) :
    SimpleCycle G where
  base := x
  walk := P.walk.append Q.walk
  isCycle := P.isPath.isCycle_append Q.isPath hdisj hlong

@[simp] theorem cycleOfDisjointPaths_length
    {G : SimpleGraph V} {x y : V}
    (P : SimplePath G x y) (Q : SimplePath G y x)
    (hdisj) (hlong) :
    (cycleOfDisjointPaths P Q hdisj hlong).length = P.length + Q.length := by
  simp [cycleOfDisjointPaths, SimpleCycle.length, SimplePath.length,
    SimpleGraph.Walk.length_append]

/-- Map the canonical 5-cycle along an injective graph homomorphism. -/
def fiveCycleOfInjectiveHom
    {G : SimpleGraph V}
    (f : SimpleGraph.cycleGraph 5 →g G)
    (hinj : Function.Injective f) :
    SimpleCycle G where
  base := f 0
  walk := (SimpleGraph.cycleGraph.cycle 2).map f
  isCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective hinj).2
      SimpleGraph.cycleGraph.isCycle_cycle

@[simp] theorem fiveCycleOfInjectiveHom_length
    {G : SimpleGraph V}
    (f : SimpleGraph.cycleGraph 5 →g G)
    (hinj : Function.Injective f) :
    (fiveCycleOfInjectiveHom f hinj).length = 5 := by
  simp [fiveCycleOfInjectiveHom, SimpleCycle.length]

/-- An embedded 5-cycle supplies the required `0 mod 5` cycle witness. -/
theorem hasCycleDivisibleByFive_of_injective_cycleHom
    {G : SimpleGraph V}
    (f : SimpleGraph.cycleGraph 5 →g G)
    (hinj : Function.Injective f) :
    HasCycleDivisibleBy G 5 := by
  refine ⟨fiveCycleOfInjectiveHom f hinj, ?_⟩
  simp

/--
Five admissible simple cycles force a cycle of length `0 mod 5`.
-/
theorem AdmissibleCycleFamily.hasCycleDivisibleByFive
    {G : SimpleGraph V} (F : AdmissibleCycleFamily G 5) :
    HasCycleDivisibleBy G 5 := by
  obtain ⟨i, hi⟩ :=
    five_term_progression_hits_zero F.start F.step F.admissible_step
  refine ⟨F.cycle i, ?_⟩
  rw [F.length_cycle i]
  exact hi

/--
In a graph with no cycle divisible by five, a five-term admissible cycle
family is impossible.
-/
theorem no_five_admissible_cycles_of_no_divisible_cycle
    {G : SimpleGraph V} (h : ¬ HasCycleDivisibleBy G 5) :
    ¬ Nonempty (AdmissibleCycleFamily G 5) := by
  rintro ⟨F⟩
  exact h F.hasCycleDivisibleByFive

end DeanK5
