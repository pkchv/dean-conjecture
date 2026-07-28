import DeanK5.COYConcatenation
import DeanK5.COYInstance
import DeanK5.COYPathOperations

/-!
# The local contradiction in COY Claim 3.16

Claim 3.16 uses only a small part of the ordered block-chain geometry.
The selected block supplies a smaller rooted instance with parameter
`q - 1`; its `q - 1` paths are embedded in the ambient graph and followed
by one fixed path through the suffix of the chain.  Two paths through the
prefix of the chain then combine with those `q - 1` paths by COY Fact 1.

The structures below deliberately do not construct the block chain.  They
package exactly the consequences that its construction must provide:
the recursive block instance, the ambient embedding, the two prefix paths,
the fixed suffix path, and the two support-disjointness statements that
certify every concatenation as a simple path.
-/

namespace DeanK5

open SimpleGraph

universe u

variable {V W : Type u}

namespace COY

/--
The path-assembly data used in the contradiction of COY Claim 3.16.

`middle` is the recursive `q - 1` family in the selected block.  The
`embedding` realizes that block inside the ambient graph.  The two
disjointness fields are the formal versions of the facts that the suffix
meets the selected block only at its right cut vertex and that the prefix
meets each assembled outer path only at its left cut vertex.
-/
structure ClaimThreeSixteenAssembly
    [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {q : ℕ} (G : SimpleGraph V) (x y : V)
    (K : SimpleGraph W) (left right : W)
    (middle :
      AdmissiblePathFamily K left right (q - 1)) where
  /-- The recursive block graph embeds in the ambient graph. -/
  embedding : K ↪g G
  /-- The two admissible prefix paths from `x` to the left cut vertex. -/
  prefixFamily :
    AdmissiblePathFamily G x (embedding left) 2
  /-- The fixed connector from the right cut vertex to `y`. -/
  suffix :
    SimplePath G (embedding right) y
  /-- Every embedded middle path avoids the suffix after their common end. -/
  middle_disjoint_suffix :
    ∀ i,
      ((middle.path i).mapInjectiveHom
        embedding.toHom embedding.injective).walk.support.Disjoint
          suffix.walk.support.tail
  /--
  Every prefix path avoids every assembled outer path after the left cut
  vertex.  This is the precise simplicity premise needed by Fact 1.
  -/
  prefix_disjoint_outer :
    ∀ i j,
      (prefixFamily.path j).walk.support.Disjoint
        (((middle.path i).mapInjectiveHom
          embedding.toHom embedding.injective).appendDisjoint
            suffix (middle_disjoint_suffix i)).walk.support.tail
  /-- The original roots are distinct. -/
  roots_ne : x ≠ y
  /-- The first root is not the left cut vertex. -/
  root_ne_left : x ≠ embedding left
  /-- The second root is not the left cut vertex. -/
  otherRoot_ne_left : y ≠ embedding left
  /-- The recursive parameter is nonzero. -/
  pred_pos : 1 ≤ q - 1

namespace ClaimThreeSixteenAssembly

variable [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  {q : ℕ} {G : SimpleGraph V} {x y : V}
  {K : SimpleGraph W} {left right : W}
  {middle :
    AdmissiblePathFamily K left right (q - 1)}

/-- The recursive family mapped from the selected block to the ambient graph. -/
def mappedMiddle
    (A : ClaimThreeSixteenAssembly G x y K left right middle) :
    AdmissiblePathFamily G
      (A.embedding left) (A.embedding right) (q - 1) :=
  middle.mapInjectiveHom A.embedding.toHom A.embedding.injective

/-- Append the fixed suffix connector to every embedded recursive path. -/
def outerFamily
    (A : ClaimThreeSixteenAssembly G x y K left right middle) :
    AdmissiblePathFamily G (A.embedding left) y (q - 1) :=
  (A.mappedMiddle).appendFixed A.suffix (by
    intro i
    exact A.middle_disjoint_suffix i)

@[simp] theorem outerFamily_path
    (A : ClaimThreeSixteenAssembly G x y K left right middle)
    (i : Fin (q - 1)) :
    (A.outerFamily.path i) =
      ((middle.path i).mapInjectiveHom
        A.embedding.toHom A.embedding.injective).appendDisjoint
          A.suffix (A.middle_disjoint_suffix i) :=
  rfl

/--
Regard the assembled outer family as a family from the singleton interface
containing the left cut vertex.
-/
def outerSetFamily
    (A : ClaimThreeSixteenAssembly G x y K left right middle) :
    SemiAdmissibleSetPathFamily G
      ({A.embedding left} : Set V) y (q - 1) where
  start := A.outerFamily.start
  step := A.outerFamily.step
  admissible_step := A.outerFamily.admissible_step
  start_ge_one := (by
    have h := A.outerFamily.start_ge_two
    omega)
  endpoint _ := A.embedding left
  endpoint_mem _ := by simp
  path i := A.outerFamily.path i
  length_path i := A.outerFamily.length_path i
  unique_endpoint := by
    intro _ v _ hv
    simpa using hv

/-- The source-shaped Fact 1 certificate: `(q - 1) + 2 - 1 = q`. -/
def factOneCertificate
    (A : ClaimThreeSixteenAssembly G x y K left right middle) :
    FactOneCertificate G x y
      ({A.embedding left} : Set V) (q - 1) 2 where
  hs := A.pred_pos
  ht := by omega
  x_ne_y := A.roots_ne
  x_not_mem := by simpa using A.root_ne_left
  y_not_mem := by simpa using A.otherRoot_ne_left
  outer := A.outerSetFamily
  inner := fun _ =>
    SemiAdmissiblePathFamily.ofAdmissible A.prefixFamily
  equal_inner_length := by
    intro _ _
    rfl
  avoid_outer := by
    intro i j
    exact A.prefix_disjoint_outer i j

/--
The assembled Claim 3.16 data contradicts the defining absence of `q`
admissible `x`--`y` paths in a minimal counterexample.
-/
theorem false_of_assembly
    {z : V}
    (M : MinimalCounterexample q G x y z)
    (A : ClaimThreeSixteenAssembly G x y K left right middle) :
    False := by
  have hpaths := fact_one A.factOneCertificate
  have hcount : (q - 1) + 2 - 1 = q := by
    have := A.pred_pos
    omega
  apply M.no_paths
  unfold RootedInstance.Solvable
  simpa only [hcount] using hpaths

end ClaimThreeSixteenAssembly

/--
The recursive-call layer of Claim 3.16.

The ordered block-chain construction will instantiate this structure for
its selected block.  Minimality produces the middle family; `assemble`
records the geometric lifting and support separation for whichever family
minimality returns.
-/
structure ClaimThreeSixteenRecursiveStage
    [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {q : ℕ} (G : SimpleGraph V) (x y : V)
    (K : SimpleGraph W) (left right exception : W) where
  /-- The selected block is a rooted instance at parameter `q - 1`. -/
  recursiveInstance :
    RootedInstance (q - 1) K left right exception
  /-- The selected block is strictly smaller than the ambient graph. -/
  complexity_lt :
    rootedComplexity K < rootedComplexity G
  /-- Every recursive solution admits the Claim 3.16 path assembly. -/
  assemble :
    ∀ middle :
      AdmissiblePathFamily K left right (q - 1),
      ClaimThreeSixteenAssembly G x y K left right middle

namespace ClaimThreeSixteenRecursiveStage

variable [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]
  {q : ℕ} {G : SimpleGraph V} {x y z : V}
  {K : SimpleGraph W} {left right exception : W}

/--
Minimality solves the selected block instance, and the local Claim 3.16
assembly then gives the forbidden ambient family.
-/
theorem false_of_recursiveStage
    (M : MinimalCounterexample q G x y z)
    (S : ClaimThreeSixteenRecursiveStage
      (q := q) G x y K left right exception) :
    False := by
  obtain ⟨middle⟩ :=
    M.smaller_solvable S.recursiveInstance S.complexity_lt
  exact (S.assemble middle).false_of_assembly M

end ClaimThreeSixteenRecursiveStage

end COY

end DeanK5
