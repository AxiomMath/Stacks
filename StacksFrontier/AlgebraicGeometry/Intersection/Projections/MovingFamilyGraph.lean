module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyParameter
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTwist

/-!
# The graph of the family of projective transformations over a line

A triple `(x, [g], y)` of a source point, a point of the line `ℓ` and a target point of `𝐏(V)`
lies on the graph of the family of projective transformations exactly when `y = r_g(x)`, that is
when the functional `f_y` cutting out `y` is proportional to `f_x ∘ g`. Proportionality of two
functionals is the vanishing of all their `2 × 2` minors,

`f_y(u) · f_x(g v) - f_y(v) · f_x(g u) = 0`,

and each such minor is a global section of `𝒪(1,1,1)` on `𝐏(V) ×_k (ℓ ×_k 𝐏(V))`: writing the
tautological endomorphism of the line in a basis `b` of the corank-two quotient as
`g = ∑ᵢ μ(bᵢ) · gᵢ` with `gᵢ = lineEnd (b.coord i)`, the minor is the signed sum of four tensors
of tautological sections. This file writes those sections down and takes their common zero locus,
a closed subset of the triple product.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.propSection`: the minor section attached to a basis
  of the corank-two quotient and a pair of vectors of `V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingGraph`: the common zero locus of all the minor
  sections.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_movingGraph`: the locus is closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_movingGraph_iff`: a point of the triple product
  lies on it exactly when no minor section is nonvanishing there.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineEnd_eq_sum`: the tautological endomorphism at a
  functional is the combination `∑ᵢ μ(bᵢ) · lineEnd (b.coord i)` of the endomorphisms attached to
  a dual basis, which is what makes the minor a sum of four tensors.

## Implementation notes

The minor sections are indexed by a basis of the corank-two quotient as well as by the two
vectors, because a tensor of tautological sections is attached to a *single* vector in each
factor and the entry `f_x(g v)` is bilinear in the line coordinate and in the source functional.
A basis is a choice; the locus does not depend on it, which is visible from the characterisation
of its closed points, and the Moving Lemma statement quantifies the family existentially, so no
canonical choice is needed.

The section is built as a `PresheafOfModules.sectionsMk` of a sum over the basis index, directly
as a compatible family, because — as in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus` — the type of global
sections of a presheaf of modules carries no additive structure of its own, only its evaluations
over an open do.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]

/-- **The tautological endomorphism in a basis.** For a finite basis `b` of the corank-two
quotient, the endomorphism attached to a functional `μ` is the combination
`∑ᵢ μ(bᵢ) · lineEnd (b.coord i)`. -/
public theorem lineEnd_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι k (lineSpace k V L))
    (μ : Module.Dual k (lineSpace k V L)) :
    lineEnd k V L μ = ∑ i, μ (b i) • lineEnd k V L (b.coord i) := by
  have hμ : μ = ∑ i, μ (b i) • b.coord i := by
    refine b.ext fun j => ?_
    rw [LinearMap.sum_apply, Finset.sum_eq_single j
      (fun i _ hij => by
        simp [Module.Basis.coord_apply, Ne.symm hij])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp [Module.Basis.coord_apply]
  conv_lhs => rw [hμ]
  exact (map_sum (lineEndₗ k V L) _ Finset.univ).trans
    (Finset.sum_congr rfl fun i _ => map_smul (lineEndₗ k V L) _ _)

variable [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- **The minor section attached to a basis of the corank-two quotient and two vectors of `V`.**
Its value at a triple of closed points cut out by `f_x`, `μ` and `f_y` is the `2 × 2` determinant
`f_y(u) · f_x(g v) - f_y(v) · f_x(g u)`, where `g` is the endomorphism `μ` names. -/
public def propSection {ι : Type*} [Fintype ι] (b : Module.Basis ι k (lineSpace k V L))
    (u v : V) : (boxModule k V L).sections :=
  (boxModule k V L).val.sectionsMk
    (fun U => ∑ i : ι,
      ((boxSection k V L (lineEnd k V L (b.coord i) v) (b i) u).eval U -
        (boxSection k V L (lineEnd k V L (b.coord i) u) (b i) v).eval U))
    (by
      intro U W f
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, PresheafOfModules.sections_property, PresheafOfModules.sections_property]
      rfl)

omit [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The minor section evaluates over an open to the signed sum of the evaluations of the four
tensors of tautological sections. -/
public theorem propSection_eval {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (u v : V)
    (U : (Opens ↥(movingProd k V L))ᵒᵖ) :
    (propSection k V L b u v).eval U =
      ∑ i : ι,
        ((boxSection k V L (lineEnd k V L (b.coord i) v) (b i) u).eval U -
          (boxSection k V L (lineEnd k V L (b.coord i) u) (b i) v).eval U) :=
  rfl

/-- **The graph of the family of projective transformations over the line**: the set of points of
`𝐏(V) ×_k (ℓ ×_k 𝐏(V))` at which every minor section vanishes, that is at which the functional
cutting out the target point is proportional to the functional `f_x ∘ g` cutting out the
translate of the source point. -/
public def movingGraph {ι : Type*} [Fintype ι] (b : Module.Basis ι k (lineSpace k V L)) :
    Set (movingProd k V L) :=
  ⋂ p : V × V, (Stacks.SheafOfModules.nonvanishingLocus
    (X := (movingProd k V L).toRingedSpace) (boxModule k V L)
    (propSection k V L b p.1 p.2))ᶜ

omit [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- A point of the triple product lies on the graph exactly when no minor section is nonvanishing
at it. -/
public theorem mem_movingGraph_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (t : movingProd k V L) :
    t ∈ movingGraph k V L b ↔
      ∀ u v : V, t ∉ Stacks.SheafOfModules.nonvanishingLocus
        (X := (movingProd k V L).toRingedSpace) (boxModule k V L)
        (propSection k V L b u v) := by
  rw [movingGraph, Set.mem_iInter]
  exact ⟨fun h u v => h (u, v), fun h p => h p.1 p.2⟩

omit [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The graph is closed**: it is an intersection of complements of nonvanishing loci, which are
open because `𝒪(1,1,1)` is invertible. -/
public theorem isClosed_movingGraph {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) :
    IsClosed (movingGraph k V L b) := by
  have hinv := isInvertible_boxModule k V L
  refine isClosed_iInter fun p => ?_
  refine IsOpen.isClosed_compl ?_
  exact (Stacks.SheafOfModules.nonvanishingOpen (X := (movingProd k V L).toRingedSpace)
    (boxModule k V L) (propSection k V L b p.1 p.2)).2

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
