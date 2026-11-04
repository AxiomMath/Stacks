module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusUnion

/-!
# Schemes with a discrete underlying space

A scheme whose underlying topological space is discrete and compact is affine: the space is then
finite, each point is a one-point open subscheme and so an affine open, and finitely many
pairwise disjoint affine opens have affine union.  Serre vanishing therefore applies to such a
scheme, so over a base field its structure sheaf has no cohomology in positive degrees.

## Main results

* `AlgebraicGeometry.isAffine_of_discreteTopology`: **a scheme whose underlying space is
  discrete and compact is affine.**
* `AlgebraicGeometry.isZero_structureSheafCohomology_of_discreteTopology`: **the positive-degree
  cohomology of the structure sheaf of such a scheme over a field vanishes.**

## Implementation notes

The affineness is not proved here, because Mathlib proves it: `Mathlib/AlgebraicGeometry/Limits`
carries a low-priority instance giving `IsAffine X` for a scheme with `[Finite X]` and
`[DiscreteTopology X]`, deduced from `AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint` applied to
the one-point opens.  What that instance cannot do is fire on the hypotheses geometry supplies: a
scheme proper over a field arrives with `CompactSpace`, not with `Finite`, and
`finite_of_compact_of_discrete` is a theorem rather than an instance, so the passage from the one
to the other has to be made by hand.  `AlgebraicGeometry.isAffine_of_discreteTopology` is exactly
that passage and nothing besides; no reader should expect to find the content of the affineness
statement in this file.

Given affineness the vanishing is Serre vanishing in the spelling
`AlgebraicGeometry.structureSheafCohomology` that the genus is defined from, which is
`AlgebraicGeometry.isZero_structureSheafCohomology_of_isAffine`.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A scheme whose underlying space is discrete and compact is affine.**  A discrete compact
space is finite (`finite_of_compact_of_discrete`), and a scheme with a finite discrete space is
affine, being the union of the pairwise disjoint one-point affine opens cut out by its points.
Only the first of those two steps happens here: the second is Mathlib's low-priority instance for
`[Finite Z]` and `[DiscreteTopology Z]`, which instance search cannot reach from `CompactSpace`
on its own. -/
theorem isAffine_of_discreteTopology (Z : Scheme.{u}) [DiscreteTopology Z] [CompactSpace Z] :
    IsAffine Z :=
  have : Finite Z := finite_of_compact_of_discrete
  inferInstance

/-- **The positive-degree cohomology of the structure sheaf of a discrete compact scheme over a
field vanishes.**  Such a scheme is affine by `AlgebraicGeometry.isAffine_of_discreteTopology`, so
this is Serre vanishing, [Stacks, Tag 01XB], in the form
`AlgebraicGeometry.isZero_structureSheafCohomology_of_isAffine`. -/
theorem isZero_structureSheafCohomology_of_discreteTopology {k : Type u} [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [DiscreteTopology Z] [CompactSpace Z] (n : ℕ)
    (hn : 0 < n) : IsZero (structureSheafCohomology g n) :=
  have := isAffine_of_discreteTopology Z
  isZero_structureSheafCohomology_of_isAffine k g n hn

end AlgebraicGeometry

end
