module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Perfect

/-!
# Composition of perfect morphisms of algebraic spaces

A composite of perfect morphisms of algebraic spaces over `S` is perfect, given that
perfectness of morphisms of schemes is étale local on the source and target.

## Main results

* `AlgebraicGeometry.Space.isPerfect_comp`: the composite of two perfect morphisms of
  algebraic spaces is perfect, carrying étale locality of perfectness as a hypothesis.

## Implementation notes

Perfectness of a morphism of algebraic spaces is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to the
scheme-morphism property `AlgebraicGeometry.Perfect`, so the statement is the case of Stacks
0AML, `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_comp`, at that property. Its two
hypotheses are stability of perfectness under composition, which is Stacks 0689 in the form
`AlgebraicGeometry.Perfect.isStableUnderComposition`, and étale locality of perfectness on the
source and target, which is the hypothesis below. The composite is *not* chartwise reducible to
Stacks 0689 the way Stacks 06BU and 06C2 are: the two charts of the intermediate space produced
by the hypotheses on the factors need not agree, so the square carrying the composite is one
whose chart of the source is merely surjective, and upgrading that to every square is exactly
the content of étale locality.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0689](https://stacks.math.columbia.edu/tag/0689)
* [Stacks Project, Tag 0AML](https://stacks.math.columbia.edu/tag/0AML)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A composition of perfect morphisms of algebraic spaces over `S` is perfect, given that
perfectness of morphisms of schemes is étale local on the source and target.

This is the statement of Stacks 06C1 at the every-étale-chart definition of perfectness, as an
instance of Stacks 0AML. -/
-- Not tagged `@[stacks 06C1]`: Stacks 06C1 asserts the composition law outright, whereas this
-- theorem carries `hP`. The tag sits on the unconditional form,
-- `AlgebraicGeometry.Space.IsPerfect.comp`, which discharges `hP` with
-- `AlgebraicGeometry.perfect_isEtaleLocalOnSourceAndTarget`.
theorem isPerfect_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hP : IsEtaleLocalOnSourceAndTarget (@AlgebraicGeometry.Perfect.{u}))
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsPerfect B S hS f) (hg : IsPerfect B S hS g) :
    IsPerfect B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS _ hP hX hY hZ f g hf hg

end AlgebraicGeometry.Space

end
