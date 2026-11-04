module

public import StacksFrontier.AlgebraicGeometry.ClauseThree.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.HigherRankIrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.NoetherianDevissage
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealPushforward

/-!
# The generic-stalk input of the dévissage on a Noetherian scheme

Let `X` be a Noetherian scheme. For every integral closed subscheme `i : W ⟶ X` with generic
point `ξ` and every coherent `𝒪_X`-module `ℱ` whose stalk at `i ξ` is annihilated by the
maximal ideal there, a finite coproduct of copies of one coherent sheaf of ideals on `W` maps
monomorphically into `ℱ`, and invertibly over a neighbourhood of `i ξ`.

## Main results

* `Stacks.AlgebraicGeometry.Tag01YQClauseThree.hasGenericStalkIdealCoproductSub`: the
  generic-stalk dévissage predicate holds on every Noetherian scheme.
* `Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective_of_h01YL`: a
  Noetherian scheme admitting a finite surjective morphism from an affine scheme is affine,
  granted the irreducible higher-rank criterion alone.
* `Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective`: a Noetherian
  scheme admitting a finite surjective morphism from an affine scheme is affine.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YL](https://stacks.math.columbia.edu/tag/01YL)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01YQClauseThree

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-- On a Noetherian scheme, a coherent module whose stalk at the image of the generic point of an
integral closed subscheme is annihilated by the maximal ideal there receives a monomorphism from a
finite coproduct of copies of a coherent sheaf of ideals, invertible near that point. -/
alias hasGenericStalkIdealCoproductSub :=
  Stacks.AlgebraicGeometry.NoetherianDevissage.hasGenericStalkIdealCoproductSub

/-- A Noetherian scheme admitting a finite surjective morphism from an affine scheme is affine,
granted the irreducible higher-rank criterion. -/
theorem isAffine_of_isFinite_surjective_of_h01YL {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X]
    (h01YL : Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X) :
    IsAffine X :=
  isAffine_of_isFinite_surjective_of_h01YE_h01YL f (hasGenericStalkIdealCoproductSub X) h01YL

/-- A Noetherian scheme admitting a finite surjective morphism from an affine scheme is affine. -/
@[stacks 01YQ]
theorem isAffine_of_isFinite_surjective {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X] :
    IsAffine X :=
  isAffine_of_isFinite_surjective_of_h01YL f
    (HigherRankIrreducibleDevissage.hasIrreducibleHigherRankCriterion X)

end Stacks.AlgebraicGeometry.Tag01YQClauseThree

end
