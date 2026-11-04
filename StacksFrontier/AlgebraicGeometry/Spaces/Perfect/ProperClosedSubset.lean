module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Closed subsets of an algebraic space proper over a base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of
finite type, and let `T` be a closed subset of the points of `X`. The subset `T` is *proper
over `Y`* when the reduced induced closed subspace of `X` supported on `T` is proper over
`Y`. This is the algebraic-space counterpart of `AlgebraicGeometry.IsProperOver`.

## Main definitions

* `AlgebraicGeometry.Space.IsProperOver`: properness over the base of a closed subset of the
  points of an algebraic space.

## Main results

There are no propositional results.

## Implementation notes

The reduced induced closed subspace is the datum
`AlgebraicGeometry.Space.reducedClosedSubspace`, a `CategoryTheory.Subfunctor` of `X`, so
`IsProperOver` is an abbreviation for properness of a composite of morphisms of presheaves
and the proper-morphism API of `AlgebraicGeometry.Space.IsProper` applies to it directly
without an unfolding lemma.

The hypotheses that `Y` is an algebraic space and that `f` is locally of finite type are
recorded in the binders, as in the source, even though the body does not use them:
`AlgebraicGeometry.Space.IsProper` is meaningful for an arbitrary morphism of presheaves, and
properness of the composite already forces the finite-type condition on the subspace. The
hypothesis that `X` is an algebraic space is genuinely used, since the reduced closed subspace
is only constructed for an algebraic space.

The topology on the point set is `AlgebraicGeometry.Space.pointTopology`, installed as a local
instance, so `T` is closed in the topology detected by scheme-valued points.

## References

* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **Stacks 0CZD.** A closed subset of the points of an algebraic space `X` is *proper over
`Y`* when the reduced induced closed subspace of `X` supported on it is proper over `Y`. -/
@[stacks 0CZD]
abbrev IsProperOver (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (_hf : IsLocallyOfFiniteType B S hS f) (T : Set (points B S hS X))
    (hT : IsClosed T) : Prop :=
  IsProper B S hS ((reducedClosedSubspace B S hS X hX T hT).ι ≫ f)

end AlgebraicGeometry.Space

end
