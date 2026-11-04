module

public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The reduced closed subspace, unconditionally

`AlgebraicGeometry.Space.reducedClosedSubspace` is the reduced closed subspace of an algebraic
space on a closed set of points. That its inclusion is a closed immersion rests on effective
descent along the surjective étale morphisms of the site — Stacks 02W8 in the form Stacks 03I2
consumes — and is available both with that descent taken as a hypothesis
(`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent`,
`AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace_of_immersionDescent`) and with the
hypothesis discharged.

This file records the hypothesis-free statements and their components.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace'`: the reduced closed
  subspace is a closed subspace, with no hypothesis, and its closed-immersion component
  `AlgebraicGeometry.Space.isClosedImmersion_ι_reducedClosedSubspace`.
* `AlgebraicGeometry.Space.existsUnique_reducedClosedSubspace'` is Stacks 03IQ: a closed
  subset of the points of an algebraic space carries a unique reduced closed subspace
  structure.

## Implementation notes

Each result is its unprimed namesake, which is already unconditional; the `_of_immersionDescent`
and `_of_closedImmersionDescent` forms there keep the descent hypothesis and remain available
for a client that wants to see where it is used.

The algebraicity component is needed on its own, because `AlgebraicGeometry.Space.IsProper` and
the other morphism predicates of Stacks 03HI and 03ZM carry algebraicity of their source in
their signatures, so a client stating properness of the reduced closed subspace over a base
needs it separately. It is not stated here: it needs no descent at all, and is
`AlgebraicGeometry.Space.isAlgebraicSpace_reducedClosedSubspace` of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/ReducedClosedSubspace.lean`, which this module
imports and re-exports.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The reduced closed subspace of an algebraic space on a closed set of points is a closed
subspace**, with no hypothesis: this is
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace`, whose descent hypothesis is
discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
theorem isClosedSubspace_reducedClosedSubspace' (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : _root_.IsClosed T) :
    IsClosedSubspace B S hS (reducedClosedSubspace B S hS X hX T hT) :=
  isClosedSubspace_reducedClosedSubspace B S hS X hX T hT

/-- The inclusion of the reduced closed subspace on a closed set of points is a closed
immersion, with no hypothesis. -/
theorem isClosedImmersion_ι_reducedClosedSubspace (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : _root_.IsClosed T) :
    IsClosedImmersion B S hS (reducedClosedSubspace B S hS X hX T hT).ι :=
  (isClosedSubspace_reducedClosedSubspace' B S hS hX T hT).2

/-- **Stacks 03IQ.** A closed subset of the set of points of an algebraic space over `S`
carries a unique reduced closed subspace structure: there is exactly one subfunctor of `X`
which is a closed subspace, has that closed set as its set of points, and is étale-locally
reduced.

The witness is `AlgebraicGeometry.Space.reducedClosedSubspace`, which is constructed explicitly. -/
@[stacks 03IQ]
theorem existsUnique_reducedClosedSubspace' (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : _root_.IsClosed T) :
    ∃! Z : Subfunctor X,
      IsClosedSubspace B S hS Z ∧
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T ∧
          HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
  existsUnique_reducedClosedSubspace B S hS X hX T hT

end AlgebraicGeometry.Space

end
