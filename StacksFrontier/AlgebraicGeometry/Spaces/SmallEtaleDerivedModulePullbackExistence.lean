module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankStratum
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# The derived pullback exists along every morphism of algebraic spaces

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B` and let
`f : X ⟶ Y` be a morphism. Degreewise pullback of `𝒪_Y`-modules followed by localization has an
everywhere-defined left derived functor, so the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is defined on the whole of `D(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy`: degreewise
  pullback of `𝒪_Y`-modules followed by localization has a left derived functor.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

variable {X Y : AlgebraicSpaces B S hS}

/-- Degreewise pullback of `𝒪_Y`-modules along a morphism `f : X ⟶ Y` of algebraic spaces,
followed by localization to `D(𝒪_X)`, has an everywhere-defined left derived functor. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy (f : X ⟶ Y) :
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (smallEtaleRingedToposHom B S hS f)

end

end AlgebraicGeometry.Space

end
