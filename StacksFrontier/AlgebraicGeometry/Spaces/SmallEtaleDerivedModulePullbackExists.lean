module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# The derived pullback along a morphism of algebraic spaces exists

`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is the derived pullback
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` along a morphism `f : X ⟶ Y` of algebraic spaces, Tag 06YY for the
morphism of small étale ringed topoi of Stacks 03G8. Degreewise pullback of `𝒪_Y`-modules has
a left derived functor along the quasi-isomorphisms, for every morphism `f` of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy`: the
  derived pullback `Lf^*` along every morphism of algebraic spaces exists, as an instance.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Degreewise pullback of `𝒪_Y`-modules along a morphism `f : X ⟶ Y` of algebraic spaces,
followed by localization, has a left derived functor along the quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy (f : X ⟶ Y) :
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (smallEtaleRingedToposHom B S hS f)

end AlgebraicGeometry.Space

end
