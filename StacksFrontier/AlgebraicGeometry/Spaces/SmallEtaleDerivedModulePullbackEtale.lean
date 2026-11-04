module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree

/-!
# The derived pullback along an étale morphism of algebraic spaces is étale restriction

Let `a : X ⟶ Y` be an étale morphism of algebraic spaces.  Pullback of `𝒪_Y`-modules along `a`
is restriction of sections along small étale postcomposition with `a` (Stacks 03LV, Equation
03LW), an exact functor, so its total left derived functor is the functor it induces degreewise:
`La^* ≅ (a^*)_{D}`.  This identifies `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback a`
with `(AlgebraicGeometry.Space.etaleModulePullback a).mapDerivedCategory`, the form in which the
étale locality statements of `D_QCoh` (Stacks 08F2) are written, and transports the derived
adjunction to it.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale`: `La^* ≅ (a^*)_D` for `a`
  étale.
* `AlgebraicGeometry.Space.etaleDerivedModuleAdjunction`: the adjunction `(a^*)_D ⊣ Ra_*`.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- For `a` étale, the derived pullback `La^*` is isomorphic to the functor that the exact functor
`etaleModulePullback a` of étale restriction (Stacks 03LV) induces on derived categories. -/
def smallEtaleDerivedModulePullbackIsoEtale (a : X ⟶ Y) (ha : IsEtale B S hS a.hom) :
    smallEtaleDerivedModulePullback B S hS a ≅
      (etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory :=
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS a).toModulesHom
  let G : type_of% F := etaleModulePullback.{u, u} B S hS a ha
  haveI : G.Additive := etaleModulePullback_additive B S hS a ha
  haveI : PreservesFiniteLimits G := preservesFiniteLimits_etaleModulePullback B S hS a ha
  haveI : PreservesFiniteColimits G := preservesFiniteColimits_etaleModulePullback B S hS a ha
  Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso F G
    (smallEtaleDerivedModulePullback B S hS a)
    (smallEtaleDerivedModulePullbackComparison B S hS a)
    (pullbackModulesIsoModulePullback B S hS a ≪≫ modulePullbackIsoEtaleModulePullback B S hS a ha)

/-- For `a` étale, the functor `(a^*)_D` that étale restriction induces on derived categories is
left adjoint to `Ra_*`. -/
def etaleDerivedModuleAdjunction (a : X ⟶ Y) (ha : IsEtale B S hS a.hom) :
    (etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory ⊣
      derivedPushforward (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS a) :=
  (smallEtaleDerivedModuleAdjunction B S hS a).ofNatIsoLeft
    (smallEtaleDerivedModulePullbackIsoEtale B S hS a ha)

end AlgebraicGeometry.Space

end
