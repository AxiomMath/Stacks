module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward

/-!
# The higher direct images along an exact direct image

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces along which the direct image
`f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` is exact. Then `Rf_*` is the functor `f_*` induces on derived
categories, and so the higher direct images of an object of `D(𝒪_X)` are the direct images of
its cohomology sheaves:

`H^n(Rf_*K) ≅ f_*(H^nK)`,

naturally in `K`. This file records that isomorphism, which is what lets a higher direct image
taken along a composite be unwound one exact factor at a time.

## Main definitions

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyFunctorIso`:
  **`Rf_* ⋙ H^n ≅ H^n ⋙ f_*` for `f_*` exact**, and
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyFunctorObjIso`
  its value at an object.

## Implementation notes

Both halves are already available generically: exactness of `f_*` makes the chosen derived
pushforward the functor `f_*` induces on derived categories
(`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory`, which despite its name has
no hypothesis beyond right exactness of `f_*`), and an exact additive functor commutes with the
homology of the derived category (`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`). The
content of this file is only that the two compose.

Left exactness of `f_*` is a hypothesis here even though it is automatic for a direct image,
which is a left exact functor as a right adjoint: the instance is phrased for
`CategoryTheory.SheafOfModules.pushforward` and instance search does not cross the definition of
`AlgebraicGeometry.RingedSpaceModuleAdjunction.modulePushforward`, so the consumer supplies it.
Every consumer in this library has it to hand.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [PreservesFiniteLimits (modulePushforward f)]
  [PreservesFiniteColimits (modulePushforward f)]

/-- **The higher direct images along an exact direct image are the direct images of the
cohomology sheaves**: for `f_*` exact, `H^n(Rf_*K) ≅ f_*(H^nK)` naturally in
`K : D(𝒪_X)`. -/
def derivedPushforwardHomologyFunctorIso (n : ℤ) :
    derivedPushforward f ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n ⋙
        modulePushforward f :=
  Functor.isoWhiskerRight (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory f) _ ≪≫
    (modulePushforward f).mapDerivedCategoryHomologyIso n

/-- `derivedPushforwardHomologyFunctorIso` at an object: `H^n(Rf_*K) ≅ f_*(H^nK)`. -/
def derivedPushforwardHomologyFunctorObjIso (n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n).obj
        ((derivedPushforward f).obj K) ≅
      (modulePushforward f).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n).obj K) :=
  (derivedPushforwardHomologyFunctorIso f n).app K

end

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
