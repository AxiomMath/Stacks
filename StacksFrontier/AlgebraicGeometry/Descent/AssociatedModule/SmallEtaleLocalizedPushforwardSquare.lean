module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageQuasiCompactBase
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfModuleOverObjectEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectivesEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.MorphismLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image along `ε_a` commutes with restriction to a slice, and its derived form

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let `V` be an object of the
small étale site of `Y`.  With `a⁻¹V = (smallEtaleBaseChange B a).obj V` and `P_V` the direct
image along the localized morphism of [Stacks, Tag 04J0] (1), the base-change square

`(ε_a)_* ⋙ (−)|_{Y_étale/V} = (−)|_{X_étale/a⁻¹V} ⋙ P_V`

holds as an equality of functors, and its derived form is the isomorphism

`(R ⁿ (ε_a)_*(𝓕))|_{Y_étale/V} ≅ R ⁿ P_V (𝓕|_{X_étale/a⁻¹V})`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.localizedStructureMapBaseChange`: the structure map of the
  morphism of ringed sites localized at `V`, [Stacks, Tag 04J0] (1) at the small étale sites.
* `AlgebraicGeometry.SmallEtale.localizedPushforwardBaseChange`: `P_V`, the direct image along
  that localized morphism.
* `AlgebraicGeometry.SmallEtale.pushforwardOverFunctorSquareIso`: the square as an isomorphism of
  functors.
* `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardOverFunctorObjIso`: the derived square
  `(R ⁿ (ε_a)_*(𝓕))|_{Y_étale/V} ≅ R ⁿ P_V (𝓕|_{X_étale/a⁻¹V})`.

## Main results

* `AlgebraicGeometry.SmallEtale.overFunctor_comp_localizedPushforwardBaseChange`: the underived
  square, as an equality of functors.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

section Injectives

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Modules on a slice of the small étale site form a Grothendieck abelian category at module
universe `u`.** -/
public instance isGrothendieckAbelian_over_structureSheaf (W : SmallEtale B S hS) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} ((structureSheaf B S hS).over W)) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- **Modules on a slice of the small étale site have enough injectives**;  [Stacks, Tag 079H]. -/
public instance enoughInjectives_over_structureSheaf (W : SmallEtale B S hS) :
    EnoughInjectives (SheafOfModules.{u} ((structureSheaf B S hS).over W)) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

/-- **Modules on a slice of the small étale site have injective resolutions.** -/
public instance hasInjectiveResolutions_over_structureSheaf (W : SmallEtale B S hS) :
    HasInjectiveResolutions (SheafOfModules.{u} ((structureSheaf B S hS).over W)) :=
  inferInstance

end Injectives

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)
  (V : SmallEtale B Y.obj Y.property)

/-- **The structure map of the morphism of small étale ringed sites localized at `V`**,
[Stacks, Tag 04J0] part (1):
`AlgebraicGeometry.RingedSite.MorphismLocalization.localizedStructureMap` at
`u = smallEtaleBaseChange B a` and the structure map
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` of `ε_a`. -/
public abbrev localizedStructureMapBaseChange :
    (structureSheaf B Y.obj Y.property).over V ⟶
      ((Over.post (X := V) (smallEtaleBaseChange B a)).sheafPushforwardContinuous RingCat.{u}
        ((topology B Y.obj Y.property).over V)
        ((topology B X.obj X.property).over ((smallEtaleBaseChange B a).obj V))).obj
          ((structureSheaf B X.obj X.property).over ((smallEtaleBaseChange B a).obj V)) :=
  RingedSite.MorphismLocalization.localizedStructureMap (smallEtaleBaseChange B a)
    (topology B X.obj X.property) (topology B Y.obj Y.property) V
    (structureSheaf B X.obj X.property) (structureSheaf B Y.obj Y.property)
    (smallEtaleStructureMapRing B a)

/-- **`P_V`:  the direct image of modules along the morphism of small étale ringed sites localized
at `V`.**  It goes from modules on the slice of `X_étale` at `a⁻¹V` to modules on the slice of
`Y_étale` at `V`. -/
public abbrev localizedPushforwardBaseChange :
    SheafOfModules.{u}
        ((structureSheaf B X.obj X.property).over ((smallEtaleBaseChange B a).obj V)) ⥤
      SheafOfModules.{u} ((structureSheaf B Y.obj Y.property).over V) :=
  SheafOfModules.pushforward.{u} (localizedStructureMapBaseChange B a V)

/-- **The direct image along `ε_a` commutes with restriction to a slice**, as an equality of
functors:

`(−)|_{X_étale/a⁻¹V} ⋙ P_V = (ε_a)_* ⋙ (−)|_{Y_étale/V}`. -/
public theorem overFunctor_comp_localizedPushforwardBaseChange :
    SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
        ((smallEtaleBaseChange B a).obj V) ⋙ localizedPushforwardBaseChange B a V =
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B Y.obj Y.property) V :=
  RingedSite.MorphismLocalization.pushforward_overPullback_comm_modules
    (smallEtaleBaseChange B a) (topology B X.obj X.property) (topology B Y.obj Y.property) V
    (structureSheaf B X.obj X.property) (structureSheaf B Y.obj Y.property)
    (smallEtaleStructureMapRing B a)

/-- **The base-change square for the direct image along `ε_a` and restriction to the slice at
`V`**, as an isomorphism of functors:

`(ε_a)_* ⋙ (−)|_{Y_étale/V} ≅ (−)|_{X_étale/a⁻¹V} ⋙ P_V`,

the `CategoryTheory.eqToIso` of
`AlgebraicGeometry.SmallEtale.overFunctor_comp_localizedPushforwardBaseChange`. -/
public def pushforwardOverFunctorSquareIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B Y.obj Y.property) V ≅
      SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
          ((smallEtaleBaseChange B a).obj V) ⋙ localizedPushforwardBaseChange B a V :=
  eqToIso (overFunctor_comp_localizedPushforwardBaseChange B a V).symm

/-- **The derived base-change square:  the restriction to the slice at `V` of the `n`-th higher
direct image along `ε_a` is the `n`-th higher direct image along the localized morphism of the
restriction to the slice at `a⁻¹V`:**

`(R ⁿ (ε_a)_*(𝓕))|_{Y_étale/V} ≅ R ⁿ P_V (𝓕|_{X_étale/a⁻¹V})`. -/
@[sga "4 V 5.1" "Clause 3, special case"]
public def rightDerivedPushforwardOverFunctorObjIso
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (n : ℕ) :
    (SheafOfModules.overFunctor.{u} (structureSheaf B Y.obj Y.property) V).obj
        (((SheafOfModules.pushforward.{u}
          (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕) ≅
      ((localizedPushforwardBaseChange B a V).rightDerived n).obj
        ((SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
          ((smallEtaleBaseChange B a).obj V)).obj 𝓕) :=
  haveI : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (structureSheaf B Y.obj Y.property) V) :=
    (Stacks.Cohomology.Localization.OfEssentiallySmall.restriction_exact
      (topology B Y.obj Y.property) (structureSheaf B Y.obj Y.property) V).1
  haveI : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (structureSheaf B Y.obj Y.property) V) :=
    (Stacks.Cohomology.Localization.OfEssentiallySmall.restriction_exact
      (topology B Y.obj Y.property) (structureSheaf B Y.obj Y.property) V).2
  haveI : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
        ((smallEtaleBaseChange B a).obj V)) :=
    (Stacks.Cohomology.Localization.OfEssentiallySmall.restriction_exact
      (topology B X.obj X.property) (structureSheaf B X.obj X.property) _).1
  haveI : (SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
      ((smallEtaleBaseChange B a).obj V)).PreservesInjectiveObjects :=
    Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor_of_essentiallySmall
      (topology B X.obj X.property) (structureSheaf B X.obj X.property) _
  haveI hacyc : Stacks.RightDerivedComp.acyclic
      (SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
        ((smallEtaleBaseChange B a).obj V)) 𝓕 := fun q hq ↦
    Functor.isZero_rightDerived_of_exactFunctor _
      (Stacks.Cohomology.Localization.OfEssentiallySmall.restriction_exact
        (topology B X.obj X.property) (structureSheaf B X.obj X.property) _) 𝓕 q hq
  ((Functor.rightDerivedCompIso (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
      (SheafOfModules.overFunctor.{u} (structureSheaf B Y.obj Y.property) V) n).app 𝓕).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (pushforwardOverFunctorSquareIso B a V) n).app 𝓕 ≪≫
    Stacks.RightDerivedComp.objIso
      (SheafOfModules.overFunctor.{u} (structureSheaf B X.obj X.property)
        ((smallEtaleBaseChange B a).obj V))
      (injectiveResolution 𝓕) hacyc (localizedPushforwardBaseChange B a V) n

end AlgebraicGeometry.SmallEtale

end
