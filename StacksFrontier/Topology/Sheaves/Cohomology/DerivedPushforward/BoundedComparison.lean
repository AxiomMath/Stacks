module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction

/-!
# The derived direct image on `D⁺` is the restriction of the one on `D`

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The direct image of sheaves of
modules has two derived functors in play: the right derived functor
`Rf_*^+ : D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)` built from injective resolutions, and the unbounded
`Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` built from K-injective resolutions. This file identifies them on the
bounded below objects: the square

```
D⁺(𝒪_X) --Rf_*^+--> D⁺(𝒪_Y)
   |                   |
   ι                   ι
   v                   v
D(𝒪_X) ---Rf_*----> D(𝒪_Y)
```

commutes up to a canonical isomorphism, pinned by its compatibility with the two comparison
maps out of the degreewise direct image.

## Main definitions

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedUnitPlus` and
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedUnitBig`: the two comparison maps
  from the degreewise direct image of a bounded below complex into `D(𝒪_Y)`, through `Rf_*^+`
  and through `Rf_*`.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso`:
  **`Rf_*^+` followed by `D⁺(𝒪_Y) ⥤ D(𝒪_Y)` is `D⁺(𝒪_X) ⥤ D(𝒪_X)` followed by `Rf_*`.**

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso_fac` and
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso_hom_app`:
  **the isomorphism carries the comparison map through `Rf_*^+` to the one through `Rf_*`**.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isIso_boundedUnitPlus_app` and
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isIso_boundedUnitBig_app`: both comparison
  maps are invertible on the bounded below complexes of injective modules.

## References

* [Stacks Project, Tag 05T5](https://stacks.math.columbia.edu/tag/05T5)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u w₁ w₂

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w₁} (_root_.SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (_root_.SheafOfModules.{u} (structureSheafRing Y))]
  [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X))]

/-- Degreewise direct image of a bounded below complex of `𝒪_X`-modules, read in `D(𝒪_Y)`. -/
abbrev boundedPushforwardToDerivedCategory :
    HomotopyCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y)) :=
  HomotopyCategory.Plus.ι _ ⋙ pushforwardToDerivedCategory f

/-- The comparison `f_*K ⟶ Rf_*^+K` from the degreewise direct image of a bounded below complex
to the derived direct image computed on `D⁺`, read in `D(𝒪_Y)`. -/
def boundedUnitPlus :
    boundedPushforwardToDerivedCategory f ⟶
      DerivedCategory.Plus.Qh ⋙
        ((modulePushforward f).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
  Functor.whiskerRight (modulePushforward f).rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι

/-- The comparison `f_*K ⟶ Rf_*K` from the degreewise direct image of a bounded below complex
to the unbounded derived direct image. -/
def boundedUnitBig :
    boundedPushforwardToDerivedCategory f ⟶
      DerivedCategory.Plus.Qh ⋙ (DerivedCategory.Plus.ι ⋙ derivedPushforward f) :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι _) (derivedPushforwardUnit f)

/-- The component of `boundedUnitPlus f` at `K` is the image in `D(𝒪_Y)` of the component at `K`
of the unit of `Rf_*^+`. -/
@[simp]
theorem boundedUnitPlus_app
    (K : HomotopyCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    (boundedUnitPlus f).app K =
      DerivedCategory.Plus.ι.map
        ((modulePushforward f).rightDerivedFunctorPlusUnit.app K) :=
  rfl

omit [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X))] in
/-- The component of `boundedUnitBig f` at `K` is the component of the unit of `Rf_*` at the
underlying unbounded complex of `K`. -/
@[simp]
theorem boundedUnitBig_app
    (K : HomotopyCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    (boundedUnitBig f).app K =
      (derivedPushforwardUnit f).app ((HomotopyCategory.Plus.ι _).obj K) :=
  rfl

/-- The comparison through `Rf_*^+` is invertible on a bounded below complex of injective
modules. -/
instance isIso_boundedUnitPlus_app
    (Z : HomotopyCategory.Plus
      (InjectiveObject (_root_.SheafOfModules.{u} (structureSheafRing X)))) :
    IsIso ((boundedUnitPlus f).app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)) := by
  rw [boundedUnitPlus_app]
  have h : IsIso ((modulePushforward f).rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
        ((modulePushforward f).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
      (modulePushforward f).rightDerivedFunctorPlusUnit Z
  exact Functor.map_isIso DerivedCategory.Plus.ι _

/-- The comparison through the unbounded `Rf_*` is invertible on a bounded below complex of
injective modules. -/
instance isIso_boundedUnitBig_app
    (Z : HomotopyCategory.Plus
      (InjectiveObject (_root_.SheafOfModules.{u} (structureSheafRing X)))) :
    IsIso ((boundedUnitBig f).app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)) := by
  obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff
    ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z).obj.as).1
    ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z).2
  have := hn
  have hKI : CochainComplex.IsKInjective
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z).obj.as :=
    CochainComplex.isKInjective_of_injective _ n
  rw [boundedUnitBig_app]
  exact isIso_derivedPushforwardUnit_app_of_isKInjective f _ hKI

/-- `Rf_*^+` followed by `D⁺(𝒪_Y) ⥤ D(𝒪_Y)`, with the comparison `boundedUnitPlus f`, is a right
derived functor of the degreewise direct image on `K⁺(𝒪_X)`. -/
instance isRightDerivedFunctor_boundedUnitPlus :
    ((modulePushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι).IsRightDerivedFunctor (boundedUnitPlus f)
      (HomotopyCategory.Plus.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedPushforwardToDerivedCategory f)).isRightDerivedFunctor_of_isIso
    (boundedUnitPlus f) (fun _ => inferInstance)

/-- `D⁺(𝒪_X) ⥤ D(𝒪_X)` followed by `Rf_*`, with the comparison `boundedUnitBig f`, is a right
derived functor of the degreewise direct image on `K⁺(𝒪_X)`. -/
instance isRightDerivedFunctor_boundedUnitBig :
    (DerivedCategory.Plus.ι ⋙ derivedPushforward f).IsRightDerivedFunctor (boundedUnitBig f)
      (HomotopyCategory.Plus.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedPushforwardToDerivedCategory f)).isRightDerivedFunctor_of_isIso
    (boundedUnitBig f) (fun _ => inferInstance)

/-- **The derived direct image on `D⁺(𝒪_X)` is the restriction of the one on `D(𝒪_X)`**: an
isomorphism `Rf_*^+ ⋙ ι ≅ ι ⋙ Rf_*` of functors `D⁺(𝒪_X) ⥤ D(𝒪_Y)`. It is the uniqueness
isomorphism of the right derived functors of the degreewise direct image on `K⁺(𝒪_X)`. -/
def boundedDerivedPushforwardIso :
    (modulePushforward f).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ derivedPushforward f :=
  Functor.rightDerivedUnique _ _ (boundedUnitPlus f) (boundedUnitBig f)
    (HomotopyCategory.Plus.quasiIso _)

/-- The isomorphism `boundedDerivedPushforwardIso f` carries the comparison map
`f_*K ⟶ Rf_*^+K` to the comparison map `f_*K ⟶ Rf_*K`. -/
theorem boundedDerivedPushforwardIso_fac :
    boundedUnitPlus f ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (boundedDerivedPushforwardIso f).hom = boundedUnitBig f := by
  simp [boundedDerivedPushforwardIso]

/-- The componentwise form of `boundedDerivedPushforwardIso_fac`: at a bounded below complex `K` of
`𝒪_X`-modules the isomorphism takes the image in `D(𝒪_Y)` of the comparison `f_*K ⟶ Rf_*^+K` to
the comparison `f_*K ⟶ Rf_*K`. -/
theorem boundedDerivedPushforwardIso_hom_app
    (K : HomotopyCategory.Plus (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    DerivedCategory.Plus.ι.map
          ((modulePushforward f).rightDerivedFunctorPlusUnit.app K) ≫
        (boundedDerivedPushforwardIso f).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (derivedPushforwardUnit f).app ((HomotopyCategory.Plus.ι _).obj K) :=
  NatTrans.congr_app (boundedDerivedPushforwardIso_fac f) K

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
