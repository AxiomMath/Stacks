module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesPerfection
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing

/-!
# The direct image of a module flat over the base along a proper morphism

Let `f : X ⟶ S` be a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation, flat over `S`. Clause (2) of [Stacks, Tag 0B91] says that `Rf_*ℱ` is a
perfect object of `D(𝒪_S)` whose formation commutes with arbitrary base change. This file proves
both halves, for `Rf_*ℱ` itself — `ℱ` placed in degree zero and pushed forward — rather than for
the tensor form `Rf_*(𝒪_X ⊗^L ℱ)` that the source's reduction to [Stacks, Tag 0A1H] produces.

## Main results

* `AlgebraicGeometry.ProperFlatDirectImage.isPerfect_derivedPushforwardModule`: `Rf_*ℱ` is
  perfect.
* `AlgebraicGeometry.ProperFlatDirectImage.nonempty_derivedPullback_derivedPushforwardModule_iso`:
  for every cartesian square with `g : S' ⟶ S` arbitrary, `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`.

## Implementation notes

*Perfectness* is [Stacks, Tag 0A1H] (`AlgebraicGeometry.isPerfect_derivedPushforward_tensor`) at
`E = 𝒪_X[0]`, which is perfect, and `𝒢^• = ℱ[0]`, which satisfies the hypothesis
`AlgebraicGeometry.FlatProperSupportFinitelyPresented` of that tag by
`AlgebraicGeometry.ProperFlatBaseChange.flatProperSupportFinitelyPresented_singleDegreeComplex`;
the left unit constraint of [Stacks, Tag 0FPT], `Stacks.RingedSpace.derivedTensorLeftUnitIso`,
identifies `Rf_*(𝒪_X[0] ⊗^L ℱ[0])` with `Rf_*ℱ`. Perfectness is a property of an isomorphism
class, so no compatibility of that constraint with anything is needed.

*Base change* is `isIso_derivedBaseChangeComp_single_of_isFlatOver` (in the namespace
`Stacks.AlgebraicGeometry.VanishingHigherDirectImages`), which already cancels the tensor factor:
the composite `Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ ⟶ Rf'_*(g')^*ℱ`
of the base-change map of [Stacks, Tag 08HY] and the derived-to-ordinary comparison is invertible.
What is added here is the passage between the spellings: `ℱ[0]` as the localization of a
single-degree complex versus `DerivedCategory.singleFunctor`, degreewise pullback of a
single-degree complex versus the single-degree complex of the pullback, and the two spellings of
the pullback of modules (`AlgebraicGeometry.modulePullbackIsoSchemePullback`).

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic (derivedPushforwardModule)
open Stacks.AlgebraicGeometry.VanishingHigherDirectImages
  (isIso_derivedBaseChangeComp_single_of_isFlatOver)

universe u

namespace AlgebraicGeometry.ProperFlatDirectImage

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}}

/-- **[Stacks, Tag 0B91], clause (2), the perfectness half.** Let `f : X ⟶ S` be a proper
morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of finite presentation, flat over
`S`. Then `Rf_*ℱ` is a perfect object of `D(𝒪_S)`.

This is [Stacks, Tag 0A1H] at `E = 𝒪_X[0]` and `𝒢^• = ℱ[0]`, followed by the left unit
constraint of [Stacks, Tag 0FPT]. -/
public theorem isPerfect_derivedPushforwardModule (f : X ⟶ S) (hf : FinitePresentation f)
    (hproper : IsProper f) (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    RingedSpace.IsPerfect (X := S.toRingedSpace) (derivedPushforwardModule f F) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have hE : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :=
    isPerfect_singleFunctor_of_isFiniteLocallyFree.{u, u + 1} X _ (isFiniteLocallyFree_unit X)
  have hG : FlatProperSupportFinitelyPresented f (ProperFlatBaseChange.singleDegreeComplex F) :=
    ProperFlatBaseChange.flatProperSupportFinitelyPresented_singleDegreeComplex f F hfp hflat
  have hperfect := isPerfect_derivedPushforward_tensor f hf _ hE _ hG
  have etensor : (((derivedTensorProductFunctor X.sheaf).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))).obj
      (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F))) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj F :=
    Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace _ ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm
  exact isPerfect_of_iso_scheme ((derivedPushforward f.toLRSHom.toShHom).mapIso etensor)
    hperfect

/-- **[Stacks, Tag 0B91], clause (2), the base-change half.** Let `f : X ⟶ S` be a proper
morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of finite presentation, flat over
`S`. For every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `g` arbitrary, `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`, the pullback of `ℱ` on the right being the
ordinary one.

The isomorphism is the composite of the base-change map of [Stacks, Tag 08HY] with the
derived-to-ordinary comparison, invertible by `isIso_derivedBaseChangeComp_single_of_isFlatOver`
of `Stacks.AlgebraicGeometry.VanishingHigherDirectImages`;
properness is not used, only that `f` is quasi-compact and quasi-separated. -/
public theorem nonempty_derivedPullback_derivedPushforwardModule_iso (f : X ⟶ S)
    (hf : FinitePresentation f) (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S')
    (g' : X' ⟶ X) (hsq : IsPullback g' f' f g) :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj (derivedPushforwardModule f F) ≅
      derivedPushforwardModule f' ((Scheme.Modules.pullback g').obj F)) := by
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  have : F.IsFinitePresentation := hfp
  have h := isIso_derivedBaseChangeComp_single_of_isFlatOver f g f' g' hsq F hflat
  refine ⟨(derivedPullback g.toLRSHom.toShHom).mapIso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F)) ≪≫ @asIso _ _ _ _ _ h ≪≫
    (derivedPushforward f'.toLRSHom.toShHom).mapIso ?_⟩
  exact DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
        (StacksDraft.KFlat.modulePullback g'.toLRSHom.toShHom) 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X'.Modules 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor X'.Modules 0).mapIso
      ((modulePullbackIsoSchemePullback g').app F)

end AlgebraicGeometry.ProperFlatDirectImage

end
