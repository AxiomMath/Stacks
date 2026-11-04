module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackChartInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Étale base change for the higher direct images of modules

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale. Then the higher direct images of modules commute with restriction along `g`:
`R^n f'_*(F|_{X'}) = (R^n f_*F)|_{Y'}` in `Mod(𝒪_{Y'})`, naturally in the `𝒪_X`-module `F`.

## Main definitions

* `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives`:
  the isomorphism `R^n f'_*(F|_{X'}) ≅ (R^n f_*F)|_{Y'}`, given that restriction along `i`
  preserves injective objects.
* `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso`: the isomorphism
  `R^n f'_*(F|_{X'}) ≅ (R^n f_*F)|_{Y'}`.
* `AlgebraicGeometry.Space.smallBaseChangeChartMap`: the base change of a representable
  morphism to an étale scheme chart of the target, as a morphism of the chart spaces.
* `AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`: the same isomorphism at an
  étale scheme chart of the target of a representable morphism.

## Main results

* `AlgebraicGeometry.Space.hasInjectiveResolutions_modules`: the `𝒪_F`-modules on the small
  étale ringed site of an algebraic space have injective resolutions, at the universe of the
  structure rings.
* `AlgebraicGeometry.Space.isPullback_smallBaseChangeChart`: an étale scheme chart of the
  target of a representable morphism and its pullback chart form a cartesian square.

## Implementation notes

The degree runs over `ℕ`, in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`. The isomorphisms are not identified with the canonical
base-change comparison map.

The instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` are stated at module universe
`max u v r w`, and instance search at module universe `u` commits to them and then fails on the
universe constraint; the local priority raises of `SheafOfModules.instAbelian` and
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` send it through the applicable instances.

## References

* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 079H](https://stacks.math.columbia.edu/tag/079H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪_F`-modules on the small étale ringed site of an algebraic space have injective
resolutions, at the universe of the structure rings. -/
theorem hasInjectiveResolutions_modules (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hW : IsAlgebraicSpace B S hS W) :
    HasInjectiveResolutions (Modules.{u, u} B S hS W hW) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS W hW).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS W)
    infer_instance
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS W hW) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  infer_instance

variable {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- For a cartesian square of algebraic spaces whose bottom arrow `g` is étale, and given that
étale restriction of modules along `i` carries injective `𝒪_X`-modules to injective
`𝒪_{X'}`-modules (the hypothesis `h03F3`), the higher direct images of `𝒪_X`-modules commute
with étale restriction,

`R^n f'_*(F|_{X'}) = (R^n f_*F)|_{Y'}`

for every `n`, naturally in the `𝒪_X`-module `F`. -/
noncomputable def moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom)
    (h03F3 : (etaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).PreservesInjectiveObjects)
    (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    etaleModulePullback B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        (modulePushforward B S hS f').rightDerived n ≅
      (modulePushforward B S hS f).rightDerived n ⋙ etaleModulePullback B S hS g hg := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  have := etaleModulePullback_additive B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := etaleModulePullback_additive B S hS g hg
  have := preservesFiniteLimits_etaleModulePullback B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := preservesFiniteColimits_etaleModulePullback B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have := preservesFiniteColimits_etaleModulePullback B S hS g hg
  exact StacksTag03LR.rightDerivedBaseChangeIso _ _ _ _
    (modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg) n

/-- Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over `S` with `g` étale.  Then for every `n` the
`n`-th higher direct image of `𝒪_X`-modules commutes with restriction along the étale base
change,

`R^n f'_*(F|_{X'}) = (R^n f_*F)|_{Y'}`

in `Mod(𝒪_{Y'})`, naturally in the `𝒪_X`-module `F`. The morphism `f` is not assumed
representable, quasi-compact or quasi-separated, and `F` is not assumed quasi-coherent. -/
@[stacks 03LX "the higher direct images"]
noncomputable def moduleHigherPushforwardEtaleBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    etaleModulePullback B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        (modulePushforward B S hS f').rightDerived n ≅
      (modulePushforward B S hS f).rightDerived n ⋙ etaleModulePullback B S hS g hg :=
  moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives B S hS i f' f g sq hg
    (preservesInjectiveObjects_etaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)) n

section ChartBaseChange

variable {X Y : AlgebraicSpaces B S hS}

/-- The base change of a representable morphism `f : X ⟶ Y` of algebraic spaces to an étale
scheme chart `V` of `Y`: the morphism from the chart `V ×_Y X` of `X` to the chart `V`. -/
noncomputable def smallBaseChangeChartMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V) ⟶ chartSpace B S hS Y V :=
  ObjectProperty.homMk (yoneda.map (hf.snd V.1.hom))

/-- The chart `V ×_Y X` of `X`, the chart `V` of `Y` and `f` form a cartesian square of
algebraic spaces. -/
theorem isPullback_smallBaseChangeChart (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    IsPullback (chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))
      (smallBaseChangeChartMap B S hS f hf V) f (chartToSpace B S hS Y V) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hf.isPullback V.1.hom)

/-- For a representable morphism `f : X ⟶ Y` of algebraic
spaces and an étale scheme chart `V` of `Y`, the higher direct images of `𝒪_X`-modules commute
with restriction to the chart:

`R^n f'_*(F|_U) = (R^n f_*F)|_V`,

naturally in the `𝒪_X`-module `F`, where `U = V ×_Y X` is the pullback chart of `X` and
`f' : U ⟶ V` is the base change of `f`. The morphism `f` is not assumed quasi-compact or
quasi-separated, `V ⟶ Y` is not assumed surjective and `F` is not assumed quasi-coherent. -/
@[stacks 071Z]
noncomputable def moduleHigherPushforwardChartBaseChangeIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS
      (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).1
      (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).2
    etaleModulePullback B S hS
          (chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))
          (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V)) ⋙
        (modulePushforward B S hS (smallBaseChangeChartMap B S hS f hf V)).rightDerived n ≅
      (modulePushforward B S hS f).rightDerived n ⋙
        etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V) :=
  moduleHigherPushforwardEtaleBaseChangeIso B S hS _ _ f _
    (isPullback_smallBaseChangeChart B S hS f hf V)
    (isEtale_chartToSpace B S hS Y V) n

end ChartBaseChange

end AlgebraicGeometry.Space

end
