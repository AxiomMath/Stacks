module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction

/-!
# The reduction of Stacks 0720 to an affine base, with Stacks 03F3 part (1) supplied

`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_chartwise` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart` reduce the
quasi-coherence of `R^n f_*F`, for a morphism `f : X ⟶ Y` of algebraic spaces, to the base change
of `f` at the affine étale scheme charts of `Y`, given that the restriction of modules along each
étale inclusion `V ×_Y X ⟶ X` carries injective modules to injective modules. That is
[Stacks, Tag 03F3], part (1), for the modules on the small étale site, and
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback` proves it for every étale
morphism of algebraic spaces. This file states the two reductions with it supplied.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_chartwise'`: if every
  chartwise higher direct image `R^n f'_*(F|_U)` over an affine étale chart is quasi-coherent,
  so is `R^n f_*F`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart'`: the
  reduction to an affine base for a quasi-compact and quasi-separated `f`.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- Restriction of modules along the étale inclusion of each chart base change preserves
injective objects. -/
private theorem preservesInjectiveObjects_chartBaseChangeModulePullback (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    (chartBaseChangeModulePullback B S hS f V).PreservesInjectiveObjects :=
  preservesInjectiveObjects_etaleModulePullback B S hS
    (chartBaseChangeInclusion B S hS f V) (isEtale_chartBaseChangeInclusion B S hS f V)

/-- If for every affine étale scheme chart `V` of `Y` the degree-`n` higher direct image
`R^n f'_*(F|_U)` along the base change `f' : U = V ×_Y X ⟶ V` of `f` is quasi-coherent, then so
is `R^n f_*F`. -/
theorem isQuasicoherentOnSite_rightDerived_of_chartwise' (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (haffine : ChartwiseIsQuasicoherentHigherDirectImage B S hS f F n) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_of_chartwise B S hS f F n
    (preservesInjectiveObjects_chartBaseChangeModulePullback B S hS f)
    haffine

/-- **The reduction of Stacks 0720 to an affine base.** Let `f : X ⟶ Y` be a quasi-compact,
quasi-separated morphism of algebraic spaces over `S` and let `F` be a quasi-coherent
`𝒪_X`-module on the small étale site of `X`. Then `R^n f_*F` is quasi-coherent, granted
`haffine`: the same conclusion for the base change of `f` at every affine étale scheme chart of
`Y`. -/
theorem isQuasicoherentOnSite_rightDerived_of_forall_affine_chart' (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (n : ℕ)
    (haffine : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiCompactSpace B S hS (chartBaseChangeSpace B S hS f V).1 →
      have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
        (chartBaseChangeSpace B S hS f V).2
      (((modulePushforward B S hS (chartBaseChangeProjection B S hS f V)).rightDerived n).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F)).IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_of_forall_affine_chart B S hS f hfqc hfqs F n
    (preservesInjectiveObjects_chartBaseChangeModulePullback B S hS f)
    haffine

end AlgebraicGeometry.Space

end
