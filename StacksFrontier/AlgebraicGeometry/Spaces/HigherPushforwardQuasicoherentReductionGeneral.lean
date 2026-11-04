module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction

/-!
# Quasi-coherence of the higher direct images: the reduction to an affine base, in general

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces. If for
every affine étale scheme chart `V` of `Y` the higher direct image `R^n f'_*(F|_U)` along the
base change `f' : U = V ×_Y X ⟶ V` is quasi-coherent, then so is `R^n f_*F`: the first step of
the proof of Stacks 0720, here for every `𝒪_X`-module `F` and with Stacks 03F3, part (1), for
`U ⟶ X` supplied by `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`.

## Main results

* `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_forall_affine_chart_general`:
  the degree-zero reduction in the binders of Stacks 03M9.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_chartwise_general` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart_general`: the
  reduction in arbitrary degree; the second is phrased in the binders of Stacks 0720.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
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

/-! ### The degree-zero reduction -/

/-- **The reduction of Stacks 03M9 to an affine base, in the pullback reading.** Let
`f : X ⟶ Y` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and let
`F` be an `𝒪_X`-module on the small étale site of `X`. If for every affine étale scheme chart
`V` of `Y` the direct image along the base change `U = V ×_Y X ⟶ V` of `F|_U` is quasi-coherent
whenever that base change is quasi-compact and quasi-separated with quasi-compact source, then
`f_*F` is quasi-coherent.

Those three properties of the base change are supplied here from those of `f` by Stacks 03HF,
Stacks 03KL, part (3), and Stacks 03HE. -/
theorem pushforward_isQuasicoherentOnSite_of_forall_affine_chart_general (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hchart : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiCompactSpace B S hS (chartBaseChangeSpace B S hS f V).1 →
      ((modulePushforward B S hS (chartBaseChangeProjection B S hS f V)).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F)).IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_modulePushforward_iff_forall_affine_chart B S hS f F).2 fun V hV ↦
    hchart V hV (isQuasiCompact_chartBaseChangeProjection B S hS f V hfqc)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)
      (isQuasiCompactSpace_chartBaseChange B S hS f V hV hfqc)

/-! ### The reduction in arbitrary degree -/

/-- **The first step of the proof of Stacks 0720.** If for every affine étale scheme chart `V`
of `Y` the degree-`n` higher direct image `R^n f'_*(F|_U)` along the base change
`f' : U = V ×_Y X ⟶ V` of `f` is quasi-coherent, then so is `R^n f_*F`.

The chartwise identification is
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives`, whose
hypothesis is Stacks 03F3, part (1), for the étale structure morphism `U ⟶ X`,
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`; quasi-coherence is then
tested on the affine étale charts by Stacks 03M0, condition (4). -/
theorem isQuasicoherentOnSite_rightDerived_of_chartwise_general (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (hchart : ChartwiseIsQuasicoherentHigherDirectImage B S hS f F n) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine isQuasicoherentOnSite_of_forall_affine_chart B S hS _ fun V hV ↦ ?_
  have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
    (chartBaseChangeSpace B S hS f V).2
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives B S hS
      (chartBaseChangeInclusion B S hS f V)
      (chartBaseChangeProjection B S hS f V) f (chartToSpace B S hS Y V)
      (isPullback_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y V)
      (preservesInjectiveObjects_etaleModulePullback B S hS _
        (isEtale_chartBaseChangeInclusion B S hS f V)) n).app F) (hchart V hV)

/-- **The first step of the proof of Stacks 0720: the reduction to an affine base.** Let
`f : X ⟶ Y` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and let `F`
be an `𝒪_X`-module on the small étale site of `X`. If for every affine étale scheme chart `V`
of `Y` the higher direct image `R^n f'_*(F|_U)` along the base change `f' : U = V ×_Y X ⟶ V` is
quasi-coherent whenever `f'` is quasi-compact and quasi-separated with quasi-compact source,
then `R^n f_*F` is quasi-coherent.

As in degree zero those three properties of `f'` are supplied from those of `f`, by
Stacks 03HF, Stacks 03KL, part (3), and Stacks 03HE. -/
theorem isQuasicoherentOnSite_rightDerived_of_forall_affine_chart_general (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (hchart : ∀ V : SmallEtale B S hS Y.1,
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
  isQuasicoherentOnSite_rightDerived_of_chartwise_general B S hS f F n
    fun V hV ↦ hchart V hV (isQuasiCompact_chartBaseChangeProjection B S hS f V hfqc)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)
      (isQuasiCompactSpace_chartBaseChange B S hS f V hV hfqc)

end AlgebraicGeometry.Space

end
