module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes
import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.GlobalFunctionsChartBaseChange

/-!
# Universally bijective global functions for a family of curves given by a morphism of schemes

Let `g : T ⟶ U` be a flat proper morphism of finite presentation of schemes of the big fppf site,
with fibres of dimension at most one, such that `𝒪 ⟶ g'_*𝒪` is an isomorphism for every base
change `g'` of `g` along a morphism of schemes (for instance by Stacks 0E0L). Then the family of
curves `F` defined by `g` has `f_*𝒪 = 𝒪` universally in the sense of Stacks 0E6T: pullback of
global functions along the projection `F ×_U Y ⟶ Y` is bijective for every algebraic space `Y`
over `U`. For a scheme `Y` this is the hypothesis; for an algebraic space it follows chart by
chart, global functions on an algebraic space being the compatible families of regular functions
on all of its scheme charts (the atlas step
`AlgebraicGeometry.Space.chartFunctionsToSmall_bijective`) and every scheme chart of `F ×_U Y`
factoring through the base change of a scheme chart of `Y`
(`AlgebraicGeometry.Space.chartFunctionsMap_pullback_snd_bijective`).

## Main results

* `CurveFamily.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfFiberDimensionLE`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Universally bijective global functions from base change of `𝒪 = g_*𝒪` along schemes.** -/
theorem hasUniversallyBijectiveGlobalFunctions_curveFamilyOfFiberDimensionLE
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hfib : ∀ x, topologicalKrullDimAt
      (((BigFppfOver.toScheme B integerBase hZ).map g).fiber
        (((BigFppfOver.toScheme B integerBase hZ).map g) x))
      (((BigFppfOver.toScheme B integerBase hZ).map g).asFiber x) ≤ 1)
    (hc : ∀ {X' S' : Scheme.{u}} {b : S' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj U}
      {b' : X' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj T} {f' : X' ⟶ S'},
      IsPullback b' f' ((BigFppfOver.toScheme B integerBase hZ).map g) b → IsIso f'.c) :
    HasUniversallyBijectiveGlobalFunctions B hZ
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib) := by
  have hΓ : ∀ {W : BigFppfOver B integerBase hZ} (w : W ⟶ U), Function.Bijective
      (Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd g w)).op).hom := by
    intro W w
    have : IsIso ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd g w)).c :=
      hc ((IsPullback.of_hasPullback g w).map (BigFppfOver.toScheme B integerBase hZ))
    have : IsIso (Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map
        (pullback.snd g w)).op) := by
      rw [Scheme.Γ_map_op]
      exact (inferInstance : IsIso (((BigFppfOver.toScheme B integerBase hZ).map
        (pullback.snd g w)).c.app (Opposite.op ⊤)))
    exact ConcreteCategory.bijective_of_isIso _
  intro Y g'
  exact Space.globalFunctionsMap_bijective_of_chartFunctionsMap_bijective _
    (Space.chartFunctionsMap_pullback_snd_bijective g g'.hom hΓ)

end AlgebraicGeometry.CurveFamily

end
