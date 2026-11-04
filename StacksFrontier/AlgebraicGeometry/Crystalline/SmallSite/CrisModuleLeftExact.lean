module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageCocontinuous
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiModuleDirectImage

/-!
# `f_{cris, *}` on modules is left exact, and `R^0 f_{cris, *} ≅ f_{cris, *}`

The module-valued direct image

  `f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})`

is a composite of five functors: two ring-universe comparisons, the two cocontinuous
pushforwards `i_{X, *}` and `f_{CRIS, *}`, and the restriction `π_{X', *}`. Each factor is left
exact, hence so is `f_{cris, *}`, and its zeroth right derived functor is `f_{cris, *}` itself.

## Main results

* `preservesFiniteLimits_bigModuleDirectImage`,
  `preservesFiniteLimits_smallModuleRestrictionULift`,
  `preservesFiniteLimits_changeBaseModuleDirectImage`: each factor of `f_{cris, *}` on modules
  is left exact.
* `preservesFiniteLimits_crisModuleDirectImage`: `f_{cris, *}` on modules is left exact.
* `higherCrisModuleDirectImageZeroIso`: `R^0 f_{cris, *} ≅ f_{cris, *}` on modules.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

universe u

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **The module-valued `i_{X, *}` of [Stacks, Tag 07IJ] is left exact.** -/
instance preservesFiniteLimits_bigModuleDirectImage :
    PreservesFiniteLimits (bigModuleDirectImage S) :=
  have : PreservesLimitsOfSize.{u + 1, u + 1} (bigModuleDirectImage S) :=
    inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1}
      (Stacks.SheafOfModules.pushforwardCocontinuous.{u + 1} (CrystallineThickening.ι S)
        (bigRingStructureMapULift S)))
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- **The module-valued restriction `π_{X, *} = i_X^{-1}` of [Stacks, Tag 07IJ] is left
exact.** -/
instance preservesFiniteLimits_smallModuleRestrictionULift :
    PreservesFiniteLimits (smallModuleRestrictionULift S) := by
  have h : PreservesFiniteLimits (smallModuleRestrictionULift S ⋙
      SheafOfModules.toSheaf.{u + 1} (structureSheafULift S)) := by
    rw [smallModuleRestrictionULift_comp_toSheaf]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{u + 1} (structureSheafULift S))

include hf

/-- **The module-valued `f_{CRIS, *}` of [Stacks, Tag 07IC] is left exact.** -/
instance preservesFiniteLimits_changeBaseModuleDirectImage :
    PreservesFiniteLimits (changeBaseModuleDirectImage S S' fS fX hf) :=
  have : PreservesLimitsOfSize.{u + 1, u + 1} (changeBaseModuleDirectImage S S' fS fX hf) :=
    inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1}
      (Stacks.SheafOfModules.pushforwardCocontinuous.{u + 1} (changeBase S S' fS fX hf)
        (changeBaseRingStructureMapULift S S' fS fX hf)))
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The ring-universe comparison `Mod(𝒪^{ULift}_{X/S}) ⥤ Mod(𝒪_{X/S})` is an equivalence of
categories. -/
instance isEquivalence_moduleRingULiftDown : (moduleRingULiftDown S).IsEquivalence :=
  (moduleRingULiftEquivalence S).isEquivalence_inverse

/-- **`f_{cris, *}` on modules is left exact.** -/
instance preservesFiniteLimits_crisModuleDirectImage :
    PreservesFiniteLimits (crisModuleDirectImage S S' fS fX hf) :=
  inferInstanceAs (PreservesFiniteLimits (moduleRingULiftUp S ⋙ bigModuleDirectImage S ⋙
    changeBaseModuleDirectImage S S' fS fX hf ⋙ smallModuleRestrictionULift S' ⋙
      moduleRingULiftDown S'))

/-- **`R^0 f_{cris, *} ≅ f_{cris, *}` on modules.** -/
def higherCrisModuleDirectImageZeroIso :
    higherCrisModuleDirectImage S S' fS fX hf 0 ≅ crisModuleDirectImage S S' fS fX hf :=
  (crisModuleDirectImage S S' fS fX hf).rightDerivedZeroIsoSelf

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
