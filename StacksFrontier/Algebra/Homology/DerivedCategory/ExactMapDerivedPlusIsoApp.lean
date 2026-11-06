module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# Components of the comparison `F.mapDerivedCategoryPlus ≅ F.rightDerivedFunctorPlus`

For an exact additive functor `F : 𝒜 ⥤ ℬ` between abelian categories with derived categories,
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso` identifies the degreewise action of `F`
on bounded below derived categories with its total right derived functor. It is constructed as
a `CategoryTheory.Localization.liftNatIso` along the localization
`Qh : K⁺(𝒜) ⥤ D⁺(𝒜)`, so it is determined by, and computed on the image of `Qh` by, the natural
isomorphism it lifts. This file records that computation in both directions.

## Main results

* `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_hom_app_Qh` and
  `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_inv_app_Qh`: on a bounded below complex
  `N`, the component of the comparison at `Qh.obj N` is the component at `N` of
  `F.mapDerivedCategoryPlusFactorsh ≪≫ asIso F.rightDerivedFunctorPlusUnith`.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

section Exact

attribute [local instance]
  CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The comparison between the degreewise action and the right derived functor of an exact
functor, on the image of the localization.** Being a lift along `Qh` of
`F.mapDerivedCategoryPlusFactorsh ≪≫ asIso F.rightDerivedFunctorPlusUnith`, it agrees with that
isomorphism componentwise on bounded below complexes. -/
theorem exactMapDerivedCategoryPlusIso_hom_app_Qh (N : HomotopyCategory.Plus C) :
    (exactMapDerivedCategoryPlusIso F).hom.app (DerivedCategory.Plus.Qh.obj N) =
      (F.mapDerivedCategoryPlusFactorsh ≪≫ asIso F.rightDerivedFunctorPlusUnith).hom.app N := by
  simp [exactMapDerivedCategoryPlusIso]

/-- The inverse half of `exactMapDerivedCategoryPlusIso_hom_app_Qh`. -/
theorem exactMapDerivedCategoryPlusIso_inv_app_Qh (N : HomotopyCategory.Plus C) :
    (exactMapDerivedCategoryPlusIso F).inv.app (DerivedCategory.Plus.Qh.obj N) =
      (F.mapDerivedCategoryPlusFactorsh ≪≫ asIso F.rightDerivedFunctorPlusUnith).inv.app N := by
  simp [exactMapDerivedCategoryPlusIso]

end Exact

end Stacks.DerivedFunctor

end
