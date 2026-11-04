module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectivesEssentiallySmall

/-! # K-injectivity descends to a slice site, over a site with large objects

Let `(C, J)` be a site whose objects form a type in an arbitrary universe `c` while its
morphisms, its sheaf of rings `R` and its modules all live in one universe `u`, and suppose that
`C` is essentially `u`-small. For an object `U` of `C`, extension by zero along `C/U ⥤ C` is
exact, and restriction to `C/U` carries a K-injective complex of sheaves of `R`-modules to a
K-injective complex.

## Main results

* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZero_exact`: extension by zero of
  sheaves of modules along `C/U ⥤ C` is exact.
* `Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`: restriction to `C/U`
  preserves K-injective complexes of sheaves of modules.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.OfEssentiallySmall

universe u c

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Extension by zero of sheaves of modules along the localization `C/U ⥤ C` is exact, for an
essentially small site whose objects need not lie in the universe of its morphisms. -/
theorem extensionByZero_exact :
    exactFunctor _ _ (SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) := by
  have := sheafRestrictionIsRightAdjoint J R U
  let F := SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let adj := SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · have : (SheafOfModules.pushforward.{u} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).Additive :=
      ⟨by intros; ext V x; rfl⟩
    have : F.Additive := adj.left_adjoint_additive
    have : Functor.PreservesMonomorphisms F := extensionByZero_preservesMonomorphisms J R U
    have : PreservesColimits F := adj.leftAdjoint_preservesColimits
    have : Functor.PreservesHomology F :=
      Functor.preservesHomology_of_preservesMonos_and_cokernels F
    exact Functor.preservesFiniteLimits_of_preservesHomology F
  · have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits F

end Stacks.Sites.ExtensionByZero.OfEssentiallySmall

namespace Stacks.Cohomology.Localization

universe u c

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of sheaves of modules to a slice site is additive, over an essentially small
site whose objects need not lie in the universe of its morphisms. -/
instance additive_overFunctor_of_essentiallySmall :
    (SheafOfModules.overFunctor.{u} R U).Additive :=
  inferInstanceAs (SheafOfModules.pushforward.{u}
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).Additive

/-- Restriction to the slice site over an object preserves K-injective complexes of sheaves of
modules, for an essentially small site whose objects need not lie in the universe of its
morphisms. -/
theorem isKInjective_over_of_essentiallySmall
    (I : CochainComplex (SheafOfModules.{u} R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let F := SheafOfModules.overFunctor.{u} R U
  let G := SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  obtain ⟨_, _⟩ := (exactFunctor_iff G).mp
    (Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZero_exact J R U)
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact F G
    (SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) I

end Stacks.Cohomology.Localization

end
