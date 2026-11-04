module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonSituation

/-!
# The square of topoi commutes after deriving the direct images

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in Stacks 0EZ3, and let
`f : X ⟶ Y` be a morphism of `C`. The square of topoi of Stacks 0EZ2 gives the strict identity
`ε_{X,*} ∘ f_{τ,*} = f_{τ',*} ∘ ε_{Y,*}` of direct images on abelian sheaves over the localized
sites. This file proves the derived form of that identity,

`Rf_{τ',*} ∘ Rε_{X,*} ≅ Rε_{Y,*} ∘ Rf_{τ,*}`

as functors `D(Ab(C_τ/X)) ⥤ D(Ab(C_τ'/Y))`, for arbitrary right derived functors of the four
direct images.

## Main results

* `Stacks.Cohomology.Localization.overPushforward_map_isKInjective`: direct image between
  localized sites preserves K-injective complexes of abelian sheaves.
* `Stacks.ComparingTopologies.abelianComparisonPushforward_map_isKInjective`: change-of-topology
  direct image preserves K-injective complexes of abelian sheaves.
* `Stacks.ComparingTopologies.derivedComparisonSquareIso`: the derived form of the square of
  topoi, `Rε_{X,*} ⋙ Rf_{τ',*} ≅ Rf_{τ,*} ⋙ Rε_{Y,*}`.

## References

* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
* [Stacks Project, Tag 0EZ2](https://stacks.math.columbia.edu/tag/0EZ2)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

universe u v w₁ w₂ w₃ w₄

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- Direct image between localized sites preserves K-injective complexes of abelian sheaves. -/
theorem overPushforward_map_isKInjective
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    [∀ U : C, HasSheafify (J.over U) Ab.{max u v}]
    (I : CochainComplex (AbelianSheaves J X) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((overPushforward J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let _ := hI
  let adj : overPullback J f ⊣ overPushforward J f :=
    (Over.map f).sheafAdjunctionCocontinuous Ab.{max u v} (J.over X) (J.over Y)
  let adj' : (Over.map f).sheafPullback Ab.{max u v} (J.over X) (J.over Y) ⊣
      overPullback J f :=
    (Over.map f).sheafAdjunctionContinuous Ab.{max u v} (J.over X) (J.over Y)
  have := adj.isLeftAdjoint
  have := adj'.isRightAdjoint
  let _ : PreservesFiniteColimits (overPullback J f) :=
    (adj.leftAdjoint_preservesColimits.{max u v, max u v}).preservesFiniteColimits
  let _ : PreservesFiniteLimits (overPullback J f) :=
    (adj'.rightAdjoint_preservesLimits.{max u v, max u v}).preservesFiniteLimits
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ (overPullback J f) adj I

end Stacks.Cohomology.Localization

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- The identity functor of a slice category is continuous from the coarse localized topology to
the fine one. -/
private theorem id_isContinuous (S : CohomologyComparison C) (X : C) :
    (Functor.id (Over X)).IsContinuous (S.coarseCoverage.toGrothendieck.over X)
      (S.fineCoverage.toGrothendieck.over X) where
  op_comp_isSheaf_of_types F := (isSheaf_iff_isSheaf_of_type _ _).1
    (F.property.of_le (over_le_over (Precoverage.toGrothendieck_mono S.coarse_le_fine) X))

/-- Change-of-topology direct image preserves K-injective complexes of abelian sheaves. -/
theorem abelianComparisonPushforward_map_isKInjective (S : CohomologyComparison C) (X : C)
    (I : CochainComplex (AbelianSheaves S.fineCoverage.toGrothendieck X) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let _ := id_isContinuous S X
  let _ := hI
  let L := (Functor.id (Over X)).sheafPullback Ab.{max u v}
    (S.coarseCoverage.toGrothendieck.over X) (S.fineCoverage.toGrothendieck.over X)
  let adj : L ⊣ abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X :=
    (Functor.id (Over X)).sheafAdjunctionContinuous Ab.{max u v} _ _
  have := adj.isLeftAdjoint
  let _ : PreservesFiniteColimits L :=
    (adj.leftAdjoint_preservesColimits.{u, u}).preservesFiniteColimits
  let _ : PreservesFiniteLimits L :=
    preservesFiniteLimits_of_natIso (abelianComparisonPullbackIsoSheafPullback S X)
  let _ : L.Additive := adj.left_adjoint_additive
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ L adj I

/-- The derived form of the square of topoi of Stacks 0EZ2: for arbitrary right derived
functors of the four direct images, total right derived change-of-topology direct image followed
by total right derived direct image along `f` for the coarse topology agrees with total right
derived direct image along `f` for the fine topology followed by total right derived change of
topology. -/
def derivedComparisonSquareIso
    (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} (AbelianSheaves S.fineCoverage.toGrothendieck X)]
    [HasDerivedCategory.{w₂} (AbelianSheaves S.coarseCoverage.toGrothendieck X)]
    [HasDerivedCategory.{w₃} (AbelianSheaves S.fineCoverage.toGrothendieck Y)]
    [HasDerivedCategory.{w₄} (AbelianSheaves S.coarseCoverage.toGrothendieck Y)]
    (RεX : DerivedCategory (AbelianSheaves S.fineCoverage.toGrothendieck X) ⥤
      DerivedCategory (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (Rfc : DerivedCategory (AbelianSheaves S.coarseCoverage.toGrothendieck X) ⥤
      DerivedCategory (AbelianSheaves S.coarseCoverage.toGrothendieck Y))
    (Rff : DerivedCategory (AbelianSheaves S.fineCoverage.toGrothendieck X) ⥤
      DerivedCategory (AbelianSheaves S.fineCoverage.toGrothendieck Y))
    (RεY : DerivedCategory (AbelianSheaves S.fineCoverage.toGrothendieck Y) ⥤
      DerivedCategory (AbelianSheaves S.coarseCoverage.toGrothendieck Y))
    (αεX : homotopyToDerived (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X) ⟶ DerivedCategory.Qh ⋙ RεX)
    (αfc : homotopyToDerived (overPushforward S.coarseCoverage.toGrothendieck f) ⟶
      DerivedCategory.Qh ⋙ Rfc)
    (αff : homotopyToDerived (overPushforward S.fineCoverage.toGrothendieck f) ⟶
      DerivedCategory.Qh ⋙ Rff)
    (αεY : homotopyToDerived (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine Y) ⟶ DerivedCategory.Qh ⋙ RεY)
    [RεX.IsRightDerivedFunctor αεX (HomotopyCategory.quasiIso
      (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ))]
    [Rfc.IsRightDerivedFunctor αfc (HomotopyCategory.quasiIso
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) (ComplexShape.up ℤ))]
    [Rff.IsRightDerivedFunctor αff (HomotopyCategory.quasiIso
      (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ))]
    [RεY.IsRightDerivedFunctor αεY (HomotopyCategory.quasiIso
      (AbelianSheaves S.fineCoverage.toGrothendieck Y) (ComplexShape.up ℤ))] :
    RεX ⋙ Rfc ≅ Rff ⋙ RεY := by
  let εX := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let εY := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine Y
  let gc := overPushforward S.coarseCoverage.toGrothendieck f
  let gf := overPushforward S.fineCoverage.toGrothendieck f
  let W := HomotopyCategory.quasiIso
    (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)
  let _ : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (AbelianSheaves S.fineCoverage.toGrothendieck X) :=
    sheaf_isGrothendieckAbelian (S.fineCoverage.toGrothendieck.over X)
  let _ : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) :=
    sheaf_isGrothendieckAbelian (S.coarseCoverage.toGrothendieck.over X)
  let _ : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (AbelianSheaves S.fineCoverage.toGrothendieck Y) :=
    sheaf_isGrothendieckAbelian (S.fineCoverage.toGrothendieck.over Y)
  let αleft := derivedCompositeUnit εX gc RεX Rfc αεX αfc
  have hleft : (RεX ⋙ Rfc).IsRightDerivedFunctor αleft W := by
    apply derivedComposite_isRightDerived εX gc RεX Rfc αεX αfc
    intro I hI
    let _ : IsIso (αεX.app ((HomotopyCategory.quotient
        (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)).obj I)) :=
      rightDerivedUnit_isIso_app_of_isKInjective _ RεX αεX I hI
    let _ : IsIso (αfc.app ((εX.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (AbelianSheaves S.fineCoverage.toGrothendieck X)
          (ComplexShape.up ℤ)).obj I))) :=
      rightDerivedUnit_isIso_app_of_isKInjective _ Rfc αfc
        ((εX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (abelianComparisonPushforward_map_isKInjective S X I hI)
    dsimp [derivedCompositeUnit]
    infer_instance
  let αright := derivedCompositeUnit gf εY Rff RεY αff αεY
  have hright : (Rff ⋙ RεY).IsRightDerivedFunctor αright W := by
    apply derivedComposite_isRightDerived gf εY Rff RεY αff αεY
    intro I hI
    let _ : IsIso (αff.app ((HomotopyCategory.quotient
        (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)).obj I)) :=
      rightDerivedUnit_isIso_app_of_isKInjective _ Rff αff I hI
    let _ : IsIso (αεY.app ((gf.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (AbelianSheaves S.fineCoverage.toGrothendieck X)
          (ComplexShape.up ℤ)).obj I))) :=
      rightDerivedUnit_isIso_app_of_isKInjective _ RεY αεY
        ((gf.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (overPushforward_map_isKInjective S.fineCoverage.toGrothendieck f I hI)
    dsimp [derivedCompositeUnit]
    infer_instance
  let _ := hleft
  let _ := hright
  exact Functor.rightDerivedNatIso (RεX ⋙ Rfc) (Rff ⋙ RεY) αleft αright W (Iso.refl _)

end Stacks.ComparingTopologies

end
