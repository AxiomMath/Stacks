module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseStructureSharp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism

/-!
# The derived direct images over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site, `f : Z₁ ⟶ Z₂` a morphism of algebraic spaces
over `W` and `g : Y₁ ⟶ Y₂` one over `S`, matched by `εᵢ : Λ_h Zᵢ ≅ Yᵢ`. This file shows that the
change of base `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` (Stacks 04SG) intertwines
the derived direct images, `Rg_* ⋙ (−)' ≅ (−)' ⋙ Rf_*`, for arbitrary `f` and `g`, and so proves
the proposition `AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison` that the passage
of Stacks 0DKX from a base `S` to `Spec ℤ` uses.

Both composites are right derived functors of the degreewise direct image followed by the
change of base, which agree by the comparison of the direct images of modules
`AlgebraicGeometry.Space.smallerBaseModulePushforwardIso`; the uniqueness of right derived
functors (`CategoryTheory.Functor.rightDerivedNatIso`) concludes.

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseHomotopyPushforwardIso`: the degreewise comparison.
* `AlgebraicGeometry.Space.smallerBaseDerivedPushforwardUnit`: the unit exhibiting `(−)' ⋙ Rf_*`
  as a right derived functor.
* `AlgebraicGeometry.Space.smallerBaseDerivedPushforwardIso`: `Rg_* ⋙ (−)' ≅ (−)' ⋙ Rf_*`.

## Main results

* `AlgebraicGeometry.Space.isRightDerivedFunctor_smallerBaseDerivedEquivalence_comp`.
* `AlgebraicGeometry.Space.smallerBaseDerivedPushforwardComparison`: the proposition
  `AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison` holds.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0DKX](https://stacks.math.columbia.edu/tag/0DKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS)

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)

/-- The degreewise comparison of the two derivable functors: the degreewise direct image along
`g` followed by the change of base, and the change of base followed by the degreewise direct
image along `f`, through `AlgebraicGeometry.Space.smallerBaseModulePushforwardIso`. -/
def smallerBaseHomotopyPushforwardIso :
    ((modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ (smallerBaseDerivedEquivalence B h ε₂).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        ((modulePushforward B W hW f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (smallerBaseModulesEquivalenceOfIso B h ε₂).functor.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (smallerBaseModulePushforwardIso B h ε₁ ε₂ hfg).symm
          (ComplexShape.up ℤ)).symm) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- The unit exhibiting the change of base followed by `Rf_*` as a right derived functor of the
change of base followed by the degreewise direct image along `f`: the unit of `Rf_*` transported
along the comparison `Qh ⋙ (−)' ≅ (−)' ⋙ Qh` of the localization functors. -/
def smallerBaseDerivedPushforwardUnit :
    (smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((modulePushforward B W hW f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ ((smallerBaseDerivedEquivalence B h ε₁).functor ⋙
        derivedModulePushforward B W hW f) :=
  ((Iso.refl _).hom ≫
      Functor.whiskerLeft
        ((smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapHomotopyCategory
          (ComplexShape.up ℤ))
        (derivedModulePushforwardUnit B W hW f) ≫
      (Functor.associator
        ((smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapHomotopyCategory
          (ComplexShape.up ℤ))
        DerivedCategory.Qh (derivedModulePushforward B W hW f)).inv) ≫
    Functor.whiskerRight
        (smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapDerivedCategoryFactorsh.inv
      (derivedModulePushforward B W hW f) ≫
    (Functor.associator DerivedCategory.Qh
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapDerivedCategory
      (derivedModulePushforward B W hW f)).hom

/-- The change of base followed by `Rf_*` is a right derived functor of the change of base
followed by the degreewise direct image along `f`, with unit
`AlgebraicGeometry.Space.smallerBaseDerivedPushforwardUnit`: the derivation of `Rf_*` transported
along the equivalences of homotopy and of derived categories induced by the module equivalence
(`Stacks.DerivedFunctor.isLeftKanExtension_comp_of_equivalence`). -/
instance isRightDerivedFunctor_smallerBaseDerivedEquivalence_comp :
    ((smallerBaseDerivedEquivalence B h ε₁).functor ⋙
      derivedModulePushforward B W hW f).IsRightDerivedFunctor
        (smallerBaseDerivedPushforwardUnit B h ε₁)
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y₁.1 Y₁.2) (ComplexShape.up ℤ)) := by
  have : ((smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapHomotopyCategory
      (ComplexShape.up ℤ)).IsEquivalence :=
    Stacks.DerivedFunctor.isEquivalence_mapHomotopyCategory _
  have : (smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapDerivedCategory.IsEquivalence :=
    (inferInstance : (smallerBaseDerivedEquivalence B h ε₁).functor.IsEquivalence)
  have hf : (derivedModulePushforward B W hW f).IsLeftKanExtension
      (derivedModulePushforwardUnit B W hW f) := by
    rw [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension
      (W := HomotopyCategory.quasiIso (Modules.{u, u} B W hW Z₁.1 Z₁.2) (ComplexShape.up ℤ))]
    infer_instance
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  exact Stacks.DerivedFunctor.isLeftKanExtension_comp_of_equivalence
    (smallerBaseModulesEquivalenceOfIso B h ε₁).functor.mapDerivedCategoryFactorsh
    (derivedModulePushforwardUnit B W hW f) (Iso.refl _) _ rfl

/-- **The derived direct images commute with the change of base**, for an arbitrary morphism:
`Rg_* ⋙ (−)' ≅ (−)' ⋙ Rf_*`. Both sides are right derived functors of the degreewise direct image
followed by the change of base: `Rg_* ⋙ (−)'` because `(−)'` is an equivalence, hence a left
adjoint, and `(−)' ⋙ Rf_*` by
`AlgebraicGeometry.Space.isRightDerivedFunctor_smallerBaseDerivedEquivalence_comp`. The degreewise
functors are compared by `AlgebraicGeometry.Space.smallerBaseHomotopyPushforwardIso`. -/
def smallerBaseDerivedPushforwardIso :
    derivedModulePushforward B S hS g ⋙ (smallerBaseDerivedEquivalence B h ε₂).functor ≅
      (smallerBaseDerivedEquivalence B h ε₁).functor ⋙ derivedModulePushforward B W hW f :=
  Functor.rightDerivedNatIso _ _
    (Functor.whiskerRight (derivedModulePushforwardUnit B S hS g)
        (smallerBaseDerivedEquivalence B h ε₂).functor ≫ (Functor.associator _ _ _).hom)
    (smallerBaseDerivedPushforwardUnit B h ε₁)
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y₁.1 Y₁.2) (ComplexShape.up ℤ))
    (smallerBaseHomotopyPushforwardIso B h ε₁ ε₂ hfg)

/-- **The proposition `AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison` holds**:
the change of base intertwines the derived direct images of arbitrary morphisms
(`AlgebraicGeometry.Space.smallerBaseDerivedPushforwardIso`). -/
theorem smallerBaseDerivedPushforwardComparison :
    SmallerBaseDerivedPushforwardComparison B h :=
  fun ε₁ ε₂ _ _ hfg => ⟨smallerBaseDerivedPushforwardIso B h ε₁ ε₂ hfg⟩

end Derived

end AlgebraicGeometry.Space

end
