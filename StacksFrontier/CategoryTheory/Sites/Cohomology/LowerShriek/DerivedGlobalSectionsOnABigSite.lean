module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# Derived global sections along a functor of sites that are not small

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and `g : Sh(C) ⟶ Sh(D)` the
corresponding morphism of topoi. This file proves

`RΓ(C, g⁻¹K) = RΓ(D, K)` for `K` in the unbounded derived category of abelian sheaves on `D`,

from two inputs on the constant sheaf `ℤ_C`:

* the counit `Lg_! ℤ_C ⟶ g_! ℤ_C` of the left derived functor of `g_!` is invertible, and
* `Γ(C, g⁻¹(-)) ≅ Γ(D, -)` on abelian sheaves (equivalently, by corepresentability,
  `g_! ℤ_C ≅ ℤ_D`).

Together these say `Lg_! ℤ = ℤ`, which is what the proof of **Stacks 0H10 (1)(a), (2)(a)**
takes from Stacks 0H0Z; the argument is the source's
`RΓ(D, K) = RHom(ℤ, K) = RHom(Lg_! ℤ, K) = RHom(ℤ, g⁻¹K) = RΓ(C, g⁻¹K)`.

It is the global-sections counterpart of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedSectionsOnABigSite.lean`, with
`j_{U!} ℤ_U` replaced by the constant sheaf, at the same universes: `C, D : Type u₁` with
`Category.{v}` and coefficients `AddCommGrpCat.{max u₁ v w}`.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianGlobalSections`: `RΓ(C, -)`.
* `Stacks.Cohomology.DerivedLowerShriek.BigSite.DerivedAbelianLowerShriekComputesConstant`: the
  invertibility of the derived lower-shriek counit at the single complex of `ℤ_C`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianGlobalSectionsRestrictionIso`:
  `g⁻¹ ⋙ RΓ(C, -) ≅ RΓ(D, -)`.

## References

* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁

namespace Stacks.Cohomology.DerivedLowerShriek.BigSite

attribute [local instance] HasDerivedCategory.standard

section GlobalSections

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u₁ v w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u₁ v w}]

/-- Global sections of abelian sheaves are additive, being a right adjoint. -/
instance additive_globalSections : (Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The constant abelian sheaf `ℤ` on a site, at coefficients `AddCommGrpCat.{max u₁ v w}`. -/
abbrev constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u₁ v w} :=
  (constantSheaf J AddCommGrpCat.{max u₁ v w}).obj
    (AddCommGrpCat.of (ULift.{max u₁ v w} ℤ))

/-- `RΓ(C, -)` on abelian sheaves: the unbounded right derived functor of global sections. -/
abbrev derivedAbelianGlobalSections
    [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})] :
    DerivedCategory (Sheaf J AddCommGrpCat.{max u₁ v w}) ⥤
      DerivedCategory AddCommGrpCat.{max u₁ v w} :=
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  ((Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))

end GlobalSections

section Abelian

variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]

variable [HasSheafify J AddCommGrpCat.{max u₁ v w}] [HasSheafify K AddCommGrpCat.{max u₁ v w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{max u₁ v w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{max u₁ v w}]
  [(f.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v w} J K).IsRightAdjoint]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v w}, f.op.HasPointwiseRightKanExtension F]
  [(abelianLowerShriekOnHomotopy.{max u₁ v w} J K f ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian.{max u₁ v w} (Sheaf K AddCommGrpCat.{max u₁ v w})]
  [(derivedAbelianLowerShriek.{max u₁ v w} J K f ⋙
    derivedAbelianRestriction.{max u₁ v w} J K f).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{max u₁ v w} J K f)
      (derivedAbelianRestriction.{max u₁ v w} J K f)).inv ≫
      Functor.whiskerRight (derivedAbelianLowerShriekComparison.{max u₁ v w} J K f)
        (derivedAbelianRestriction.{max u₁ v w} J K f))
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))]

/-- The invertibility of the derived lower-shriek counit at the single complex of the constant
sheaf `ℤ_C`: the statement `Lg_! ℤ_C = g_! ℤ_C` that the higher left derived functors of `g_!`
vanish on `ℤ_C`. -/
abbrev DerivedAbelianLowerShriekComputesConstant : Prop :=
  IsIso ((derivedAbelianLowerShriekComparison.{max u₁ v w} J K f).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj (constantIntegerSheaf.{w} J))))

variable [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})]

omit [HasGlobalSectionsFunctor K AddCommGrpCat.{max u₁ v w}] in
/-- **The restriction of a K-injective complex computes derived global sections.** Global
sections are corepresented by `ℤ_C`, and the derived adjunction `Lg_! ⊣ g⁻¹` turns morphisms out
of `ℤ_C` into morphisms out of `Lg_! ℤ_C = g_! ℤ_C`, where the complex is K-injective. -/
theorem globalSections_restriction_rightDerivedUnit_isIso
    (hZ : DerivedAbelianLowerShriekComputesConstant.{w} J K f)
    (I : CochainComplex (Sheaf K AddCommGrpCat.{max u₁ v w}) ℤ) [I.IsKInjective]
    (RT : DerivedCategory (Sheaf J AddCommGrpCat.{max u₁ v w}) ⥤
      DerivedCategory AddCommGrpCat.{max u₁ v w})
    (α : (Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))] :
    IsIso (α.app ((abelianRestrictionOnHomotopy.{max u₁ v w} J K f).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  refine rightDerivedUnit_isIso_of_corepresentable (Sheaf.Γ J AddCommGrpCat.{max u₁ v w})
    (constantIntegerSheaf.{w} J)
    (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{max v w} J).symm RT α
    (((abelianRestriction.{max u₁ v w} J K f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (fun n => ?_)
  refine qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((abelianRestriction.{max u₁ v w} J K f).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).app I)) ?_
  exact map_bijective_of_adjunction_comparison (abelianHomotopyAdjunction.{max u₁ v w} J K f)
    DerivedCategory.Qh DerivedCategory.Qh
    (derivedAbelianLowerShriekAdjunction.{max u₁ v w} J K f)
    (derivedAbelianLowerShriekComparison.{max u₁ v w} J K f)
    (derivedAbelianRestrictionComparison.{max u₁ v w} J K f)
    (derivedAbelianLowerShriekAdjunction_unit_fac.{max u₁ v w} J K f) _ _
    (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧))

variable {J K f} in
/-- The unit exhibiting derived restriction followed by `RΓ(C, -)` as a candidate right derived
functor of global sections on `D`, given `Γ(C, g⁻¹(-)) ≅ Γ(D, -)`. -/
def restrictedAbelianGlobalSectionsUnit
    (hΓ : abelianRestriction.{max u₁ v w} J K f ⋙ Sheaf.Γ J AddCommGrpCat.{max u₁ v w} ≅
      Sheaf.Γ K AddCommGrpCat.{max u₁ v w}) :
    (Sheaf.Γ K AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedAbelianRestriction.{max u₁ v w} J K f ⋙
        derivedAbelianGlobalSections.{w} J) :=
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso hΓ
    (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (abelianRestrictionOnHomotopy.{max u₁ v w} J K f)
    (((Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (derivedAbelianRestrictionComparison.{max u₁ v w} J K f)
    (derivedAbelianGlobalSections.{w} J) ≫
  (Functor.associator _ _ _).hom

/-- **`RΓ(C, g⁻¹K) = RΓ(D, K)` from `Lg_! ℤ = ℤ`.** Let `u : C ⥤ D` be a continuous and
cocontinuous functor of sites and `g : Sh(C) ⟶ Sh(D)` the corresponding morphism of topoi. If
the derived lower-shriek counit is invertible at `ℤ_C` and `Γ(C, g⁻¹(-)) ≅ Γ(D, -)`, then for
every `K` in the unbounded derived category of abelian sheaves on `D`,
`RΓ(C, g⁻¹K) = RΓ(D, K)`, naturally in `K`. -/
def derivedAbelianGlobalSectionsRestrictionIso
    (hZ : DerivedAbelianLowerShriekComputesConstant.{w} J K f)
    (hΓ : abelianRestriction.{max u₁ v w} J K f ⋙ Sheaf.Γ J AddCommGrpCat.{max u₁ v w} ≅
      Sheaf.Γ K AddCommGrpCat.{max u₁ v w}) :
    derivedAbelianRestriction.{max u₁ v w} J K f ⋙ derivedAbelianGlobalSections.{w} J ≅
      derivedAbelianGlobalSections.{w} K := by
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((Sheaf.Γ K AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  have hβ : (derivedAbelianRestriction.{max u₁ v w} J K f ⋙
      derivedAbelianGlobalSections.{w} J).IsRightDerivedFunctor
        (restrictedAbelianGlobalSectionsUnit.{w} hΓ)
        (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_kInjective _ _ _ (fun I _ => ?_)
    have := globalSections_restriction_rightDerivedUnit_isIso.{w} J K f hZ I _
      (((Sheaf.Γ J AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)))
    dsimp only [restrictedAbelianGlobalSectionsUnit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact Functor.rightDerivedUnique _ _ (restrictedAbelianGlobalSectionsUnit.{w} hΓ)
    (((Sheaf.Γ K AddCommGrpCat.{max u₁ v w}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))

end Abelian

end Stacks.Cohomology.DerivedLowerShriek.BigSite

end
