module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedGlobalSectionsOnABigSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedLowerShriekOfTheConstantSheaf

/-!
# Derived global sections along a functor of sites, from the counit form of `Lg_! ℤ = ℤ`

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and `g : Sh(C) ⟶ Sh(D)` the
corresponding morphism of topoi. **Stacks 0H0Z** is stated in this library in its sharp form:
the counit `Lg_!(g⁻¹ℤ_D) ⟶ ℤ_D` of the derived adjunction `Lg_! ⊣ g⁻¹` is invertible at the
constant sheaf `ℤ_D` placed in degree zero. The comparison
`Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianGlobalSectionsRestrictionIso`,

`RΓ(C, g⁻¹K) = RΓ(D, K)`,

takes its two inputs in another shape: invertibility of the comparison `Lg_! ⟶ g_!` at
`ℤ_C[0]` (`DerivedAbelianLowerShriekComputesConstant`) and an isomorphism
`Γ(C, g⁻¹ -) ≅ Γ(D, -)`. This file derives both from the counit form, which closes the argument
of **Stacks 0H10 (1)(a), (2)(a)**:

`RΓ(D, K) = RHom(ℤ_D, K) = RHom(Lg_! ℤ_C, K) = RHom(ℤ_C, g⁻¹K) = RΓ(C, g⁻¹K)`.

## The argument

1. Invertibility of the derived counit at `ℤ_D[0]` makes the derived restriction bijective on
   morphisms out of `ℤ_D[0]`, hence — the single complex functors being fully faithful and
   commuting with restriction — restriction is bijective on morphisms of sheaves out of `ℤ_D`
   (`abelianRestriction_map_bijective_of_counit`). Equivalently the ordinary counit
   `g_! g⁻¹ ℤ_D ⟶ ℤ_D` is invertible (`isIso_abelianAdjunction_counit_constantSheaf`, the degree
   zero part of Stacks 0H0Z), and, `ℤ` corepresenting global sections,
   `Γ(C, g⁻¹ -) ≅ Γ(D, -)` (`globalSectionsRestrictionIsoOfCounit`).
2. The derived counit at `ℤ_D[0]` factors as the comparison `Lg_! ⟶ g_!` at `g⁻¹ℤ_D[0]` followed
   by the ordinary counit in degree zero; both counits being invertible, so is the comparison,
   and `g⁻¹ ℤ_D ≅ ℤ_C` transports this to `ℤ_C[0]`
   (`derivedAbelianLowerShriekComputesConstant_of_counit`).

## Main results

* `derivedAbelianGlobalSectionsRestrictionIsoOfCounit`: `g⁻¹ ⋙ RΓ(C, -) ≅ RΓ(D, -)`, from the
  counit form of Stacks 0H0Z alone.

## References

* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁

namespace Stacks.Cohomology.DerivedLowerShriek.BigSite

section Comparison

variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]

attribute [local instance] HasDerivedCategory.standard

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

/-- **Stacks 0H0Z, in the form this file uses**: the counit of the derived adjunction
`Lg_! ⊣ g⁻¹` is invertible at the constant sheaf `ℤ_D` placed in degree zero. -/
abbrev DerivedLowerShriekConstantSheafCounitIsIso : Prop :=
  IsIso ((derivedAbelianLowerShriekAdjunction.{max u₁ v w} J K f).counit.app
    ((DerivedCategory.singleFunctor _ 0).obj (constantIntegerSheaf.{w} K)))

variable {J K f}

/-- The counit of an adjunction is invertible at `X` iff the right adjoint is bijective on
morphisms out of `X`. -/
private lemma isIso_counit_app_iff_map_bijective {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ]
    {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} (adj : L ⊣ R) (X : ℬ) :
    IsIso (adj.counit.app X) ↔
      ∀ Y, Function.Bijective (R.map : (X ⟶ Y) → (R.obj X ⟶ R.obj Y)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun Y => ?_
  have h : (fun x : X ⟶ Y => adj.counit.app X ≫ x) = (adj.homEquiv _ Y).symm ∘ R.map := by
    funext x
    simp [Adjunction.homEquiv_counit]
  exact (congrArg Function.Bijective h).to_iff.trans (Equiv.comp_bijective _ _)

/-- A right adjoint is bijective on morphisms out of an object at which the counit is
invertible. -/
lemma rightAdjoint_map_bijective_of_isIso_counit {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ]
    {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} (adj : L ⊣ R) (X Y : ℬ) [IsIso (adj.counit.app X)] :
    Function.Bijective (R.map : (X ⟶ Y) → (R.obj X ⟶ R.obj Y)) :=
  (isIso_counit_app_iff_map_bijective adj X).1 inferInstance Y

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{max u₁ v w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{max u₁ v w}] in
/-- **Restriction is bijective on morphisms of sheaves out of `ℤ_D`**, given Stacks 0H0Z. The
derived restriction is bijective on morphisms out of `ℤ_D[0]`, the derived counit being
invertible there, and the single complex functors are fully faithful and commute with
restriction. -/
lemma abelianRestriction_map_bijective_of_counit
    (hZ : DerivedLowerShriekConstantSheafCounitIsIso.{w} J K f)
    (F : Sheaf K AddCommGrpCat.{max u₁ v w}) :
    Function.Bijective ((abelianRestriction.{max u₁ v w} J K f).map :
      (constantIntegerSheaf.{w} K ⟶ F) → _) := by
  set R := abelianRestriction.{max u₁ v w} J K f
  set SJ := DerivedCategory.singleFunctor (Sheaf J AddCommGrpCat.{max u₁ v w}) 0
  set SK := DerivedCategory.singleFunctor (Sheaf K AddCommGrpCat.{max u₁ v w}) 0
  set σ := R.mapDerivedCategorySingleFunctor 0
  have hD := rightAdjoint_map_bijective_of_isIso_counit
    (derivedAbelianLowerShriekAdjunction.{max u₁ v w} J K f)
    (SK.obj (constantIntegerSheaf.{w} K)) (SK.obj F)
  have hcomp : (SJ.map ∘ (R.map : (constantIntegerSheaf.{w} K ⟶ F) → _)) =
      (fun ψ => σ.inv.app _ ≫ ψ ≫ σ.hom.app F) ∘ R.mapDerivedCategory.map ∘ SK.map := by
    funext φ
    have := σ.hom.naturality φ
    simp only [Functor.comp_map] at this
    simp only [Function.comp_apply]
    rw [this, Iso.inv_hom_id_app_assoc]
  have hconj : Function.Bijective
      (fun ψ : R.mapDerivedCategory.obj (SK.obj (constantIntegerSheaf.{w} K)) ⟶
          R.mapDerivedCategory.obj (SK.obj F) => σ.inv.app _ ≫ ψ ≫ σ.hom.app F) :=
    (Iso.homCongr (σ.app _) (σ.app F)).bijective
  have hall : Function.Bijective (SJ.map ∘ (R.map : (constantIntegerSheaf.{w} K ⟶ F) → _)) := by
    rw [hcomp]
    exact hconj.comp (hD.comp ((Functor.FullyFaithful.ofFullyFaithful SK).map_bijective _ _))
  exact (Function.Bijective.of_comp_iff' ((Functor.FullyFaithful.ofFullyFaithful SJ).map_bijective
    _ _) _).1 hall

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{max u₁ v w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{max u₁ v w}] in
/-- **The degree-zero part of Stacks 0H0Z: `g_! ℤ_C = ℤ_D`.** Given that the derived counit is
invertible at `ℤ_D[0]`, so is the ordinary counit `g_! g⁻¹ ℤ_D ⟶ ℤ_D`. -/
theorem isIso_abelianAdjunction_counit_constantSheaf
    (hZ : DerivedLowerShriekConstantSheafCounitIsIso.{w} J K f) :
    IsIso ((abelianAdjunction.{max u₁ v w} J K f).counit.app (constantIntegerSheaf.{w} K)) :=
  (isIso_counit_app_iff_map_bijective _ _).2 (abelianRestriction_map_bijective_of_counit hZ)

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{max u₁ v w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{max u₁ v w}] in
/-- **The comparison `Lg_! ⟶ g_!` is invertible at `g⁻¹ ℤ_D` placed in degree zero**, given
Stacks 0H0Z. The counit of the derived adjunction at `ℤ_D[0]` factors as this comparison followed
by the ordinary counit `g_! g⁻¹ ℤ_D ⟶ ℤ_D` in degree zero, and both the derived and the ordinary
counit are invertible there. -/
theorem isIso_derivedAbelianLowerShriekComparison_app_single
    (hZ : DerivedLowerShriekConstantSheafCounitIsIso.{w} J K f) :
    IsIso ((derivedAbelianLowerShriekComparison.{max u₁ v w} J K f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj
          ((abelianRestriction.{max u₁ v w} J K f).obj (constantIntegerSheaf.{w} K))))) := by
  set R := abelianRestriction.{max u₁ v w} J K f
  set Z := constantIntegerSheaf.{w} K
  set N := (HomotopyCategory.quotient (Sheaf K AddCommGrpCat.{max u₁ v w})
    (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj Z)
  have h1 : IsIso ((derivedAbelianLowerShriekAdjunction.{max u₁ v w} J K f).counit.app
      (DerivedCategory.Qh.obj N)) :=
    (NatTrans.isIso_app_iff_of_iso _
      ((DerivedCategory.quotientCompQhIso _).app ((CochainComplex.singleFunctor _ 0).obj Z) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app Z).symm)).2 hZ
  have h2 : IsIso ((abelianHomotopyAdjunction.{max u₁ v w} J K f).counit.app N) := by
    let v := (NatTrans.mapHomologicalComplex (abelianAdjunction.{max u₁ v w} J K f).counit
      (ComplexShape.up ℤ)).app ((CochainComplex.singleFunctor _ 0).obj Z)
    have : ∀ n, IsIso (v.f n) := by
      intro n
      show IsIso ((abelianAdjunction.{max u₁ v w} J K f).counit.app
        (((CochainComplex.singleFunctor _ 0).obj Z).X n))
      by_cases hn : n = 0
      · subst hn
        exact (NatTrans.isIso_app_iff_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 Z)).2
          (isIso_abelianAdjunction_counit_constantSheaf hZ)
      · have hX : IsZero (((CochainComplex.singleFunctor _ 0).obj Z).X n) :=
          HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
        exact isIso_of_source_target_iso_zero _
          ((R ⋙ abelianLowerShriek.{max u₁ v w} J K f).map_isZero hX).isoZero hX.isoZero
    have : IsIso v := HomologicalComplex.Hom.isIso_of_components _
    show IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map v)
    infer_instance
  have h4 : IsIso ((derivedAbelianLowerShriekComparison.{max u₁ v w} J K f).app
        ((abelianRestrictionOnHomotopy.{max u₁ v w} J K f).obj N) ≫
      DerivedCategory.Qh.map ((abelianHomotopyAdjunction.{max u₁ v w} J K f).counit.app N)) := by
    rw [← derivedAbelianLowerShriekAdjunction_counit_fac.{max u₁ v w} J K f N]
    infer_instance
  have h5 : IsIso ((derivedAbelianLowerShriekComparison.{max u₁ v w} J K f).app
      ((abelianRestrictionOnHomotopy.{max u₁ v w} J K f).obj N)) :=
    IsIso.of_isIso_comp_right _
      (DerivedCategory.Qh.map ((abelianHomotopyAdjunction.{max u₁ v w} J K f).counit.app N))
  exact (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) 0).app Z))).1 h5

omit [HasGlobalSectionsFunctor J AddCommGrpCat.{max u₁ v w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{max u₁ v w}] in
/-- **The comparison `Lg_! ⟶ g_!` is invertible at `ℤ_C[0]`**, given the counit form of
Stacks 0H0Z: this is `isIso_derivedAbelianLowerShriekComparison_app_single` transported along
`g⁻¹ ℤ_D ≅ ℤ_C`. -/
theorem derivedAbelianLowerShriekComputesConstant_of_counit
    (hZ : DerivedLowerShriekConstantSheafCounitIsIso.{w} J K f) :
    DerivedAbelianLowerShriekComputesConstant.{w} J K f :=
  (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
    ((CochainComplex.singleFunctor _ 0).mapIso
      (restriction_constantSheafIso f J K AddCommGrpCat.{max u₁ v w}
        (AddCommGrpCat.of (ULift.{max u₁ v w} ℤ)))))).2
    (isIso_derivedAbelianLowerShriekComparison_app_single hZ)

attribute [local instance] Stacks.Cohomology.GlobalSections.additive_Γ in
/-- **`Γ(C, g⁻¹ -) ≅ Γ(D, -)`**, given the counit form of Stacks 0H0Z: restriction is bijective on
morphisms out of `ℤ_D`, which corepresents global sections on `D`, and `g⁻¹ ℤ_D ≅ ℤ_C`
corepresents global sections on `C`. -/
def globalSectionsRestrictionIsoOfCounit
    (hZ : DerivedLowerShriekConstantSheafCounitIsIso.{w} J K f) :
    abelianRestriction.{max u₁ v w} J K f ⋙ Sheaf.Γ J AddCommGrpCat.{max u₁ v w} ≅
      Sheaf.Γ K AddCommGrpCat.{max u₁ v w} :=
  Functor.isoWhiskerLeft _
      (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{max v w} J ≪≫
        preadditiveCoyoneda.mapIso (restriction_constantSheafIso f J K
          AddCommGrpCat.{max u₁ v w} (AddCommGrpCat.of (ULift.{max u₁ v w} ℤ))).symm.op) ≪≫
    (NatIso.ofComponents (fun F => (AddEquiv.ofBijective
      ((abelianRestriction.{max u₁ v w} J K f).mapAddHom
        (X := constantIntegerSheaf.{w} K) (Y := F))
      (abelianRestriction_map_bijective_of_counit hZ F)).toAddCommGrpIso) (by
        intro F G g
        ext φ
        exact ((abelianRestriction.{max u₁ v w} J K f).map_comp φ g).symm)).symm ≪≫
    (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{max v w} K).symm

variable [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})]

/-- **`RΓ(C, g⁻¹K) = RΓ(D, K)` from the counit form of `Lg_! ℤ = ℤ`.** Let `u : C ⥤ D` be a
continuous and cocontinuous functor of sites and `g : Sh(C) ⟶ Sh(D)` the corresponding morphism
of topoi. If the counit `Lg_! g⁻¹ ℤ_D ⟶ ℤ_D` of the derived adjunction is invertible at `ℤ_D[0]`
(Stacks 0H0Z), then derived restriction followed by derived global sections on `C` is derived
global sections on `D`, naturally on the unbounded derived category of abelian sheaves on `D`.
This is the argument of Stacks 0H10 (1)(a), (2)(a). -/
def derivedAbelianGlobalSectionsRestrictionIsoOfCounit
    (hZ : DerivedLowerShriekConstantSheafCounitIsIso.{w} J K f) :
    derivedAbelianRestriction.{max u₁ v w} J K f ⋙ derivedAbelianGlobalSections.{w} J ≅
      derivedAbelianGlobalSections.{w} K :=
  derivedAbelianGlobalSectionsRestrictionIso.{w} J K f
    (derivedAbelianLowerShriekComputesConstant_of_counit hZ)
    (globalSectionsRestrictionIsoOfCounit hZ)

end Comparison

end Stacks.Cohomology.DerivedLowerShriek.BigSite

end
