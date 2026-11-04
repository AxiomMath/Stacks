module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveDetectsIsomorphisms
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleLocalizationBijective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor

/-!
# The derived lower shriek on a sheaf whose higher `Ext` into restricted injectives vanish

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, `g⁻¹` restriction of abelian
sheaves along it, `g_!` its left adjoint and `Lg_! ⊣ g⁻¹` the derived adjunction of Stacks 07AC
(`Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction`). Let `P` be an
abelian sheaf on `C` such that

`Ext^i(P, g⁻¹E) = 0` for every injective abelian sheaf `E` on `D` and every `i ≥ 1`.

Then the comparison `Lg_!(P) ⟶ g_!(P)` is an isomorphism of `D(Ab(D))`, and consequently, for
every K-injective complex `I` of abelian sheaves on `D` and every `n`, the localization map

`Hom_{K(Ab(C))}(P, (g⁻¹ I)[n]) ⟶ Hom_{D(Ab(C))}(P, (g⁻¹ I)[n])`

is bijective: the restriction `g⁻¹ I` computes `RHom(P, -)`, although it need not be K-injective
itself.

The first statement is tested on the injective objects placed in every single degree
(`DerivedCategory.isIso_of_bijective_precomp_singleFunctor_injective`): through the derived
adjunction, morphisms out of `Lg_!(P)` into `E[q]` are morphisms out of `P` into `(g⁻¹ E)[q]`,
which are `Hom(P, g⁻¹E)` for `q = 0` and vanish otherwise, exactly as the morphisms out of
`g_!(P)` into `E[q]` do. The second is
`Stacks.Cohomology.DerivedLowerShriek.map_bijective_of_adjunction_comparison` at the comparison.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction_homEquiv_comparison`:
  the derived adjunction, applied to the comparison followed by the localization of a homotopy
  class, is the localization of the adjoint homotopy class.
* `Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekComparison_app_single`:
  `Lg_!(P) ⟶ g_!(P)` is an isomorphism.
* `Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_single_restriction`: the localization
  map from `P` into the shifts of a restricted K-injective complex is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

universe w' w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

/-- Postcomposition with an isomorphism is bijective. -/
private lemma bijective_comp_isIso_hom {B : Type*} [Category* B] {X Y Y' : B} (e : Y ⟶ Y')
    [IsIso e] : Function.Bijective (fun a : X ⟶ Y => a ≫ e) :=
  ⟨fun _ _ h => (cancel_mono e).mp h, fun b => ⟨b ≫ inv e, by simp⟩⟩

/-- Precomposition stays bijective when the target is replaced by an isomorphic one. -/
private lemma bijective_precomp_of_iso {B : Type*} [Category* B] {X X' Y Y' : B} (c : X ⟶ X')
    (e : Y ≅ Y') (h : Function.Bijective (fun a : X' ⟶ Y => c ≫ a)) :
    Function.Bijective (fun a : X' ⟶ Y' => c ≫ a) := by
  convert (bijective_comp_isIso_hom e.hom).comp (h.comp (bijective_comp_isIso_hom e.inv)) using 1
  funext a
  simp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] [u.IsCocontinuous J K]
  [HasSheafify J AddCommGrpCat.{max v₁ w}] [HasSheafify K AddCommGrpCat.{max v₁ w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max v₁ w} J K).IsRightAdjoint]

attribute [local instance] HasDerivedCategory.standard

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max v₁ w}, u.op.HasPointwiseRightKanExtension F]
  [(abelianLowerShriekOnHomotopy.{w} J K u ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian.{max v₁ w} (Sheaf K AddCommGrpCat.{max v₁ w})]
  [(derivedAbelianLowerShriek.{w} J K u ⋙
    derivedAbelianRestriction.{w} J K u).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{w} J K u)
      (derivedAbelianRestriction.{w} J K u)).inv ≫
      Functor.whiskerRight (derivedAbelianLowerShriekComparison.{w} J K u)
        (derivedAbelianRestriction.{w} J K u))
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))]

/-- **The derived adjunction on a localized homotopy class.** For a complex `M` on `C`, a complex
`Y` on `D` and a homotopy class `ψ : g_! M ⟶ Y`, the morphism `M ⟶ g⁻¹ Y` of the derived
category adjoint to the comparison `Lg_! M ⟶ g_! M` followed by the localization of `ψ` is the
localization of the homotopy class `M ⟶ g⁻¹ Y` adjoint to `ψ`, followed by the comparison of
degreewise and derived restriction. -/
theorem derivedAbelianLowerShriekAdjunction_homEquiv_comparison
    (M : HomotopyCategory (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))
    (Y : HomotopyCategory (Sheaf K AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ))
    (ψ : (abelianLowerShriekOnHomotopy.{w} J K u).obj M ⟶ Y) :
    (derivedAbelianLowerShriekAdjunction.{w} J K u).homEquiv _ _
        ((derivedAbelianLowerShriekComparison.{w} J K u).app M ≫ DerivedCategory.Qh.map ψ) =
      DerivedCategory.Qh.map ((abelianHomotopyAdjunction.{w} J K u).homEquiv _ _ ψ) ≫
        (derivedAbelianRestrictionComparison.{w} J K u).app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    derivedAbelianLowerShriekAdjunction_unit_fac, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact ((derivedAbelianRestrictionComparison.{w} J K u).naturality ψ).symm

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max v₁ w})]

/-- **The comparison `Lg_!(P) ⟶ g_!(P)` is an isomorphism** for an abelian sheaf `P` on `C` with
`Ext^i(P, g⁻¹E) = 0` for every injective abelian sheaf `E` on `D` and every `i ≥ 1`.

Morphisms into `E[q]`, for `E` injective, are tested: precomposition with the comparison on
morphisms out of `g_!(P)`, followed by the derived adjunction, is by
`derivedAbelianLowerShriekAdjunction_homEquiv_comparison` the localization map on homotopy
classes out of `P` into `(g⁻¹E)[q]`, up to the ordinary adjunction; that localization map is
bijective by `DerivedCategory.qh_map_bijective_single_of_ext_eq_zero`. -/
theorem isIso_derivedAbelianLowerShriekComparison_app_single
    (P : Sheaf J AddCommGrpCat.{max v₁ w})
    (hext : ∀ (E : Sheaf K AddCommGrpCat.{max v₁ w}), Injective E → ∀ (n : ℕ)
      (a : Ext.{w'} P ((abelianRestriction.{w} J K u).obj E) (n + 1)), a = 0) :
    IsIso ((derivedAbelianLowerShriekComparison.{w} J K u).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj P))) := by
  set M := (HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ)).obj
    ((CochainComplex.singleFunctor _ 0).obj P)
  set c := (derivedAbelianLowerShriekComparison.{w} J K u).app M
  apply DerivedCategory.isIso_of_bijective_precomp_singleFunctor_injective
  intro E hE q
  set Yc := (CochainComplex.singleFunctor (Sheaf K AddCommGrpCat.{max v₁ w}) q).obj E
  have : Yc.IsKInjective := CochainComplex.isKInjective_single_obj_of_injective E q
  set Y := (HomotopyCategory.quotient (Sheaf K AddCommGrpCat.{max v₁ w}) (ComplexShape.up ℤ)).obj
    Yc
  have hR : Function.Bijective (DerivedCategory.Qh.map :
      (M ⟶ (abelianRestrictionOnHomotopy.{w} J K u).obj Y) → _) :=
    qh_map_bijective_of_iso
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (abelianRestriction.{w} J K u)
          (ComplexShape.up ℤ) q).app E)).symm
      (DerivedCategory.qh_map_bijective_single_of_ext_eq_zero P _ (hext E hE) q)
  let pre : (DerivedCategory.Qh.obj ((abelianLowerShriekOnHomotopy.{w} J K u).obj M) ⟶
      DerivedCategory.Qh.obj Y) → _ := fun a => c ≫ a
  have hcomp : Function.Bijective
      ((derivedAbelianLowerShriekAdjunction.{w} J K u).homEquiv _ _ ∘ pre ∘
        DerivedCategory.Qh.map) := by
    convert (bijective_comp_isIso_hom ((derivedAbelianRestrictionComparison.{w} J K u).app Y)).comp
      (hR.comp ((abelianHomotopyAdjunction.{w} J K u).homEquiv _ _).bijective) using 1
    funext ψ
    exact derivedAbelianLowerShriekAdjunction_homEquiv_comparison J K u M Y ψ
  have hY : Function.Bijective pre :=
    (Function.Bijective.of_comp_iff' (Equiv.bijective _) _).1
      ((Function.Bijective.of_comp_iff _
        (CochainComplex.IsKInjective.Qh_map_bijective _ Yc)).1 hcomp)
  exact bijective_precomp_of_iso c (DerivedCategory.qhSingleIso E q) hY

/-- **A restricted K-injective complex computes `RHom` out of a sheaf with vanishing higher
`Ext` into restricted injectives.** For an abelian sheaf `P` on `C` with `Ext^i(P, g⁻¹E) = 0`
for every injective `E` and every `i ≥ 1`, and a K-injective complex `I` of abelian sheaves on
`D`, the localization map from homotopy classes of morphisms out of `P` placed in degree `0`
into the restriction of `I` to the morphisms of the derived category is bijective. -/
theorem qh_map_bijective_single_restriction
    (P : Sheaf J AddCommGrpCat.{max v₁ w})
    (hext : ∀ (E : Sheaf K AddCommGrpCat.{max v₁ w}), Injective E → ∀ (n : ℕ)
      (a : Ext.{w'} P ((abelianRestriction.{w} J K u).obj E) (n + 1)), a = 0)
    (I : CochainComplex (Sheaf K AddCommGrpCat.{max v₁ w}) ℤ) [I.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj P) ⟶
        (abelianRestrictionOnHomotopy.{w} J K u).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) → _) := by
  have := isIso_derivedAbelianLowerShriekComparison_app_single J K u P hext
  exact map_bijective_of_adjunction_comparison (abelianHomotopyAdjunction.{w} J K u)
    DerivedCategory.Qh DerivedCategory.Qh (derivedAbelianLowerShriekAdjunction.{w} J K u)
    (derivedAbelianLowerShriekComparison.{w} J K u) (derivedAbelianRestrictionComparison.{w} J K u)
    (derivedAbelianLowerShriekAdjunction_unit_fac.{w} J K u) _ _
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)

end Stacks.Cohomology.DerivedLowerShriek
