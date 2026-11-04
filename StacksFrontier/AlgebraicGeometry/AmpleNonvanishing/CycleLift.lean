module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TwistedSectionChart
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormulaLeft
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.ExtUnit
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.Basic

/-!
# Lifting a nonzero section of a quotient along an ample twist

Let `X` be a scheme with an ample invertible module `L`, and let `π : Z ⟶ H` be an epimorphism
of quasi-coherent `𝒪_X`-modules with `H ≠ 0`. Then for some `p ≥ 0` there is a morphism
`φ : L^{⊗ -p} ⟶ Z` whose composite with `π` is nonzero.

This is the module-level step of the proof of [Stacks, Tag 0BQR]: a nonzero section of `H` over
an affine nonvanishing open `X_s` lifts to `Z` because `X_s` is affine, the lift extends to a
global section of `Z ⊗ L^{⊗ p}` after multiplication by a power of `s` ([Stacks, Tag 01PW]),
and its image in `H ⊗ L^{⊗ p}` is nonzero because it restricts on `X_s` to the product of a
nonzero section with a nowhere vanishing one. Tensoring with `L^{⊗ -p}` turns the global
section into a morphism out of `L^{⊗ -p}`.

## Main results

* `Stacks.AmpleNonvanishing.whiskerRight_injective_of_iso_unit`: whiskering by an invertible
  object is injective on morphisms.
* `Stacks.AmpleNonvanishing.exists_tensorPow_hom_comp_ne_zero`: the statement above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.SectionExtension (resTop)

universe u

namespace Stacks.AmpleNonvanishing

/-- **Whiskering by an invertible object is injective on morphisms**: if `B ⊗ A ≅ 𝟙`, then
`f ▷ B = g ▷ B` forces `f = g`. -/
theorem whiskerRight_injective_of_iso_unit {C : Type*} [Category C] [MonoidalCategory C]
    {A B : C} (e : B ⊗ A ≅ 𝟙_ C) {X Y : C} {f g : X ⟶ Y} (h : f ▷ B = g ▷ B) : f = g := by
  have h1 : f ▷ (B ⊗ A) = g ▷ (B ⊗ A) := by
    rw [MonoidalCategory.whiskerRight_tensor, MonoidalCategory.whiskerRight_tensor, h]
  have h2 : f ▷ 𝟙_ C = g ▷ 𝟙_ C := by
    have key (k : X ⟶ Y) : k ▷ 𝟙_ C = (X ◁ e.inv) ≫ k ▷ (B ⊗ A) ≫ (Y ◁ e.hom) := by
      rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp, e.inv_hom_id,
        MonoidalCategory.whiskerLeft_id, Category.comp_id]
    rw [key f, key g, h1]
  rw [← cancel_mono (ρ_ Y).inv, MonoidalCategory.rightUnitor_inv_naturality,
    MonoidalCategory.rightUnitor_inv_naturality, h2]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

open Stacks.SectionTensorFormula (tensorSection)

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)

include hL in
/-- **A nonzero section of a quotient lifts to a twisted global section with nonzero image.**
For `π : Z ⟶ H` an epimorphism of quasi-coherent modules with `H ≠ 0` there is a global section
`τ` of `Z ⊗ L^{⊗ p}` whose image in `H ⊗ L^{⊗ p}` is nonzero. -/
theorem exists_tensorPow_section_comp_ne_zero {Z H : X.Modules} [Z.IsQuasicoherent]
    [H.IsQuasicoherent] (π : Z ⟶ H) [Epi π] (hH : ¬ IsZero H) :
    ∃ (p : ℕ) (τ : Γ(Z ⊗ tensorPowModule X L (p : ℤ), ⊤)),
      (π ▷ tensorPowModule X L (p : ℤ)).val.app (op ⊤) τ ≠ 0 := by
  obtain ⟨x, hx⟩ := Stacks.AmpleNonvanishingChart.exists_point_not_isZero_stalk H hH
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL x
  obtain ⟨t, ht⟩ :=
    Stacks.AmpleNonvanishingChart.exists_section_ne_zero_of_isAffineOpen H _ haff x hxs hx
  obtain ⟨t', rfl⟩ := surjective_app_of_epi_of_isAffineOpen π haff t
  obtain ⟨p, σ, τ, hopen, heq⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple L hL Z hn s t'
  refine ⟨p, τ, fun hτ => ht (Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero H
    (tensorPowModule X L (p : ℤ)) σ (fun y hy => ?_) ?_)⟩
  · rw [hopen] at hy
    exact hy
  · have h1 := Stacks.SectionTensorFormula.tensorSection_whiskerRight
      (G := tensorPowModule X L (p : ℤ)) π t' (resTop _ σ)
    rw [← heq] at h1
    refine h1.symm.trans ?_
    refine (PresheafOfModules.naturality_apply (π ▷ tensorPowModule X L (p : ℤ)).val
      (homOfLE (le_top : Stacks.AmpleTheory.powNonvanishingOpen X L n s ≤ ⊤)).op τ).trans ?_
    rw [hτ, map_zero]
    rfl

include hL in
/-- **A nonzero section of a quotient lifts along a negative twist.** For `π : Z ⟶ H` an
epimorphism of quasi-coherent modules with `H ≠ 0` there are `p ≥ 0` and a morphism
`φ : L^{⊗ -p} ⟶ Z` with `φ ≫ π ≠ 0`. -/
theorem exists_tensorPow_hom_comp_ne_zero {Z H : X.Modules} [Z.IsQuasicoherent]
    [H.IsQuasicoherent] (π : Z ⟶ H) [Epi π] (hH : ¬ IsZero H) :
    ∃ (p : ℕ) (φ : tensorPowModule X L (-(p : ℤ)) ⟶ Z), φ ≫ π ≠ 0 := by
  obtain ⟨p, τ, hτ⟩ := exists_tensorPow_section_comp_ne_zero L hL π hH
  let A := tensorPowModule X L (p : ℤ)
  let B := tensorPowModule X L (-(p : ℤ))
  let h := Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X
  let e : A ⊗ B ≅ 𝟙_ X.Modules :=
    AlgebraicGeometry.SheafOfModules.tensorPowAddIso X.presheaf h L (p : ℤ) (-(p : ℤ)) ≪≫
      eqToIso (by rw [add_neg_cancel]; rfl)
  let e' : B ⊗ A ≅ 𝟙_ X.Modules :=
    AlgebraicGeometry.SheafOfModules.tensorPowAddIso X.presheaf h L (-(p : ℤ)) (p : ℤ) ≪≫
      eqToIso (by rw [neg_add_cancel]; rfl)
  let M : X.Modules := Z ⊗ A
  let ψ₀ : unitModule X ⟶ Z ⊗ A := Stacks.AlgebraicGeometry.ExtUnit.unitHomAddEquiv X M τ
  let ψ : 𝟙_ X.Modules ⟶ Z ⊗ A := (unitModuleIsoTensorUnit X).inv ≫ ψ₀
  refine ⟨p, (λ_ B).inv ≫ (ψ ▷ B) ≫ (α_ Z A B).hom ≫ (Z ◁ e.hom) ≫ (ρ_ Z).hom, fun h0 => hτ ?_⟩
  have hnat : ((λ_ B).inv ≫ (ψ ▷ B) ≫ (α_ Z A B).hom ≫ (Z ◁ e.hom) ≫ (ρ_ Z).hom) ≫ π =
      (λ_ B).inv ≫ ((ψ ≫ π ▷ A) ▷ B) ≫ (α_ H A B).hom ≫ (H ◁ e.hom) ≫ (ρ_ H).hom := by
    simp only [Category.assoc, MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.rightUnitor_naturality, ← whisker_exchange_assoc,
      MonoidalCategory.associator_naturality_left_assoc]
  rw [hnat] at h0
  have h1 : (ψ ≫ π ▷ A) ▷ B = 0 := by
    have := congrArg (fun f => (λ_ B).hom ≫ f ≫ (ρ_ H).inv ≫ (H ◁ e.inv) ≫ (α_ H A B).inv) h0
    simpa using this
  have h2 : ψ ≫ π ▷ A = 0 :=
    whiskerRight_injective_of_iso_unit e'
      (h1.trans ((MonoidalCategory.tensorRight B).map_zero _ _).symm)
  have h2' : ψ₀ ≫ π ▷ A = 0 :=
    (Iso.hom_inv_id_assoc (unitModuleIsoTensorUnit X) (ψ₀ ≫ π ▷ A)).symm.trans
      ((congrArg (fun f => (unitModuleIsoTensorUnit X).hom ≫ f) h2).trans (Limits.comp_zero))
  have h3 := congrArg (fun f : unitModule X ⟶ H ⊗ A =>
    (SheafOfModules.Hom.val f).app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤))) h2'
  have h4 := Stacks.AlgebraicGeometry.ExtUnit.unitHomAddEquiv_app_one X M τ
  refine Eq.trans ?_ h3
  show _ = (π ▷ A).val.app (op ⊤) (ψ₀.val.app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤)))
  exact congrArg _ h4.symm

end Stacks.AmpleNonvanishing

end
