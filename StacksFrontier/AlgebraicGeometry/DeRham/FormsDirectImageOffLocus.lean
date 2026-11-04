module

public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageSection
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange

/-!
# The comparison map on direct images of forms where the morphism is an isomorphism

For `f : Y ⟶ X` over `π : X ⟶ S`, the canonical map `Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}`
(`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`) is invertible on the sections over
any open `U` of `X` over which `f` restricts to an isomorphism. For an open immersion this holds
over every open inside the image.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_app_formsDirectImageComparison_of_isOpenImmersion` — along
  an open immersion the comparison is invertible over every open inside the image.
* `AlgebraicGeometry.Scheme.Hom.isIso_app_formsDirectImageComparison_of_isIso_morphismRestrict` —
  the comparison is invertible over every open on which `f` restricts to an isomorphism.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- **Along an open immersion the comparison map on forms is invertible over its image.** For
an open immersion `j : Y ⟶ X` over `π : X ⟶ S` and an open `W ⊆ j(Y)`, the map
`Γ(Ω^d_{X/S}, W) ⟶ Γ(Ω^d_{Y/S}, j⁻¹W)` is an isomorphism. -/
theorem isIso_app_formsDirectImageComparison_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    (π : X ⟶ S) (d : ℤ) (W : X.Opens) (hW : W ≤ j.opensRange) :
    IsIso ((formsDirectImageComparison j π d).app W) := by
  have h₁ := Stacks.Descent.isIso_unitApp j (relativeDifferentialForms π d) W hW
  have h₂ : IsIso (relativeDifferentialFormsMap j π (j ≫ π) (𝟙 S) (by simp) d) :=
    isIso_relativeDifferentialFormsMap_of_etale j π (j ≫ π) (𝟙 S) (by simp) d
  rw [formsDirectImageComparison, Scheme.Modules.Hom.comp_app]
  exact IsIso.comp_isIso' h₁ (inferInstanceAs (IsIso
    ((relativeDifferentialFormsMap j π (j ≫ π) (𝟙 S) (by simp) d).app (j ⁻¹ᵁ W))))

/-- **Over an open on which `f` is an isomorphism, the comparison map on forms is invertible on
sections.** If `f ∣_ U` is an isomorphism, then `Γ(Ω^d_{X/S}, U) ⟶ Γ(Ω^d_{Y/S}, f⁻¹U)` is an
isomorphism. -/
theorem isIso_app_formsDirectImageComparison_of_isIso_morphismRestrict (f : Y ⟶ X) (π : X ⟶ S)
    (d : ℤ) (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso ((formsDirectImageComparison f π d).app U) := by
  set s : U.toScheme ⟶ Y := inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι with hs
  have hsf : s ≫ f = U.ι := by
    rw [hs, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hrange : s.opensRange = f ⁻¹ᵁ U :=
    (Scheme.Hom.opensRange_comp_of_isIso (inv (f ∣_ U)) (f ⁻¹ᵁ U).ι).trans
      (Scheme.Opens.opensRange_ι _)
  have : IsOpenImmersion (s ≫ f) := by rw [hsf]; infer_instance
  have h₁ := isIso_app_formsDirectImageComparison_of_isOpenImmersion (s ≫ f) π d U
    (fun x hx => by
      show x ∈ Set.range (s ≫ f).base
      rw [hsf]
      exact ⟨⟨x, hx⟩, rfl⟩)
  have h₂ := isIso_app_formsDirectImageComparison_of_isOpenImmersion s (f ≫ π) d (f ⁻¹ᵁ U)
    hrange.ge
  rw [formsDirectImageComparison_comp] at h₁
  have h₁' : IsIso ((formsDirectImageComparison f π d).app U ≫
      (formsDirectImageComparison s (f ≫ π) d).app (f ⁻¹ᵁ U)) := h₁
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ ((formsDirectImageComparison f π d).app U)
    ((formsDirectImageComparison s (f ≫ π) d).app (f ⁻¹ᵁ U)) h₂ h₁'

end AlgebraicGeometry.Scheme.Hom
