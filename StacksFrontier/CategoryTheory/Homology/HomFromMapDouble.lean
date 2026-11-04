module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Double

/-!
# Morphisms out of the image of a two-term complex under an additive functor

Let `F : C ⥤ D` be an additive functor, let `g : X₀ ⟶ X₁` be a morphism of `C` and let
`c.Rel i₀ i₁` with `i₀ ≠ i₁`. Mathlib's `HomologicalComplex.double g hi₀₁` is the complex with
`X₀` in degree `i₀`, `X₁` in degree `i₁`, `g` as its only differential and zero elsewhere, so a
morphism from `(F.mapHomologicalComplex c).obj (double g hi₀₁)` to a complex `K` is nothing but
a pair of morphisms `F.obj X₀ ⟶ K.X i₀` and `F.obj X₁ ⟶ K.X i₁` commuting with `F.map g` and
the differential of `K`, the second being annihilated by every differential out of `K.X i₁`.

## Main definitions

* `HomologicalComplex.homFromMapDouble`: the morphism of complexes given by such a pair.
* `HomologicalComplex.isoFromMapDouble`: the isomorphism it gives when the two components are
  isomorphisms and `K` is concentrated in the degrees `i₀` and `i₁`.

## Main results

* `HomologicalComplex.homFromMapDouble_f₀` and `HomologicalComplex.homFromMapDouble_f₁`
  compute its two nonzero components.
* `HomologicalComplex.isIso_homFromMapDouble`: it is an isomorphism when its two components are
  isomorphisms and `K` vanishes outside the degrees `i₀` and `i₁`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

section ZeroObjects

variable {E : Type*} [Category E]

end ZeroObjects

section HomFromMapDouble

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] {X₀ X₁ : C} (g : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁) {K : HomologicalComplex D c}
  (φ₀ : F.obj X₀ ⟶ K.X i₀) (φ₁ : F.obj X₁ ⟶ K.X i₁)
  (comm : φ₀ ≫ K.d i₀ i₁ = F.map g ≫ φ₁)
  (hφ : ∀ k, c.Rel i₁ k → φ₁ ≫ K.d i₁ k = 0)

open scoped Classical in
/-- A morphism from the image under an additive functor of a two-term complex, given by its two
components in the two degrees where the complex is nonzero. -/
noncomputable def homFromMapDouble :
    (F.mapHomologicalComplex c).obj (double g hi₀₁) ⟶ K where
  f k :=
    if hk₀ : k = i₀ then
      eqToHom (by rw [hk₀]; rfl) ≫ F.map (doubleXIso₀ g hi₀₁).hom ≫ φ₀ ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = i₁ then
      eqToHom (by rw [hk₁]; rfl) ≫ F.map (doubleXIso₁ g hi₀₁ h).hom ≫ φ₁ ≫ eqToHom (by rw [hk₁])
    else 0
  comm' k₀ k₁ hk := by
    by_cases h₀ : k₀ = i₀
    · subst h₀
      rw [dite_eq_left rfl]
      obtain rfl := c.next_eq hk hi₀₁
      simp only [dite_eq_right h.symm, Category.id_comp, Category.comp_id, eqToHom_refl]
      dsimp
      rw [double_d g hi₀₁ h, F.map_comp, F.map_comp]
      simp only [Category.assoc]
      rw [← F.map_comp_assoc (doubleXIso₁ g hi₀₁ h).inv (doubleXIso₁ g hi₀₁ h).hom,
        Iso.inv_hom_id, F.map_id, Category.id_comp]
      exact congrArg (F.map (doubleXIso₀ g hi₀₁).hom ≫ ·) comm
    · rw [dite_eq_right h₀]
      by_cases h₁ : k₀ = i₁
      · subst h₁
        dsimp
        rw [ite_eq_left rfl, Category.comp_id, Category.id_comp, Category.assoc, hφ k₁ hk,
          Limits.comp_zero, double_d_eq_zero₀ _ _ _ _ h.symm, F.map_zero, Limits.zero_comp]
      · exact (Functor.map_isZero F (isZero_double_X g hi₀₁ k₀ h₀ h₁)).eq_of_src _ _

omit [HasZeroObject D] in
open scoped Classical in
/-- The component of `homFromMapDouble` in degree `i₀` is `φ₀`, read through the identification
of the image of the double complex's term in that degree. -/
@[simp]
lemma homFromMapDouble_f₀ :
    (homFromMapDouble F g hi₀₁ h φ₀ φ₁ comm hφ).f i₀ = F.map (doubleXIso₀ g hi₀₁).hom ≫ φ₀ := by
  simp [homFromMapDouble]

omit [HasZeroObject D] in
open scoped Classical in
/-- The component of `homFromMapDouble` in degree `i₁` is `φ₁`, read through the identification
of the image of the double complex's term in that degree. -/
@[simp]
lemma homFromMapDouble_f₁ :
    (homFromMapDouble F g hi₀₁ h φ₀ φ₁ comm hφ).f i₁ =
      F.map (doubleXIso₁ g hi₀₁ h).hom ≫ φ₁ := by
  simp [homFromMapDouble, h.symm]

omit [HasZeroObject D] in
/-- `HomologicalComplex.homFromMapDouble` is an isomorphism as soon as its two components are
isomorphisms and the target complex vanishes outside the two degrees `i₀` and `i₁`. -/
theorem isIso_homFromMapDouble [IsIso φ₀] [IsIso φ₁]
    (hK : ∀ k, k ≠ i₀ → k ≠ i₁ → IsZero (K.X k)) :
    IsIso (homFromMapDouble F g hi₀₁ h φ₀ φ₁ comm hφ) := by
  have hf (k) : IsIso ((homFromMapDouble F g hi₀₁ h φ₀ φ₁ comm hφ).f k) := by
    by_cases h₀ : k = i₀
    · subst h₀
      rw [homFromMapDouble_f₀]
      infer_instance
    · by_cases h₁ : k = i₁
      · subst h₁
        rw [homFromMapDouble_f₁]
        infer_instance
      · exact (Functor.map_isZero F (isZero_double_X g hi₀₁ k h₀ h₁)).isIso (hK k h₀ h₁) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The isomorphism from the image under an additive functor of a two-term complex to a complex
`K` concentrated in the same two degrees, given by two component isomorphisms commuting with
the differentials. -/
noncomputable def isoFromMapDouble (e₀ : F.obj X₀ ≅ K.X i₀) (e₁ : F.obj X₁ ≅ K.X i₁)
    (comm' : e₀.hom ≫ K.d i₀ i₁ = F.map g ≫ e₁.hom)
    (hφ' : ∀ k, c.Rel i₁ k → e₁.hom ≫ K.d i₁ k = 0)
    (hK : ∀ k, k ≠ i₀ → k ≠ i₁ → IsZero (K.X k)) :
    (F.mapHomologicalComplex c).obj (double g hi₀₁) ≅ K :=
  letI := isIso_homFromMapDouble F g hi₀₁ h e₀.hom e₁.hom comm' hφ' hK
  asIso (homFromMapDouble F g hi₀₁ h e₀.hom e₁.hom comm' hφ')

end HomFromMapDouble

end HomologicalComplex

end
