module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsGlobalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamSections
public import StacksFrontier.RingTheory.MvPolynomial.FreeModuleVariablePowerDivisibility
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsChartFactor

/-!
# Direct images of differential forms on sections

For a morphism `f : Y ⟶ X` of schemes over `S`, the canonical map
`Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}` (`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`) is, on the
sections over an open `V`, the pullback of differential forms along `f`. This file records that
description and the bijectivity of the pullback of forms in the cases where `f` is locally an
isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison_app_apply`: on sections the comparison
  map is the pullback of forms.
* `AlgebraicGeometry.Scheme.Hom.bijective_relativeDifferentialFormsPullback_of_isOpenImmersion`:
  pulling back forms along an open immersion is bijective over every open inside its image.
* `AlgebraicGeometry.Scheme.Hom.bijective_relativeDifferentialFormsPullback_of_isIso`: pulling
  back forms along an isomorphism is bijective over every open.
* `AlgebraicGeometry.Scheme.Hom.bijective_formsDirectImageComparison_app_of_isIso_restrict`:
  over an open above which `f` restricts to an isomorphism, `Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}` is
  bijective on sections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- On the sections over an open `V`, the comparison map `Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}` is the
pullback of differential forms along `f`. -/
theorem formsDirectImageComparison_app_apply (f : Y ⟶ X) (π : X ⟶ S) (d : ℤ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π d, V)) :
    Scheme.Modules.Hom.app (formsDirectImageComparison f π d) V ω =
      relativeDifferentialFormsPullback f π (f ≫ π) (𝟙 S) (by simp) d V ω :=
  rfl

/-- Restricting sections of a module along an inclusion of opens which is an equality is
bijective. -/
theorem bijective_presheaf_map_homOfLE_of_eq {Z : Scheme.{u}} (M : Z.Modules) {U U' : Z.Opens}
    (h : U = U') : Function.Bijective (M.presheaf.map (homOfLE h.le).op) := by
  rw [show homOfLE h.le = eqToHom h from Subsingleton.elim _ _, eqToHom_op]
  exact ConcreteCategory.bijective_of_isIso _

/-- **Pulling back forms along an open immersion is bijective over every open inside its
image.** The canonical map on forms of an open immersion is an isomorphism, the immersion being
étale, and the unit of the pullback adjunction is, up to the identification of the pullback
with the restriction, the restriction of sections to `ι(ι⁻¹W) = W`. -/
theorem bijective_relativeDifferentialFormsPullback_of_isOpenImmersion (ι : Y ⟶ X)
    [IsOpenImmersion ι] (π : X ⟶ S) (d : ℤ) (W : X.Opens) (hW : W ≤ ι.opensRange) :
    Function.Bijective
      (relativeDifferentialFormsPullback ι π (ι ≫ π) (𝟙 S) (by simp) d W) := by
  have hmap : IsIso (relativeDifferentialFormsMap ι π (ι ≫ π) (𝟙 S) (by simp) d) :=
    isIso_relativeDifferentialFormsMap_of_etale ι π (ι ≫ π) (𝟙 S) (by simp) d
  have h1 : Function.Bijective (Scheme.Modules.Hom.app
      (relativeDifferentialFormsMap ι π (ι ≫ π) (𝟙 S) (by simp) d) (ι ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  have hres : Function.Bijective ((relativeDifferentialForms π d).presheaf.map
      (homOfLE (ι.image_preimage_le W)).op) :=
    bijective_presheaf_map_homOfLE_of_eq _ <| by
      rw [ι.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  have he : Function.Bijective (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app
        (relativeDifferentialForms π d)) (ι ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  have hunit : Function.Bijective
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ι (relativeDifferentialForms π d) W) := by
    have hcomp : (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app
        (relativeDifferentialForms π d)) (ι ⁻¹ᵁ W)) ∘
          Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ι (relativeDifferentialForms π d) W =
        (relativeDifferentialForms π d).presheaf.map (homOfLE (ι.image_preimage_le W)).op :=
      funext fun a => Scheme.Modules.restrictFunctorIsoPullback_inv_unit ι _ W a
    exact (Function.Bijective.of_comp_iff' he _).mp (hcomp ▸ hres)
  exact h1.comp hunit

/-- `bijective_relativeDifferentialFormsPullback_of_isOpenImmersion`, for any spelling `π'` of
the structure morphism of the source. -/
theorem bijective_relativeDifferentialFormsPullback_of_isOpenImmersion' (ι : Y ⟶ X)
    [IsOpenImmersion ι] (π : X ⟶ S) (π' : Y ⟶ S) (h : ι ≫ π = π' ≫ 𝟙 S) (d : ℤ)
    (W : X.Opens) (hW : W ≤ ι.opensRange) :
    Function.Bijective (relativeDifferentialFormsPullback ι π π' (𝟙 S) h d W) := by
  obtain rfl : π' = ι ≫ π := by simpa using h.symm
  exact bijective_relativeDifferentialFormsPullback_of_isOpenImmersion ι π d W hW

/-- **Pulling back forms along an isomorphism of schemes is bijective over every open**: it is
the comparison map on direct images of forms along an isomorphism, read on sections, and that
comparison is an isomorphism. -/
theorem bijective_relativeDifferentialFormsPullback_of_isIso (k : Y ⟶ X) [IsIso k]
    (π : X ⟶ S) (π' : Y ⟶ S) (h : k ≫ π = π' ≫ 𝟙 S) (d : ℤ) (W : X.Opens) :
    Function.Bijective (relativeDifferentialFormsPullback k π π' (𝟙 S) h d W) := by
  obtain rfl : π' = k ≫ π := by simpa using h.symm
  have := isIso_formsDirectImageComparison_of_isIso k π d
  exact ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (formsDirectImageComparison k π d) W)

/-- **Over an open `V` above which `f` restricts to an isomorphism, the comparison map
`Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S}` is bijective on sections.** Pulling back along `f` and then along
the inclusion of `f⁻¹V` is pulling back along the inclusion of `V` and then along the
isomorphism `f⁻¹V ≅ V`; the two pullbacks along inclusions are bijective over `V` and `f⁻¹V`, and
so is the pullback along the isomorphism. -/
theorem bijective_formsDirectImageComparison_app_of_isIso_restrict (f : Y ⟶ X) (π : X ⟶ S)
    (d : ℤ) (V : X.Opens) [IsIso (f ∣_ V)] :
    Function.Bijective (Scheme.Modules.Hom.app (formsDirectImageComparison f π d) V) := by
  have hsq : (f ∣_ V) ≫ V.ι = (f ⁻¹ᵁ V).ι ≫ f := morphismRestrict_ι f V
  have hV : ((f ∣_ V) ≫ V.ι) ⁻¹ᵁ V = ((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ V := by rw [hsq]
  set π'' : (f ⁻¹ᵁ V).toScheme ⟶ S := (f ⁻¹ᵁ V).ι ≫ f ≫ π with hπ''
  have h₁ : f ≫ π = (f ≫ π) ≫ 𝟙 S := by simp
  have h₂ : (f ⁻¹ᵁ V).ι ≫ (f ≫ π) = π'' ≫ 𝟙 S := by simp [hπ'']
  have h₃ : ((f ⁻¹ᵁ V).ι ≫ f) ≫ π = π'' ≫ 𝟙 S := by simp [hπ'']
  have g₁ : V.ι ≫ π = (V.ι ≫ π) ≫ 𝟙 S := by simp
  have g₂ : (f ∣_ V) ≫ (V.ι ≫ π) = π'' ≫ 𝟙 S := by
    rw [← Category.assoc, hsq]
    simp [hπ'']
  have g₃ : ((f ∣_ V) ≫ V.ι) ≫ π = π'' ≫ 𝟙 S := by rw [Category.assoc, g₂]
  have key : (relativeDifferentialForms π'' d).presheaf.map (homOfLE hV.le).op ∘
      relativeDifferentialFormsPullback (f ⁻¹ᵁ V).ι (f ≫ π) π'' (𝟙 S) h₂ d (f ⁻¹ᵁ V) ∘
        relativeDifferentialFormsPullback f π (f ≫ π) (𝟙 S) h₁ d V =
      relativeDifferentialFormsPullback (f ∣_ V) (V.ι ≫ π) π'' (𝟙 S) g₂ d (V.ι ⁻¹ᵁ V) ∘
        relativeDifferentialFormsPullback V.ι π (V.ι ≫ π) (𝟙 S) g₁ d V := funext fun ω =>
    (congrArg _ (Stacks.Gysin.relativeDifferentialFormsPullback_comp f (f ⁻¹ᵁ V).ι π (f ≫ π) π''
      (𝟙 S) (𝟙 S) (𝟙 S) h₁ (by simpa using h₂) (by simpa using h₃) d V ω).symm).trans <|
    (Stacks.Gysin.relativeDifferentialFormsPullback_congrMor hsq.symm π π'' (𝟙 S) h₃ g₃ d V
      ω).trans <|
      Stacks.Gysin.relativeDifferentialFormsPullback_comp V.ι (f ∣_ V) π (V.ι ≫ π) π'' (𝟙 S)
        (𝟙 S) (𝟙 S) g₁ (by simpa using g₂) (by simpa using g₃) d V ω
  have hall := (bijective_relativeDifferentialFormsPullback_of_isIso (f ∣_ V) (V.ι ≫ π) π'' g₂ d
    (V.ι ⁻¹ᵁ V)).comp (bijective_relativeDifferentialFormsPullback_of_isOpenImmersion' V.ι π
      (V.ι ≫ π) g₁ d V (by simp))
  rw [← key] at hall
  exact (Function.Bijective.of_comp_iff'
    (bijective_relativeDifferentialFormsPullback_of_isOpenImmersion' (f ⁻¹ᵁ V).ι (f ≫ π) π'' h₂ d
      (f ⁻¹ᵁ V) (by simp)) _).mp
    ((Function.Bijective.of_comp_iff'
      (bijective_presheaf_map_homOfLE_of_eq (relativeDifferentialForms π'' d) hV) _).mp hall)

end AlgebraicGeometry.Scheme.Hom

end
