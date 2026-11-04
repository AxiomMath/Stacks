module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Contracting an exceptional curve in a nodal relative curve: the basic facts

Let `E ⊆ X` be an exceptional curve of the first kind, presented by its ideal sheaf `D` and an
isomorphism `e : 𝐏¹_k ≅ E`, and let `b : X ⟶ X'` be a contraction of `E` in the sense of
`AlgebraicGeometry.IsContractionOfExceptionalCurve`. This file proves elementary properties of
such a contraction.

## Main results

* `AlgebraicGeometry.const_of_isField_sections`: a morphism from a scheme whose global functions
  form a field to an affine scheme is constant on points.
* `AlgebraicGeometry.exists_const_on_exceptionalCurve`: a morphism to an affine scheme carries an
  exceptional curve of the first kind to a single point.
* `AlgebraicGeometry.exists_factor_of_contraction`: a morphism to an affine scheme factors
  uniquely through a contraction.
* `AlgebraicGeometry.nodal_on_compl_centre`: away from the contracted point the base morphism is
  at-worst-nodal of relative dimension one.
* `AlgebraicGeometry.isIntegral_subscheme_of_iso_projectiveLineProj`: an exceptional curve of the
  first kind is integral.
* `AlgebraicGeometry.surjective_of_isContractionOfExceptionalCurve`: a contraction is surjective.
* `AlgebraicGeometry.isIso_appTop_of_isContractionOfExceptionalCurve`: a contraction induces an
  isomorphism on global functions.

## References

* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism from a scheme whose global functions form a field to an affine scheme is constant
on points. -/
public theorem const_of_isField_sections {Z : Scheme.{u}} (hZ : IsField Γ(Z, ⊤))
    {A : Type u} [CommRing A] (g : Z ⟶ Spec (.of A)) (x y : Z) : g x = g y := by
  let : Field Γ(Z, ⊤) := hZ.toField
  have hg : g = (Z.toSpecΓ ≫ Spec.map g.appTop) ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
    rw [← Scheme.toSpecΓ_naturality, Category.assoc,
      AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [hg]
  show (Spec.map _ ≫ Spec.map _) (Z.toSpecΓ x) = (Spec.map _ ≫ Spec.map _) (Z.toSpecΓ y)
  exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum Γ(Z, ⊤)) _ _)

/-- An exceptional curve of the first kind is carried to a single point by any morphism to an
affine scheme. -/
public theorem exists_const_on_exceptionalCurve {X : Scheme.{u}} (D : X.IdealSheafData)
    (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    {A : Type u} [CommRing A] [Nonempty (Spec (CommRingCat.of A))]
    (f : X ⟶ Spec (.of A)) :
    ∃ y : Spec (CommRingCat.of A), ∀ d : D.subscheme, f (D.subschemeι d) = y := by
  rcases isEmpty_or_nonempty D.subscheme with hemp | hne
  · exact ⟨Classical.arbitrary _, fun d => (hemp.false d).elim⟩
  · obtain ⟨d₀⟩ := hne
    exact ⟨f (D.subschemeι d₀), fun d => const_of_isField_sections
      (Scheme.IdealSheafData.isField_sections_subscheme_of_iso_projectiveLineProj D k e)
      (D.subschemeι ≫ f) d d₀⟩

/-- A morphism from `X` to the spectrum of a nontrivial ring factors uniquely through the
contraction of an exceptional curve of the first kind in `X`. -/
public theorem exists_factor_of_contraction {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    {A : Type u} [CommRing A] [Nontrivial A] (f : X ⟶ Spec (.of A)) :
    ∃! f' : X' ⟶ Spec (.of A), b ≫ f' = f := by
  have : Nonempty (Spec (CommRingCat.of A)) :=
    ⟨⟨(Ideal.exists_maximal A).choose, (Ideal.exists_maximal A).choose_spec.isPrime⟩⟩
  exact existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b hb f
    (exists_const_on_exceptionalCurve D k e f)

/-- Let `b : X ⟶ X'` be, up to the isomorphism `ε`, the blow-up of `X'` at the closed point `z`.
If `b ≫ f'` is at worst nodal of relative dimension one, then so is the restriction of `f'` to the
complement of `z`. -/
public theorem nodal_on_compl_centre {X X' S : Scheme.{u}} (D : X.IdealSheafData)
    (b : X ⟶ X') (z : X') (hz : IsClosed ({z} : Set X'))
    (ε : X ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')))
    (hε : ε.hom ≫ blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')) = b)
    (f' : X' ⟶ S) (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f')) :
    IsAtWorstNodalOfRelativeDimensionOne
      (Scheme.Opens.ι (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens) ≫ f') := by
  have : MorphismProperty.RespectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let W : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
  show IsAtWorstNodalOfRelativeDimensionOne (W.ι ≫ f')
  have hoff : IsIso (b ∣_ W) :=
    isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ε hε
  have hres : IsAtWorstNodalOfRelativeDimensionOne ((b ∣_ W) ≫ W.ι ≫ f') := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    exact isAtWorstNodalOfRelativeDimensionOne_comp_etale (b ≫ f') (b ⁻¹ᵁ W).ι hf
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@IsAtWorstNodalOfRelativeDimensionOne.{u}) (b ∣_ W) (W.ι ≫ f')).mp hres

/-- An exceptional curve of the first kind is an integral scheme. -/
@[ega "II 7.4.14" "more general"]
public theorem isIntegral_subscheme_of_iso_projectiveLineProj {X : Scheme.{u}}
    (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme) : IsIntegral D.subscheme := by
  have : IsIntegral (projectiveLineProj k) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj k 1
  exact IsIntegral.of_isIso e.hom

/-- A contraction of an exceptional curve of the first kind is surjective. -/
public theorem surjective_of_isContractionOfExceptionalCurve {X X' : Scheme.{u}}
    (D : X.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b) :
    Function.Surjective b.base := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨z, hz, -, -, hD, ε, hε⟩ := hb.exists_blowUp_iso
  let W : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
  have hoff : IsIso (b ∣_ W) :=
    isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ε hε
  intro y
  by_cases hy : y = z
  · subst hy
    obtain ⟨d⟩ : Nonempty D.subscheme := inferInstance
    exact ⟨D.subschemeι d, IsContractionOfExceptionalCurve.eq_centre_of_mem_support hD
      (by rw [← D.range_subschemeι]; exact ⟨d, rfl⟩)⟩
  · have hyW : y ∈ W := hy
    obtain ⟨x, hx⟩ := (asIso (b ∣_ W)).hom.homeomorph.surjective ⟨y, hyW⟩
    refine ⟨(b ⁻¹ᵁ W).ι x, ?_⟩
    have : ((b ∣_ W) ≫ W.ι) x = y := congrArg (fun t : W => (t : X')) hx
    rwa [morphismRestrict_ι] at this

/-- The comparison map of global functions along a contraction is an isomorphism. -/
public theorem isIso_appTop_of_isContractionOfExceptionalCurve {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) :
    IsIso b.appTop := by
  have : IsIso b.c := hb.isIso_c
  exact CategoryTheory.NatIso.isIso_app_of_isIso (α := b.c) (op ⊤)

end AlgebraicGeometry

end
