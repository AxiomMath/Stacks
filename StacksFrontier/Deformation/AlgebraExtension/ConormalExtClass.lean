module

public import StacksFrontier.Algebra.Homology.DoubleProjectionSign
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.Deformation.AlgebraExtension.NaiveCotangentExt

/-!
# The two first `Ext` classes of a map out of `ℐ/ℐ²`, and their naturality

For a presentation `α : ℰ ⟶ 𝒪` of `𝒪` over `𝒜` and a morphism `δ : ℐ/ℐ² ⟶ 𝒢` out of the degree
`-1` term of `NL(α)`, the library has two classes in `Ext¹(NL(α), 𝒢)`:

* `Stacks.SheafOfModules.presentationConormalExtClass`, the chain map `NL(α) ⟶ 𝒢[-1]` which is
  `δ` in degree `-1` — the form in which [Stacks Project, Tag 08UJ] is stated;
* the class `NaiveCotangentTwoTerm.conormalExtClass` of the two-term structure of `NL(α)`,
  the projection `NL(α) ⟶ (ℐ/ℐ²)[1]` followed by `δ[1]` — the form whose vanishing is
  characterised by factoring `δ` through `d`.

They differ by a sign (`CochainComplex.Q_map_doubleToSingleNegOne_comp_shiftIso_inv`). The first
is visibly natural in the presentation: along a morphism of presentations `h : ℰ₁ ⟶ ℰ₂` the
class of `δ` pulls back to the class of `δ` precomposed with the induced map of conormal
sheaves. Hence so is the second.

## Main results

* `Deformation.AlgebraExtension.presentationConormalExtClass_eq_neg`: the sign.
* `Deformation.AlgebraExtension.presentationConormalExtClass_naturality`,
  `Deformation.AlgebraExtension.conormalExtClass_naturality`: naturality in the presentation.

## References

* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpaceThickening (NaiveCotangentTwoTerm)
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence
  presentationNaiveCotangentComplex presentationConormalExtClass presentationConormalMap
  presentationNaiveCotangentComplexMap)

universe t u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The sign**: the chain-map class of `δ` is minus the two-term class of `δ`. -/
theorem presentationConormalExtClass_eq_neg {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ G) :
    presentationConormalExtClass.{u, u, u, t} J A O a E α G δ =
      -(presentationTwoTerm a E α).conormalExtClass G δ :=
  CochainComplex.Q_map_doubleToSingleNegOne_comp_shiftIso_inv _ δ

section Naturality

variable {E₁ E₂ : Cᵒᵖ ⥤ Type u} (h : E₁ ⟶ E₂) {α₁ : E₁ ⟶ underlyingPresheaf J O}
  {α₂ : E₂ ⟶ underlyingPresheaf J O} (hα : h ≫ α₂ = α₁)
  [Presheaf.IsLocallySurjective J (presentation J A O a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A O a E₂ α₂).hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Naturality of the chain-map class in the presentation.** -/
theorem presentationConormalExtClass_naturality
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E₂ α₂).X₁ ⟶ G) :
    DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u} J A E₁ E₂ h O a
        α₁ α₂ hα) ≫ presentationConormalExtClass.{u, u, u, t} J A O a E₂ α₂ G δ =
      presentationConormalExtClass.{u, u, u, t} J A O a E₁ α₁ G
        (presentationConormalMap.{u, u, u, u} J A E₁ E₂ h O a α₁ α₂ hα ≫ δ) := by
  simp only [presentationConormalExtClass]
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.mkHomToSingle_f,
    Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_negOne]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Naturality of the two-term class in the presentation.** -/
theorem conormalExtClass_naturality
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E₂ α₂).X₁ ⟶ G) :
    DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{u, u, u, u} J A E₁ E₂ h O a
        α₁ α₂ hα) ≫ (presentationTwoTerm a E₂ α₂).conormalExtClass G δ =
      (presentationTwoTerm a E₁ α₁).conormalExtClass G
        (presentationConormalMap.{u, u, u, u} J A E₁ E₂ h O a α₁ α₂ hα ≫ δ) := by
  have h1 := presentationConormalExtClass_naturality G h hα δ
  rw [presentationConormalExtClass_eq_neg, presentationConormalExtClass_eq_neg] at h1
  exact neg_inj.1 ((Preadditive.comp_neg _ _).symm.trans h1)

end Naturality

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The two-term class is additive. -/
theorem conormalExtClass_sub {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
    (δ δ' : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ G) :
    (presentationTwoTerm a E α).conormalExtClass G (δ - δ') =
      (presentationTwoTerm a E α).conormalExtClass G δ -
        (presentationTwoTerm a E α).conormalExtClass G δ' :=
  (congrArg ((presentationTwoTerm a E α).proj ≫ ·)
    ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).map_sub)).trans
    (Preadditive.comp_sub _ _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The two-term class commutes with negation. -/
theorem conormalExtClass_neg {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ G) :
    (presentationTwoTerm a E α).conormalExtClass G (-δ) =
      -(presentationTwoTerm a E α).conormalExtClass G δ :=
  (congrArg ((presentationTwoTerm a E α).proj ≫ ·)
    ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).map_neg)).trans
    (Preadditive.comp_neg _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Two morphisms out of `ℐ/ℐ²` with the same two-term class differ by `θ ∘ d`. -/
theorem exists_d_comp_eq_sub_of_conormalExtClass_eq {E : Cᵒᵖ ⥤ Type u}
    {α : E ⟶ underlyingPresheaf J O} [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
    {δ δ' : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ G}
    (h : (presentationTwoTerm a E α).conormalExtClass G δ =
      (presentationTwoTerm a E α).conormalExtClass G δ') :
    ∃ θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ G,
      (presentationConormalSequence.{u, u, u, u} J A O a E α).f ≫ θ = δ - δ' :=
  ((presentationTwoTerm a E α).conormalExtClass_eq_zero_iff G (δ - δ')).1
    ((conormalExtClass_sub G δ δ').trans ((congrArg (_ - ·) h.symm).trans (sub_self _)))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The two-term class is natural in the module. -/
theorem conormalExtClass_comp {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
    [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom] {G' : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ G) (g : G ⟶ G') :
    (presentationTwoTerm a E α).conormalExtClass G δ ≫
        ((DerivedCategory.singleFunctor _ 0).map g)⟦(1 : ℤ)⟧' =
      (presentationTwoTerm a E α).conormalExtClass G' (δ ≫ g) :=
  (Category.assoc _ _ _).trans (congrArg ((presentationTwoTerm a E α).proj ≫ ·)
    (((shiftFunctor _ (1 : ℤ)).map_comp _ _).symm.trans
      (congrArg (shiftFunctor _ (1 : ℤ)).map
        ((DerivedCategory.singleFunctor _ 0).map_comp _ _).symm)))

end Deformation.AlgebraExtension

end
