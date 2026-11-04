module

public import StacksFrontier.Deformation.AlgebraExtension.ExtClass
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare

/-!
# The class of an extension of algebras under restriction of the base

Let `g : 𝒜₀ ⟶ 𝒜` and `a : 𝒜 ⟶ 𝒪` be morphisms of sheaves of commutative rings on a small site,
and let `0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` be an extension of `𝒜`-algebras. Read through `g`, it is an
extension of `𝒜₀`-algebras. Its class in `Ext¹(NL_{𝒪/𝒜₀}, ℳ)` (Stacks 0GQ5) is the pullback of
the class in `Ext¹(NL_{𝒪/𝒜}, ℳ)` along the change of base ring `NL_{𝒪/𝒜₀} ⟶ NL_{𝒪/𝒜}` of
Stacks 08TX.

This is one of the identities behind condition (iv) of [Stacks, Tag 07YY] for deformations of an
algebraic space, as in [Stacks, Remark 0D1P]. Over a short exact sequence of thickenings, the
square `(h₂)` compares the class of a lift read over `A₃'` with the tangent class of its
restriction to `A₁' = A[I₁]`. That restriction is an extension of `A`-algebras which, read over
`A₃'`, is the pushout of the lift.

## Main definitions

* `Deformation.AlgebraExtension.restrictAlong`: an extension of `𝒜`-algebras, read as an
  extension of `𝒜₀`-algebras.
* `Deformation.AlgebraExtension.presentationBaseChangeMap`: for a family of generators
  `α : ℰ ⟶ 𝒪`, the chain map `NL_{𝒜₀}(α) ⟶ NL_𝒜(α)` induced by `𝒜₀[ℰ] ⟶ 𝒜[ℰ]`.

## Main results

* `Deformation.AlgebraExtension.extClass_restrictAlong`: the class of the restricted extension.

## References

* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence
  presentationNaiveCotangentComplex naiveCotangentComplex naiveCotangentComplexComparison
  presentationConormalExtClass freeAlgebraMapOfSquare)
open Stacks.Sites.Conormal (conormalSheafMapOfSquare tensorSheafMapOfSquare)

universe t u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  {A₀ A O : Sheaf J CommRingCat.{u}} (g : A₀ ⟶ A) {a : A ⟶ O}
  {M : SheafOfModules.{u} (underlyingRingSheaf O)}

/-- **An extension of `𝒜`-algebras, read as an extension of `𝒜₀`-algebras** through
`g : 𝒜₀ ⟶ 𝒜`. -/
public def restrictAlong (P : AlgebraExtension a M) : AlgebraExtension (g ≫ a) M where
  extension := P.extension
  reduction := P.reduction
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  algebraMap := g ≫ P.algebraMap
  algebraMap_reduction := by rw [Category.assoc, P.algebraMap_reduction]
  kernelInclusion := P.kernelInclusion
  kernelZero := P.kernelZero
  kernelUniversal := P.kernelUniversal

/-! ### The change of base on a presentation -/

section Presentation

variable (E : Cᵒᵖ ⥤ Type u) (α : E ⟶ underlyingPresheaf J O)

/-- The morphism `𝒜₀[ℰ] ⟶ 𝒜[ℰ]` which is `g` on coefficients and the identity on variables. -/
public abbrev baseChangeFreeMap : freeAlgebraSheaf J A₀ E ⟶ freeAlgebraSheaf J A E :=
  freeAlgebraMapOfSquare J A₀ A E E g (𝟙 E)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- On coefficients, `𝒜₀[ℰ] ⟶ 𝒜[ℰ]` is `g`. -/
public theorem coefficientMap_comp_baseChangeFreeMap :
    g ≫ freeAlgebraSheafCoefficientMap J A E =
      freeAlgebraSheafCoefficientMap J A₀ E ≫ baseChangeFreeMap g E :=
  (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare
    J A₀ A E E g (𝟙 E)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `𝒜₀[ℰ] ⟶ 𝒜[ℰ]` lies over the two presentations of `𝒪`. -/
public theorem baseChangeFreeMap_comp_presentation :
    baseChangeFreeMap g E ≫ presentation J A O a E α =
      presentation J A₀ O (g ≫ a) E α ≫ 𝟙 O := by
  rw [Category.comp_id]
  refine freeAlgebraSheaf_hom_ext J A₀ O E ?_ ?_
  · rw [← Category.assoc, ← coefficientMap_comp_baseChangeFreeMap, Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc, freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare,
      Category.id_comp, freeAlgebraSheafVariable_comp_desc, freeAlgebraSheafVariable_comp_desc]

variable [Presheaf.IsLocallySurjective J (presentation J A₀ O (g ≫ a) E α).hom]
  [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]

/-- The map of conormal sheaves `ℐ₀/ℐ₀² ⟶ ℐ/ℐ²` of the change of base on a presentation. -/
public abbrev presentationBaseConormalMap :
    (presentationConormalSequence.{u, u, u, u} J A₀ O (g ≫ a) E α).X₁ ⟶
      (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ :=
  conormalSheafMapOfSquare.{u, u, u, u} J _ _ O O (presentation J A₀ O (g ≫ a) E α)
    (presentation J A O a E α) (baseChangeFreeMap g E) (𝟙 O)
    (baseChangeFreeMap_comp_presentation g E α)

/-- The map of scalar extensions of differentials of the change of base on a presentation. -/
public abbrev presentationBaseTensorMap :
    (presentationConormalSequence.{u, u, u, u} J A₀ O (g ≫ a) E α).X₂ ⟶
      (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ :=
  tensorSheafMapOfSquare.{u, u, u, u} J A₀ A _ _ O O (freeAlgebraSheafCoefficientMap J A₀ E)
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A₀ O (g ≫ a) E α)
    (presentation J A O a E α) (baseChangeFreeMap g E) (𝟙 O) g
    (baseChangeFreeMap_comp_presentation g E α) (coefficientMap_comp_baseChangeFreeMap g E)

/-- The components in degrees `-1` and `0` of the change of base on a presentation commute with
the differentials `ℐ₀/ℐ₀² ⟶ 𝒪 ⊗ Ω` and `NL_𝒜(α)⁻¹ ⟶ NL_𝒜(α)⁰`. -/
public theorem presentationBaseConormalMap_comm :
    (presentationBaseConormalMap g E α ≫
        eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne J A O a E
          α).symm) ≫
      (presentationNaiveCotangentComplex.{u, u, u, u} J A O a E α).d (-1) 0 =
    (presentationConormalSequence.{u, u, u, u} J A₀ O (g ≫ a) E α).f ≫
      (presentationBaseTensorMap g E α ≫
        eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero J A O a E
          α).symm) := by
  rw [Stacks.SheafOfModules.presentationNaiveCotangentComplex_d_negOne_zero]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ eqToHom
      (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero J A O a E α).symm)
    (Stacks.Sites.Conormal.conormalSequence_f_naturality_square.{u, u, u, u} J A₀ A _ _ O O
      (freeAlgebraSheafCoefficientMap J A₀ E) (freeAlgebraSheafCoefficientMap J A E)
      (presentation J A₀ O (g ≫ a) E α) (presentation J A O a E α) (baseChangeFreeMap g E)
      (𝟙 O) g (baseChangeFreeMap_comp_presentation g E α)
      (coefficientMap_comp_baseChangeFreeMap g E)).symm

/-- The component in degree `0` of the change of base on a presentation, followed by a
differential of `NL_𝒜(α)` out of degree `0`, is zero. -/
public theorem presentationBaseTensorMap_comp_d (k : ℤ) :
    (presentationBaseTensorMap g E α ≫
        eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero J A O a E
          α).symm) ≫ (presentationNaiveCotangentComplex.{u, u, u, u} J A O a E α).d 0 k = 0 := by
  rw [Stacks.SheafOfModules.presentationNaiveCotangentComplex_d_zero, comp_zero]

/-- **The change of base on a presentation**: the chain map `NL_{𝒜₀}(α) ⟶ NL_𝒜(α)` induced by
`𝒜₀[ℰ] ⟶ 𝒜[ℰ]`. -/
public def presentationBaseChangeMap :
    presentationNaiveCotangentComplex.{u, u, u, u} J A₀ O (g ≫ a) E α ⟶
      presentationNaiveCotangentComplex.{u, u, u, u} J A O a E α := by
  have : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (presentationBaseConormalMap g E α ≫
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne J A O a E α).symm)
    (presentationBaseTensorMap g E α ≫
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero J A O a E α).symm)
    (presentationBaseConormalMap_comm g E α)
    (fun k _ ↦ by
      rw [Stacks.SheafOfModules.presentationNaiveCotangentComplex_d_zero, comp_zero])

/-- In degree `-1`, the change of base on a presentation is the map of conormal sheaves
`ℐ₀/ℐ₀² ⟶ ℐ/ℐ²`, up to the identifications of the terms of the complexes. -/
public theorem presentationBaseChangeMap_f_negOne :
    (presentationBaseChangeMap g E α).f (-1) =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne J A₀ O (g ≫ a)
          E α) ≫
        presentationBaseConormalMap g E α ≫
        eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne J A O a E
          α).symm := by
  have : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    hasZeroObject_of_hasTerminal_object
  have h₀ : (HomologicalComplex.doubleXIso₀
      (presentationConormalSequence.{u, u, u, u} J A₀ O (g ≫ a) E α).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne J A₀ O (g ≫ a)
        E α) := by
    simp only [HomologicalComplex.doubleXIso₀]
    congr 1
  rw [← h₀]
  exact HomologicalComplex.mkHomFromDouble_f₀
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (presentationBaseConormalMap_comm g E α) (fun k _ ↦ presentationBaseTensorMap_comp_d g E α k)

/-- In degree `0`, the change of base on a presentation is the map of scalar extensions of
differentials, up to the identifications of the terms of the complexes. -/
public theorem presentationBaseChangeMap_f_zero :
    (presentationBaseChangeMap g E α).f 0 =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero J A₀ O (g ≫ a) E
          α) ≫
        presentationBaseTensorMap g E α ≫
        eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero J A O a E
          α).symm := by
  have : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    hasZeroObject_of_hasTerminal_object
  have h₁ : (HomologicalComplex.doubleXIso₁
      (presentationConormalSequence.{u, u, u, u} J A₀ O (g ≫ a) E α).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      eqToHom (Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero J A₀ O (g ≫ a)
        E α) := by
    simp only [HomologicalComplex.doubleXIso₁]
    congr 1
  rw [← h₁]
  exact HomologicalComplex.mkHomFromDouble_f₁
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (presentationBaseConormalMap_comm g E α) (fun k _ ↦ presentationBaseTensorMap_comp_d g E α k)

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- **The chain-map class is natural in the change of base**: pulling back the class of `δ`
along `NL_{𝒜₀}(α) ⟶ NL_𝒜(α)` is the class of `δ` precomposed with the map of conormal
sheaves. -/
public theorem presentationConormalExtClass_baseChange
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ G) :
    DerivedCategory.Q.map (presentationBaseChangeMap g E α) ≫
        presentationConormalExtClass.{u, u, u, t} J A O a E α G δ =
      presentationConormalExtClass.{u, u, u, t} J A₀ O (g ≫ a) E α G
        (presentationBaseConormalMap g E α ≫ δ) := by
  simp only [presentationConormalExtClass]
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.mkHomToSingle_f, presentationBaseChangeMap_f_negOne]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **The two-term class is natural in the change of base.** -/
public theorem conormalExtClass_baseChange
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ G) :
    DerivedCategory.Q.map (presentationBaseChangeMap g E α) ≫
        (presentationTwoTerm a E α).conormalExtClass G δ =
      (presentationTwoTerm (g ≫ a) E α).conormalExtClass G
        (presentationBaseConormalMap g E α ≫ δ) := by
  have h1 := presentationConormalExtClass_baseChange g E α G δ
  rw [presentationConormalExtClass_eq_neg, presentationConormalExtClass_eq_neg] at h1
  exact neg_inj.1 ((Preadditive.comp_neg _ _).symm.trans h1)

end Presentation

/-! ### Compatibility with morphisms of presentations -/

section Naturality

variable {E₁ E₂ : Cᵒᵖ ⥤ Type u} (h : E₁ ⟶ E₂) {α₁ : E₁ ⟶ underlyingPresheaf J O}
  {α₂ : E₂ ⟶ underlyingPresheaf J O} (hα : h ≫ α₂ = α₁)
  [Presheaf.IsLocallySurjective J (presentation J A₀ O (g ≫ a) E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A O a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A₀ O (g ≫ a) E₂ α₂).hom]
  [Presheaf.IsLocallySurjective J (presentation J A O a E₂ α₂).hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The two ways from `𝒜₀[ℰ₁]` to `𝒜[ℰ₂]`, through `𝒜[ℰ₁]` and through `𝒜₀[ℰ₂]`, agree. -/
public theorem baseChangeFreeMap_comp_freeAlgebraMap :
    baseChangeFreeMap g E₁ ≫ Stacks.SheafOfModules.freeAlgebraMap J A E₁ E₂ h =
      Stacks.SheafOfModules.freeAlgebraMap J A₀ E₁ E₂ h ≫ baseChangeFreeMap g E₂ := by
  refine freeAlgebraSheaf_hom_ext J A₀ _ E₁ ?_ ?_
  · rw [← Category.assoc, ← coefficientMap_comp_baseChangeFreeMap, Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap, ← Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
      coefficientMap_comp_baseChangeFreeMap]
  · rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare, Category.id_comp,
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMap,
      CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMap, Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare, Category.id_comp]

/-- **Degree `-1`.** -/
@[reassoc]
public theorem presentationBaseConormalMap_naturality :
    presentationBaseConormalMap g E₁ α₁ ≫
        Stacks.SheafOfModules.presentationConormalMap J A E₁ E₂ h O a α₁ α₂ hα =
      Stacks.SheafOfModules.presentationConormalMap J A₀ E₁ E₂ h O (g ≫ a) α₁ α₂ hα ≫
        presentationBaseConormalMap g E₂ α₂ := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ fun X x => ?_
  have key := congrArg (fun m => m.hom.app X x.1) (baseChangeFreeMap_comp_freeAlgebraMap g h)
  have e1 := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass J A₀ A
    (freeAlgebraSheaf J A₀ E₁) (freeAlgebraSheaf J A E₁) O O
    (freeAlgebraSheafCoefficientMap J A₀ E₁) (freeAlgebraSheafCoefficientMap J A E₁)
    (presentation J A₀ O (g ≫ a) E₁ α₁) (presentation J A O a E₁ α₁) (baseChangeFreeMap g E₁)
    (𝟙 O) (baseChangeFreeMap_comp_presentation g E₁ α₁) X x
  have e2 := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass J A O
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
    (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A O a E₁ α₁) (presentation J A O a E₂ α₂)
    (Stacks.SheafOfModules.freeAlgebraMap J A E₁ E₂ h)
    (Stacks.SheafOfModules.freeAlgebraMap_comp_presentation J A E₁ E₂ h O a α₁ α₂ hα) X
    ⟨(baseChangeFreeMap g E₁).hom.app X x.1, Stacks.Sites.Conormal.kernelIdeal_le_comap_square
      (presentation J A₀ O (g ≫ a) E₁ α₁).hom (presentation J A O a E₁ α₁).hom
      (baseChangeFreeMap g E₁).hom (𝟙 O : O ⟶ O).hom
      (Stacks.Sites.Conormal.hom_of_square (baseChangeFreeMap_comp_presentation g E₁ α₁)) X x.2⟩
  have e3 := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass J A₀ O
    (freeAlgebraSheaf J A₀ E₁) (freeAlgebraSheaf J A₀ E₂)
    (freeAlgebraSheafCoefficientMap J A₀ E₁) (freeAlgebraSheafCoefficientMap J A₀ E₂)
    (presentation J A₀ O (g ≫ a) E₁ α₁) (presentation J A₀ O (g ≫ a) E₂ α₂)
    (Stacks.SheafOfModules.freeAlgebraMap J A₀ E₁ E₂ h)
    (Stacks.SheafOfModules.freeAlgebraMap_comp_presentation J A₀ E₁ E₂ h O (g ≫ a) α₁ α₂ hα) X x
  have e4 := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass J A₀ A
    (freeAlgebraSheaf J A₀ E₂) (freeAlgebraSheaf J A E₂) O O
    (freeAlgebraSheafCoefficientMap J A₀ E₂) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A₀ O (g ≫ a) E₂ α₂) (presentation J A O a E₂ α₂) (baseChangeFreeMap g E₂)
    (𝟙 O) (baseChangeFreeMap_comp_presentation g E₂ α₂) X
    ⟨(Stacks.SheafOfModules.freeAlgebraMap J A₀ E₁ E₂ h).hom.app X x.1,
      Stacks.Sites.Conormal.kernelIdeal_le_comap (presentation J A₀ O (g ≫ a) E₁ α₁).hom
        (presentation J A₀ O (g ≫ a) E₂ α₂).hom
        (Stacks.SheafOfModules.freeAlgebraMap J A₀ E₁ E₂ h).hom
        (Stacks.Sites.Conormal.hom_of_comp_eq
          (Stacks.SheafOfModules.freeAlgebraMap_comp_presentation J A₀ E₁ E₂ h O (g ≫ a) α₁ α₂
            hα)) X x.2⟩
  refine ((congrArg _ e1).trans e2).trans (Eq.trans ?_ ((congrArg _ e3).trans e4).symm)
  congr 1
  exact Subtype.ext key

/-- **Degree `0`.** -/
@[reassoc]
public theorem presentationBaseTensorMap_naturality :
    presentationBaseTensorMap g E₁ α₁ ≫
        Stacks.SheafOfModules.presentationTensorMap J A E₁ E₂ h O a α₁ α₂ hα =
      Stacks.SheafOfModules.presentationTensorMap J A₀ E₁ E₂ h O (g ≫ a) α₁ α₂ hα ≫
        presentationBaseTensorMap g E₂ α₂ := by
  have hsq : ∀ (A' : Sheaf J CommRingCat.{u}) (a' : A' ⟶ O),
      Stacks.SheafOfModules.freeAlgebraMap J A' E₁ E₂ h ≫ presentation J A' O a' E₂ α₂ =
        presentation J A' O a' E₁ α₁ ≫ 𝟙 O := fun A' a' ↦ by
    rw [Category.comp_id]
    exact Stacks.SheafOfModules.freeAlgebraMap_comp_presentation J A' E₁ E₂ h O a' α₁ α₂ hα
  have ha : ∀ A' : Sheaf J CommRingCat.{u}, 𝟙 A' ≫ freeAlgebraSheafCoefficientMap J A' E₂ =
      freeAlgebraSheafCoefficientMap J A' E₁ ≫ Stacks.SheafOfModules.freeAlgebraMap J A' E₁ E₂ h :=
    fun A' ↦ by
      rw [Category.id_comp]
      exact (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A' E₁ E₂
        h).symm
  have hL := Stacks.Sites.Conormal.tensorSheafMapOfSquare_comp J A₀ A A (freeAlgebraSheaf J A₀ E₁)
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂) O O O
    (freeAlgebraSheafCoefficientMap J A₀ E₁) (freeAlgebraSheafCoefficientMap J A E₁)
    (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A₀ O (g ≫ a) E₁ α₁)
    (presentation J A O a E₁ α₁) (presentation J A O a E₂ α₂) (baseChangeFreeMap g E₁)
    (Stacks.SheafOfModules.freeAlgebraMap J A E₁ E₂ h) (𝟙 O) (𝟙 O) g (𝟙 A)
    (baseChangeFreeMap_comp_presentation g E₁ α₁) (hsq A _)
    (coefficientMap_comp_baseChangeFreeMap g E₁) (ha A)
  have hR := Stacks.Sites.Conormal.tensorSheafMapOfSquare_comp J A₀ A₀ A (freeAlgebraSheaf J A₀ E₁)
    (freeAlgebraSheaf J A₀ E₂) (freeAlgebraSheaf J A E₂) O O O
    (freeAlgebraSheafCoefficientMap J A₀ E₁) (freeAlgebraSheafCoefficientMap J A₀ E₂)
    (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A₀ O (g ≫ a) E₁ α₁)
    (presentation J A₀ O (g ≫ a) E₂ α₂) (presentation J A O a E₂ α₂)
    (Stacks.SheafOfModules.freeAlgebraMap J A₀ E₁ E₂ h) (baseChangeFreeMap g E₂) (𝟙 O) (𝟙 O)
    (𝟙 A₀) g (hsq A₀ _) (baseChangeFreeMap_comp_presentation g E₂ α₂) (ha A₀)
    (coefficientMap_comp_baseChangeFreeMap g E₂)
  have hC := Stacks.Sites.Conormal.tensorSheafMapOfSquare_congr J A₀ A (freeAlgebraSheaf J A₀ E₁)
    (freeAlgebraSheaf J A E₂) O O (freeAlgebraSheafCoefficientMap J A₀ E₁)
    (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A₀ O (g ≫ a) E₁ α₁)
    (presentation J A O a E₂ α₂) (𝟙 O ≫ 𝟙 O)
    (Stacks.Sites.Conormal.square_comp (baseChangeFreeMap_comp_presentation g E₁ α₁) (hsq A _))
    (Stacks.Sites.Conormal.square_comp (coefficientMap_comp_baseChangeFreeMap g E₁) (ha A))
    (Stacks.Sites.Conormal.square_comp (hsq A₀ _) (baseChangeFreeMap_comp_presentation g E₂ α₂))
    (Stacks.Sites.Conormal.square_comp (ha A₀) (coefficientMap_comp_baseChangeFreeMap g E₂))
    (baseChangeFreeMap_comp_freeAlgebraMap g h) (by rw [Category.comp_id, Category.id_comp])
  exact hL.trans (hC.trans hR.symm)

/-- **The change of base is natural in the presentation.** -/
public theorem presentationBaseChangeMap_naturality :
    presentationBaseChangeMap g E₁ α₁ ≫
        Stacks.SheafOfModules.presentationNaiveCotangentComplexMap J A E₁ E₂ h O a α₁ α₂ hα =
      Stacks.SheafOfModules.presentationNaiveCotangentComplexMap J A₀ E₁ E₂ h O (g ≫ a) α₁ α₂
          hα ≫ presentationBaseChangeMap g E₂ α₂ := by
  have : HasZeroObject
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    hasZeroObject_of_hasTerminal_object
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1 : i = -1
  · subst h1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, presentationBaseChangeMap_f_negOne,
      presentationBaseChangeMap_f_negOne,
      Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_negOne,
      Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_negOne]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [presentationBaseConormalMap_naturality_assoc]
  by_cases h0 : i = 0
  · subst h0
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, presentationBaseChangeMap_f_zero,
      presentationBaseChangeMap_f_zero,
      Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_zero,
      Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_zero]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [presentationBaseTensorMap_naturality_assoc]
  exact (Stacks.SheafOfModules.presentationNaiveCotangentComplex_isZero_X J A₀ O (g ≫ a) E₁ α₁
    i h1 h0).eq_of_src _ _

end Naturality

/-! ### The class of the restricted extension -/

section ExtClass

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O} {P : AlgebraExtension a M}

/-- A lift of generators to an extension of `𝒜`-algebras is a lift to the restricted
extension. -/
public def GeneratorLift.restrictAlong (β : GeneratorLift α P) :
    GeneratorLift α (P.restrictAlong g) :=
  ⟨β.lift, β.lift_comp⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))] in
/-- The homomorphism `𝒜₀[ℰ] ⟶ 𝒪'` of the restricted lift factors through `𝒜₀[ℰ] ⟶ 𝒜[ℰ]`. -/
public theorem GeneratorLift.hom_restrictAlong (β : GeneratorLift α P) :
    (β.restrictAlong g).hom = baseChangeFreeMap g E ≫ β.hom := by
  refine freeAlgebraSheaf_hom_ext J A₀ P.extension E ?_ ?_
  · have h : g ≫ P.algebraMap =
        freeAlgebraSheafCoefficientMap J A₀ E ≫ baseChangeFreeMap g E ≫ β.hom := by
      rw [← Category.assoc, ← coefficientMap_comp_baseChangeFreeMap, Category.assoc,
        β.coefficientMap_hom]
    exact (GeneratorLift.coefficientMap_hom (β.restrictAlong g)).trans h
  · have h : freeAlgebraSheafVariable J A₀ E ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{u}).map (baseChangeFreeMap g E ≫ β.hom))
          (forget CommRingCat.{u}) = β.lift := by
      rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
        Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare,
        Category.id_comp, β.variable_hom]
    exact (GeneratorLift.variable_hom (β.restrictAlong g)).trans h.symm

variable [Presheaf.IsLocallySurjective J (presentation J A₀ O (g ≫ a) E α).hom]
  [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))] in
/-- **The conormal map of the restricted lift** is that of the lift, precomposed with the map
`ℐ₀/ℐ₀² ⟶ ℐ/ℐ²` of the change of base. -/
public theorem GeneratorLift.conormalHom_restrictAlong (β : GeneratorLift α P) :
    (β.restrictAlong g).conormalHom = presentationBaseConormalMap g E α ≫ β.conormalHom := by
  refine GeneratorLift.conormal_ext fun U x => ?_
  rw [GeneratorLift.conormalHom_relClass]
  have e := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass J A₀ A
    (freeAlgebraSheaf J A₀ E) (freeAlgebraSheaf J A E) O O
    (freeAlgebraSheafCoefficientMap J A₀ E) (freeAlgebraSheafCoefficientMap J A E)
    (presentation J A₀ O (g ≫ a) E α) (presentation J A O a E α) (baseChangeFreeMap g E) (𝟙 O)
    (baseChangeFreeMap_comp_presentation g E α) U x
  refine Eq.trans ?_ (congrArg (β.conormalHom.val.app U) e).symm
  refine Eq.trans ?_ (β.conormalHom_relClass U _).symm
  refine P.incl_injective ?_
  refine ((β.restrictAlong g).incl_restriction U x).trans ?_
  refine Eq.trans ?_ (β.incl_restriction U _).symm
  rw [GeneratorLift.hom_restrictAlong]
  rfl

omit [J.HasSheafCompose (forget CommRingCat.{u})] [(forget CommRingCat.{u}).ReflectsIsomorphisms] in
/-- **The class of the restricted extension** (Stacks 0GQ5 and 08TX): the class in
`Ext¹(NL_{𝒪/𝒜₀}, ℳ)` of an extension of `𝒜`-algebras read over `𝒜₀` is its class in
`Ext¹(NL_{𝒪/𝒜}, ℳ)` pulled back along the change of base ring `NL_{𝒪/𝒜₀} ⟶ NL_{𝒪/𝒜}`. -/
public theorem extClass_restrictAlong (P : AlgebraExtension a M) :
    extClass (P.restrictAlong g) =
      DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{u, u, u, u}
        J A₀ O (g ≫ a) A a g rfl) ≫ extClass P := by
  have := isLocallySurjective_fibreMap P P
  rw [extClass_eq_of_lift ((fibreFst P P).restrictAlong g), extClass, liftClass, liftClass,
    GeneratorLift.conormalHom_restrictAlong]
  refine (congrArg (_ ≫ ·) (conormalExtClass_baseChange g _ _ _ _).symm).trans ?_
  have key : (presentationTwoTermIso (g ≫ a) (fibreGenerators P P) (fibreMap P P)).inv ≫
      DerivedCategory.Q.map (presentationBaseChangeMap g (fibreGenerators P P) (fibreMap P P)) =
    DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{u, u, u, u}
        J A₀ O (g ≫ a) A a g rfl) ≫
      (presentationTwoTermIso a (fibreGenerators P P) (fibreMap P P)).inv := by
    have H : DerivedCategory.Q.map (presentationBaseChangeMap g (fibreGenerators P P)
          (fibreMap P P)) ≫ (presentationTwoTermIso a (fibreGenerators P P) (fibreMap P P)).hom =
        (presentationTwoTermIso (g ≫ a) (fibreGenerators P P) (fibreMap P P)).hom ≫
          DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{u, u, u, u}
            J A₀ O (g ≫ a) A a g rfl) :=
      (Functor.map_comp DerivedCategory.Q _ _).symm.trans
        ((congrArg DerivedCategory.Q.map
          (presentationBaseChangeMap_naturality g (fibreMap P P) (Category.comp_id _))).trans
          (Functor.map_comp DerivedCategory.Q _ _))
    exact (Iso.eq_comp_inv _).mpr ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) H).trans (Iso.inv_hom_id_assoc _ _)))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫
    (presentationTwoTerm a (fibreGenerators P P) (fibreMap P P)).conormalExtClass (tensorModule M)
      (fibreFst P P).conormalHom) key).trans (Category.assoc _ _ _))

end ExtClass

end Deformation.AlgebraExtension

end
