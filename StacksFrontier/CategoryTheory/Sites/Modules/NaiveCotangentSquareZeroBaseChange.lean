module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentOfSurjection
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquareIso

/-!
# The base change of a presented naive cotangent complex to a surjection

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a site, `p : B' ⟶ B` a locally
surjective one and `b : A ⟶ B'` a lift of `a` (`b ≫ p = a`). Let `α : ℰ ⟶ B` be a family of
generators presenting `B` over `A` and `α' : ℰ ⟶ B'` a lift of it, giving the map of
`A`-algebras `λ : A[ℰ] ⟶ B'`. Two chain maps `NL(α) ⟶ NL_{B/B'}` are then available:

* the comparison `NL(α) ⟶ NL_{B/A}` of **Stacks 08TY** followed by the base change
  `NL_{B/A} ⟶ NL_{B/B'}` of **Stacks 08TX**, induced by `[x] ↦ [α x]`;
* the map `NL(α) ⟶ (Ker p/Ker p²)[1]` of conormal sheaves induced by `λ`, followed by the
  canonical map `η : (Ker p/Ker p²)[1] ⟶ NL_{B/B'}`, induced by `[x] ↦ λ [x]` read as a
  constant.

They are homotopic, by **Stacks 00S1 (2)**: both are induced by morphisms of presentations
`A[ℰ] ⟶ B'[B]` over the same square, which agree on the base ring `A`. This identifies, in the
derived category, the class of the extension `0 ⟶ Ker p ⟶ B' ⟶ B ⟶ 0` read through any
presentation with the canonical map `NL_{B/A} ⟶ NL_{B/B'} ≅ (Ker p/Ker p²)[1]`.

## Main definitions

* `Stacks.SheafOfModules.liftConormalMap`: the map `𝒥/𝒥² ⟶ Ker p/Ker p²` induced by `λ`.
* `Stacks.SheafOfModules.liftToSingle`: the chain map `NL(α) ⟶ (Ker p/Ker p²)[1]` it gives.

## Main results

* `Stacks.SheafOfModules.comparisonBaseChangeHomotopy`: the homotopy.
* `Stacks.SheafOfModules.Q_map_comparison_comp_baseChange`: its consequence in the derived
  category.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)
open Stacks.Sites.Conormal (conormalSheaf conormalSequence conormalSheafMapOfSquare
  tensorSheafMapOfSquare conormalClass kernelIdeal)
open Stacks.Sites.FreeAlgebra (freeAlgebraSheaf freeAlgebraSheafCoefficientMap
  freeAlgebraSheafDesc underlyingPresheaf canonicalPresentation)

universe t u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A B B' : Sheaf J CommRingCat.{u}} (a : A ⟶ B) (p : B' ⟶ B) [Presheaf.IsLocallySurjective J p.hom]
  (b : A ⟶ B') (hb : b ≫ p = a)
  {E : Functor Cᵒᵖ (Type u)} (α : E ⟶ underlyingPresheaf J B)
  (α' : E ⟶ underlyingPresheaf J B')
  (hα : α' ≫ Functor.whiskerRight p.hom (forget CommRingCat.{u}) = α)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]

include hb hα in
omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J p.hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] in
/-- The map `λ : A[ℰ] ⟶ B'` lies over the presentation. -/
theorem freeAlgebraSheafDesc_comp_of_lift :
    freeAlgebraSheafDesc J A B' E b α' ≫ p = presentation J A B a E α ≫ 𝟙 B := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A B E ?_ ?_
  · rw [← Category.assoc, Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc, hb,
      Category.comp_id, Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [Category.comp_id, CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp,
      ← Category.assoc, Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc]
    exact hα

/-- The map of conormal sheaves `𝒥/𝒥² ⟶ Ker p/Ker p²` induced by `λ : A[ℰ] ⟶ B'`. -/
noncomputable def liftConormalMap :
    (presentationConormalSequence.{u, u, u, u} J A B a E α).X₁ ⟶
      conormalSheaf.{u, u, u, u} J B' B p :=
  conormalSheafMapOfSquare.{u, u, u, u} J _ B' B B (presentation J A B a E α) p
    (freeAlgebraSheafDesc J A B' E b α') (𝟙 B)
    (freeAlgebraSheafDesc_comp_of_lift J a p b hb α α' hα)

/-- On the class of a local relation `x`, `λ` gives the class of `λ x`. -/
theorem liftConormalMap_conormalClass (X : Cᵒᵖ)
    (x : kernelIdeal (presentation J A B a E α).hom X) :
    (liftConormalMap J a p b hb α α' hα).val.app X
        (conormalClass.{u, u, u, u} J A _ B (freeAlgebraSheafCoefficientMap J A E)
          (presentation J A B a E α) X x) =
      conormalClass.{u, u, u, u} J B' B' B (𝟙 B') p X
        ⟨(freeAlgebraSheafDesc J A B' E b α').hom.app X x,
          Stacks.Sites.Conormal.kernelIdeal_le_comap_square (presentation J A B a E α).hom p.hom
            (freeAlgebraSheafDesc J A B' E b α').hom (𝟙 B : B ⟶ B).hom
            (Stacks.Sites.Conormal.hom_of_square
              (freeAlgebraSheafDesc_comp_of_lift J a p b hb α α' hα)) X x.2⟩ :=
  Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A B' _ B' B B
    (freeAlgebraSheafCoefficientMap J A E) (𝟙 B') _ p _ (𝟙 B)
    (freeAlgebraSheafDesc_comp_of_lift J a p b hb α α' hα) X x

/-- The chain map `NL(α) ⟶ (Ker p/Ker p²)[1]` induced by `λ` in degree `-1`. -/
noncomputable def liftToSingle :
    presentationNaiveCotangentComplex.{u, u, u, u} J A B a E α ⟶
      (CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).obj
        (conormalSheaf.{u, u, u, u} J B' B p) := by
  letI : HasZeroObject (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  refine HomologicalComplex.mkHomToSingle
    (eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E α) ≫
      liftConormalMap J a p b hb α α' hα) ?_
  intro i hi
  exact (presentationNaiveCotangentComplex_isZero_X J A B a E α i
    (by rintro rfl; simp at hi) (by rintro rfl; simp at hi)).eq_of_src _ _

/-- In degree `-1`, `liftToSingle` is the map of conormal sheaves induced by `λ`. -/
theorem liftToSingle_f_negOne :
    (liftToSingle J a p b hb α α' hα).f (-1) =
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E α) ≫
        liftConormalMap J a p b hb α α' hα ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (conormalSheaf.{u, u, u, u} J B' B p)).inv := by
  let : HasZeroObject (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  rw [liftToSingle, HomologicalComplex.mkHomToSingle_f, Category.assoc]

/-! ### The two maps of presentations `A[ℰ] ⟶ B'[B]` -/

/-- `[x] ↦ [α x]`: the comparison `A[ℰ] ⟶ A[B]` followed by the base change `A[B] ⟶ B'[B]`. -/
noncomputable abbrev variableMap :
    freeAlgebraSheaf J A E ⟶ freeAlgebraSheaf J B' (underlyingPresheaf J B) :=
  freeAlgebraMap J A E (underlyingPresheaf J B) α ≫
    canonicalFreeAlgebraMapOfSquare J A B' B B b (𝟙 B)

/-- `[x] ↦ λ [x]`, read as a constant of `B'[B]`. -/
noncomputable abbrev constantMap :
    freeAlgebraSheaf J A E ⟶ freeAlgebraSheaf J B' (underlyingPresheaf J B) :=
  freeAlgebraSheafDesc J A B' E b α' ≫ freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B)

include hb in
omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J p.hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] in
/-- The map `[x] ↦ [α x]` lies over the presentation. -/
theorem variableMap_comp :
    variableMap J b α ≫ canonicalPresentation J B' B p = presentation J A B a E α ≫ 𝟙 B := by
  rw [Category.assoc, freeAlgebraMapOfSquare_comp_canonicalPresentation J A B' B B a p b (𝟙 B)
    (by rw [Category.comp_id, hb]), ← Category.assoc]
  exact congrArg (· ≫ 𝟙 B)
    (freeAlgebraMap_comp_presentation J A E (underlyingPresheaf J B) α B a α (𝟙 _)
      (Category.comp_id α))

include hb hα in
omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J p.hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] in
/-- The map `[x] ↦ λ [x]` lies over the presentation. -/
theorem constantMap_comp :
    constantMap J b α' ≫ canonicalPresentation J B' B p = presentation J A B a E α ≫ 𝟙 B := by
  rw [Category.assoc, Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap]
  exact freeAlgebraSheafDesc_comp_of_lift J a p b hb α α' hα

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The map `[x] ↦ [α x]` restricts to `b : A ⟶ B'` on coefficients. -/
theorem coefficientMap_comp_variableMap :
    b ≫ freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B) =
      freeAlgebraSheafCoefficientMap J A E ≫ variableMap J b α := by
  rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
    freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The map `[x] ↦ λ [x]` restricts to `b : A ⟶ B'` on coefficients. -/
theorem coefficientMap_comp_constantMap :
    b ≫ freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B) =
      freeAlgebraSheafCoefficientMap J A E ≫ constantMap J b α' := by
  rw [← Category.assoc, Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc]

/-- The comparison of **Stacks 08TY** on conormal sheaves, with its target read as the
degree `-1` term of `NL_{B/A}`. -/
noncomputable def comparisonConormalMap :
    (presentationConormalSequence.{u, u, u, u} J A B a E α).X₁ ⟶
      (canonicalConormalSequence.{u, u, u, u} J A B a).X₁ :=
  presentationConormalMap.{u, u, u, u} J A E (underlyingPresheaf J B) α B a α (𝟙 _)
    (Category.comp_id α)

/-- The comparison of **Stacks 08TY** on scalar extensions of differentials, with its target
read as the degree `0` term of `NL_{B/A}`. -/
noncomputable def comparisonTensorMap :
    (presentationConormalSequence.{u, u, u, u} J A B a E α).X₂ ⟶
      (canonicalConormalSequence.{u, u, u, u} J A B a).X₂ :=
  presentationTensorMap.{u, u, u, u} J A E (underlyingPresheaf J B) α B a α (𝟙 _)
    (Category.comp_id α)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The comparison of **Stacks 08TY** in degree `-1`, with its target read in `NL_{B/A}`. -/
theorem naiveCotangentComplexComparison_f_negOne_eq_comparisonConormalMap :
    (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α).f (-1) =
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E α) ≫
        comparisonConormalMap J a α ≫
        eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u} J A B a).symm :=
  presentationNaiveCotangentComplexMap_f_negOne.{u, u, u, u} J A E (underlyingPresheaf J B) α B a
    α (𝟙 _) (Category.comp_id α)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The comparison of **Stacks 08TY** in degree `0`, with its target read in `NL_{B/A}`. -/
theorem naiveCotangentComplexComparison_f_zero :
    (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α).f 0 =
      eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E α) ≫
        comparisonTensorMap J a α ≫
        eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u} J A B a).symm :=
  presentationNaiveCotangentComplexMap_f_zero.{u, u, u, u} J A E (underlyingPresheaf J B) α B a
    α (𝟙 _) (Category.comp_id α)

include hb in
omit [Presheaf.IsLocallySurjective J p.hom] in
/-- The comparison followed by the base change, on conormal sheaves, is the map of
`[x] ↦ [α x]`. -/
theorem presentationConormalMap_comp_conormalMapOfBase :
    comparisonConormalMap J a α ≫
        naiveCotangentConormalMapOfBase.{u, u, u, u} J A B a B' p b hb.symm =
      conormalSheafMapOfSquare.{u, u, u, u} J _ _ B B (presentation J A B a E α)
        (canonicalPresentation J B' B p) (variableMap J b α) (𝟙 B)
        (variableMap_comp J a p b hb α) := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun X x ↦ ?_)
  have e₁ := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{u, u, u, u} J A B _ _
    (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafCoefficientMap J A _)
    (presentation J A B a E α) (canonicalPresentation J A B a)
    (freeAlgebraMap J A E (underlyingPresheaf J B) α)
    (freeAlgebraMap_comp_presentation J A E (underlyingPresheaf J B) α B a α (𝟙 _)
      (Category.comp_id α)) X x
  have e₂ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A B'
    _ _ B B (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap J B' _)
    (canonicalPresentation J A B a) (canonicalPresentation J B' B p)
    (canonicalFreeAlgebraMapOfSquare J A B' B B b (𝟙 B)) (𝟙 B)
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A B' B B a p b (𝟙 B)
      (by rw [Category.comp_id, hb])) X
    ⟨(freeAlgebraMap J A E (underlyingPresheaf J B) α).hom.app X x,
      Stacks.Sites.Conormal.kernelIdeal_le_comap (presentation J A B a E α).hom
        (canonicalPresentation J A B a).hom (freeAlgebraMap J A E (underlyingPresheaf J B) α).hom
        (Stacks.Sites.Conormal.hom_of_comp_eq (freeAlgebraMap_comp_presentation J A E
          (underlyingPresheaf J B) α B a α (𝟙 _) (Category.comp_id α))) X x.2⟩
  have e₃ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A B'
    _ _ B B (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafCoefficientMap J B' _)
    (presentation J A B a E α) (canonicalPresentation J B' B p) (variableMap J b α) (𝟙 B)
    (variableMap_comp J a p b hb α) X x
  exact ((congrArg _ e₁).trans e₂).trans e₃.symm

include hb in
omit [Presheaf.IsLocallySurjective J p.hom] in
/-- The comparison followed by the base change, on the scalar extensions of the
differentials, is the map of `[x] ↦ [α x]`. -/
theorem presentationTensorMap_comp_tensorMapOfBase :
    comparisonTensorMap J a α ≫
        naiveCotangentTensorMapOfBase.{u, u, u, u} J A B a B' p b hb.symm =
      tensorSheafMapOfSquare.{u, u, u, u} J A B' _ _ B B (freeAlgebraSheafCoefficientMap J A E)
        (freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B))
        (presentation J A B a E α) (canonicalPresentation J B' B p) (variableMap J b α) (𝟙 B) b
        (variableMap_comp J a p b hb α) (coefficientMap_comp_variableMap J b α) := by
  refine Stacks.Sites.Conormal.tensorSheaf_hom_ext.{u, u, u, u} J A _ B
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) _ (fun X x ↦ ?_)
  have e₁ := Stacks.Sites.Conormal.tensorSheafMapOfFac_tensorDifferential.{u, u, u, u} J A B _ _
    (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafCoefficientMap J A _)
    (presentation J A B a E α) (canonicalPresentation J A B a)
    (freeAlgebraMap J A E (underlyingPresheaf J B) α)
    (freeAlgebraMap_comp_presentation J A E (underlyingPresheaf J B) α B a α (𝟙 _)
      (Category.comp_id α))
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E (underlyingPresheaf J B) α) X x
  have e₂ := Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J A B'
    _ _ B B (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap J B' _)
    (canonicalPresentation J A B a) (canonicalPresentation J B' B p)
    (canonicalFreeAlgebraMapOfSquare J A B' B B b (𝟙 B)) (𝟙 B) b
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A B' B B a p b (𝟙 B)
      (by rw [Category.comp_id, hb]))
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A B' _ _ b
      (underlyingPresheafMap J B B (𝟙 B))).symm X
    ((freeAlgebraMap J A E (underlyingPresheaf J B) α).hom.app X x)
  have e₃ := Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J A B'
    _ _ B B (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafCoefficientMap J B' _)
    (presentation J A B a E α) (canonicalPresentation J B' B p) (variableMap J b α) (𝟙 B) b
    (variableMap_comp J a p b hb α) (coefficientMap_comp_variableMap J b α) X x
  exact ((congrArg _ e₁).trans e₂).trans e₃.symm

include hb hα in
/-- `λ` followed by the constants, on conormal sheaves, is the map of `[x] ↦ λ [x]`. -/
theorem liftConormalMap_comp_conormalToNaiveCotangentConormal :
    liftConormalMap J a p b hb α α' hα ≫ conormalToNaiveCotangentConormal J B' B p =
      conormalSheafMapOfSquare.{u, u, u, u} J _ _ B B (presentation J A B a E α)
        (canonicalPresentation J B' B p) (constantMap J b α') (𝟙 B)
        (constantMap_comp J a p b hb α α' hα) := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun X x ↦ ?_)
  have e₁ := liftConormalMap_conormalClass J a p b hb α α' hα X x
  have e₂ := conormalToNaiveCotangentConormal_conormalClass J B' B p (𝟙 B') X
    ⟨(freeAlgebraSheafDesc J A B' E b α').hom.app X x,
      Stacks.Sites.Conormal.kernelIdeal_le_comap_square (presentation J A B a E α).hom p.hom
        (freeAlgebraSheafDesc J A B' E b α').hom (𝟙 B : B ⟶ B).hom
        (Stacks.Sites.Conormal.hom_of_square
          (freeAlgebraSheafDesc_comp_of_lift J a p b hb α α' hα)) X x.2⟩
  have e₃ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A B'
    _ _ B B (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafCoefficientMap J B' _)
    (presentation J A B a E α) (canonicalPresentation J B' B p) (constantMap J b α') (𝟙 B)
    (constantMap_comp J a p b hb α α' hα) X x
  exact ((congrArg _ e₁).trans e₂).trans e₃.symm

/-! ### The composite of the comparison and the base change -/

omit [HasWeakSheafify J CommRingCat.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Presheaf.IsLocallySurjective J p.hom] in
/-- Two inverse `eqToHom`s cancel in the middle of a composite. -/
private theorem comp_eq_eqToHom_comp_comp {𝒞 : Type*} [Category 𝒞] {V W X Y Z U : 𝒞}
    {φ : V ⟶ W} {ψ : W ⟶ U} {e : V ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z} {k : Z ⟶ U}
    {h : Y = W} {h' : W = Y} (hφ : φ = e ≫ f ≫ eqToHom h) (hψ : ψ = eqToHom h' ≫ g ≫ k) :
    φ ≫ ψ = e ≫ (f ≫ g) ≫ k := by
  subst hφ hψ; simp

include hb in
omit [Presheaf.IsLocallySurjective J p.hom] in
/-- In degree `-1`, the comparison followed by the base change is the composite of the maps on
conormal sheaves. -/
theorem comparison_comp_baseChange_f_negOne :
    (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α ≫
        naiveCotangentComplexMapOfBase.{u, u, u, u} J A B a B' p b hb.symm).f (-1) =
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E α) ≫
        (comparisonConormalMap J a α ≫
          naiveCotangentConormalMapOfBase.{u, u, u, u} J A B a B' p b hb.symm) ≫
        eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u} J B' B p).symm :=
  comp_eq_eqToHom_comp_comp
    (naiveCotangentComplexComparison_f_negOne_eq_comparisonConormalMap J a α)
    (naiveCotangentComplexMapOfBase_f_negOne J A B a B' p b hb.symm)

include hb in
omit [Presheaf.IsLocallySurjective J p.hom] in
/-- In degree `0`, the comparison followed by the base change is the composite of the maps on the
scalar extensions of the differentials. -/
theorem comparison_comp_baseChange_f_zero :
    (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α ≫
        naiveCotangentComplexMapOfBase.{u, u, u, u} J A B a B' p b hb.symm).f 0 =
      eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E α) ≫
        (comparisonTensorMap J a α ≫
          naiveCotangentTensorMapOfBase.{u, u, u, u} J A B a B' p b hb.symm) ≫
        eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u} J B' B p).symm :=
  comp_eq_eqToHom_comp_comp (naiveCotangentComplexComparison_f_zero J a α)
    (naiveCotangentComplexMapOfBase_f_zero J A B a B' p b hb.symm)

/-! ### The homotopy -/

/-- **The comparison followed by the base change is homotopic to `λ` followed by `η`**
(**Stacks 00S1 (2)**): both are induced by morphisms of presentations `A[ℰ] ⟶ B'[B]` over one
square, agreeing on the base ring. -/
noncomputable def comparisonBaseChangeHomotopy :
    Homotopy (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α ≫
        naiveCotangentComplexMapOfBase.{u, u, u, u} J A B a B' p b hb.symm)
      (liftToSingle J a p b hb α α' hα ≫ conormalToNaiveCotangentComplex J B' B p) := by
  letI : HasZeroObject (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  let H : (presentationConormalSequence.{u, u, u, u} J A B a E α).X₂ ⟶
      (canonicalConormalSequence.{u, u, u, u} J B' B p).X₁ :=
    Stacks.Sites.Conormal.conormalHomotopyOfSquare.{u, u, u, u} J A B' _ _ B B
      (freeAlgebraSheafCoefficientMap J A E)
      (freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B))
      (presentation J A B a E α) (canonicalPresentation J B' B p) (variableMap J b α)
      (constantMap J b α') (𝟙 B) b (variableMap_comp J a p b hb α)
      (constantMap_comp J a p b hb α α' hα) (coefficientMap_comp_variableMap J b α)
      (coefficientMap_comp_constantMap J b α')
  have key₁ : comparisonConormalMap J a α ≫
        naiveCotangentConormalMapOfBase.{u, u, u, u} J A B a B' p b hb.symm =
      ((presentationConormalSequence.{u, u, u, u} J A B a E α).f ≫ H :
        (presentationConormalSequence.{u, u, u, u} J A B a E α).X₁ ⟶
          (canonicalConormalSequence.{u, u, u, u} J B' B p).X₁) +
        liftConormalMap J a p b hb α α' hα ≫ conormalToNaiveCotangentConormal J B' B p := by
    rw [presentationConormalMap_comp_conormalMapOfBase J a p b hb α,
      liftConormalMap_comp_conormalToNaiveCotangentConormal]
    exact Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_add.{u, u, u, u} J A B' _ _ B B
      (freeAlgebraSheafCoefficientMap J A E)
      (freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B))
      (presentation J A B a E α) (canonicalPresentation J B' B p) (variableMap J b α)
      (constantMap J b α') (𝟙 B) b (variableMap_comp J a p b hb α)
      (constantMap_comp J a p b hb α α' hα) (coefficientMap_comp_variableMap J b α)
      (coefficientMap_comp_constantMap J b α')
  have key₀ : comparisonTensorMap J a α ≫
        naiveCotangentTensorMapOfBase.{u, u, u, u} J A B a B' p b hb.symm =
      H ≫ (canonicalConormalSequence.{u, u, u, u} J B' B p).f := by
    rw [presentationTensorMap_comp_tensorMapOfBase J a p b hb α]
    refine (Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_add.{u, u, u, u} J A B' _ _ B B
      (freeAlgebraSheafCoefficientMap J A E)
      (freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B))
      (presentation J A B a E α) (canonicalPresentation J B' B p) (variableMap J b α)
      (constantMap J b α') (𝟙 B) b (variableMap_comp J a p b hb α)
      (constantMap_comp J a p b hb α α' hα) (coefficientMap_comp_variableMap J b α)
      (coefficientMap_comp_constantMap J b α')).trans ?_
    refine (congrArg (_ + ·) ?_).trans (add_zero _)
    exact Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_zero_of_factor J A B' _ _ B B
      (freeAlgebraSheafCoefficientMap J A E)
      (freeAlgebraSheafCoefficientMap J B' (underlyingPresheaf J B))
      (presentation J A B a E α) (canonicalPresentation J B' B p)
      (freeAlgebraSheafDesc J A B' E b α') (𝟙 B) b (constantMap_comp J a p b hb α α' hα)
      (coefficientMap_comp_constantMap J b α')
  refine Stacks.NaiveCotangentFinitePresentation.homotopyOfIsZeroX
    (fun i h1 h2 ↦ presentationNaiveCotangentComplex_isZero_X J A B a E α i h1 h2)
    (eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E α) ≫ H ≫
      eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u} J B' B p).symm) ?_ ?_
  · rw [comparison_comp_baseChange_f_negOne J a p b hb α, key₁, HomologicalComplex.comp_f,
      liftToSingle_f_negOne, conormalToNaiveCotangentComplex_f_negOne,
      presentationNaiveCotangentComplex_d_negOne_zero]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
  · have hz : (liftToSingle J a p b hb α α' hα ≫ conormalToNaiveCotangentComplex J B' B p).f 0 =
        0 := by
      rw [HomologicalComplex.comp_f,
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
          (conormalSheaf.{u, u, u, u} J B' B p) 0 (by decide)).eq_of_tgt
          ((liftToSingle J a p b hb α α' hα).f 0) 0, zero_comp]
    rw [hz, add_zero, comparison_comp_baseChange_f_zero J a p b hb α, key₀,
      naiveCotangentComplex_d_negOne_zero]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B))]

/-- The homotopy, read in the derived category. -/
theorem Q_map_comparison_comp_baseChange :
    DerivedCategory.Q.map (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α) ≫
        DerivedCategory.Q.map
          (naiveCotangentComplexMapOfBase.{u, u, u, u} J A B a B' p b hb.symm) =
      DerivedCategory.Q.map (liftToSingle J a p b hb α α' hα) ≫
        DerivedCategory.Q.map (conormalToNaiveCotangentComplex J B' B p) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy (h := comparisonBaseChangeHomotopy J a p b hb α α' hα)

variable {G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
  (κ : conormalSheaf.{u, u, u, u} J B' B p ⟶ G)

/-- The class in `Ext¹(NL(α), G)` of `λ` on conormal sheaves followed by `κ : Ker p/Ker p² ⟶ G`
is the map `NL(α) ⟶ (Ker p/Ker p²)[1]` of `λ` followed by `κ[1]`. -/
theorem presentationConormalExtClass_liftConormalMap_comp :
    presentationConormalExtClass.{u, u, u, t} J A B a E α G
        (liftConormalMap J a p b hb α α' hα ≫ κ) =
      DerivedCategory.Q.map (liftToSingle J a p b hb α α' hα) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).map κ) ≫
        ((DerivedCategory.singleFunctors
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B))).shiftIso
          (1 : ℤ) (-1) 0 (by decide)).inv.app G := by
  let : HasZeroObject (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  unfold presentationConormalExtClass
  rw [← Category.assoc (DerivedCategory.Q.map (liftToSingle J a p b hb α α' hα)),
    ← CategoryTheory.Functor.map_comp]
  congr 2
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.mkHomToSingle_f, HomologicalComplex.comp_f, liftToSingle_f_negOne]
  change _ = _ ≫ ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).map κ).f (-1)
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The class of `λ` followed by `κ`, through canonical complexes**: it is the comparison
`NL(α) ⟶ NL_{B/A}` of **Stacks 08TY**, followed by the base change `NL_{B/A} ⟶ NL_{B/B'}` of
**Stacks 08TX**, the inverse of `η : (Ker p/Ker p²)[1] ≅ NL_{B/B'}` and `κ[1]`. -/
theorem presentationConormalExtClass_liftConormalMap_comp_eq_canonical :
    presentationConormalExtClass.{u, u, u, t} J A B a E α G
        (liftConormalMap J a p b hb α α' hα ≫ κ) =
      DerivedCategory.Q.map (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α) ≫
        DerivedCategory.Q.map
          (naiveCotangentComplexMapOfBase.{u, u, u, u} J A B a B' p b hb.symm) ≫
        inv (DerivedCategory.Q.map (conormalToNaiveCotangentComplex J B' B p)) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (-1)).map κ) ≫
        ((DerivedCategory.singleFunctors
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B))).shiftIso
          (1 : ℤ) (-1) 0 (by decide)).inv.app G := by
  rw [presentationConormalExtClass_liftConormalMap_comp, ← Category.assoc
    (DerivedCategory.Q.map (naiveCotangentComplexComparison.{u, u, u, u} J A B a E α)),
    Q_map_comparison_comp_baseChange J a p b hb α α' hα, Category.assoc,
    IsIso.hom_inv_id_assoc]

/-! ### A base change followed by a square, and a square followed by a base change -/

section Rectangle

variable {A O B A'' E' E₂ : Sheaf J CommRingCat.{u}} (a : A ⟶ O) (σ : O ⟶ B) (ψ : A ⟶ A'')
  (b : A'' ⟶ B) (hab : a ≫ σ = ψ ≫ b) (p : E' ⟶ B) (bD : A'' ⟶ E') (hbD : b = bD ≫ p)
  (q : E₂ ⟶ O) (b₂ : A ⟶ E₂) (hb₂ : a = b₂ ≫ q) (fst : E₂ ⟶ E')
  (hfst : q ≫ σ = fst ≫ p) (hbase : b₂ ≫ fst = ψ ≫ bD)

include hbase in
omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The two composite morphisms of polynomial presentations `A[O] ⟶ E'[B]` around the
rectangle agree. -/
theorem canonicalFreeAlgebraMap_rectangle :
    canonicalFreeAlgebraMapOfSquare J A E₂ O O b₂ (𝟙 O) ≫
        canonicalFreeAlgebraMapOfSquare J E₂ E' O B fst σ =
      canonicalFreeAlgebraMapOfSquare J A A'' O B ψ σ ≫
        canonicalFreeAlgebraMapOfSquare J A'' E' B B bD (𝟙 B) := by
  rw [canonicalFreeAlgebraMapOfSquare_comp, canonicalFreeAlgebraMapOfSquare_comp, hbase,
    Category.id_comp, Category.comp_id]

include hbase in
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The rectangle on conormal sheaves. -/
theorem conormalMap_rectangle :
    naiveCotangentConormalMapOfBase.{u, u, u, u} J A O a E₂ q b₂ hb₂ ≫
        naiveCotangentConormalMapOfSquare.{u, u, u, u} J E₂ O q E' B p fst σ hfst =
      naiveCotangentConormalMapOfSquare.{u, u, u, u} J A O a A'' B b ψ σ hab ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite σ)).map
          (naiveCotangentConormalMapOfBase.{u, u, u, u} J A'' B b E' p bD hbD) := by
  refine Stacks.Sites.Conormal.conormal_hom_ext _ _ (fun X x ↦ ?_)
  have e₁ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A E₂
    _ _ O O (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap J E₂ _)
    (canonicalPresentation J A O a) (canonicalPresentation J E₂ O q)
    (canonicalFreeAlgebraMapOfSquare J A E₂ O O b₂ (𝟙 O)) (𝟙 O)
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A E₂ O O a q b₂ (𝟙 O)
      (comp_id_eq_comp_of_fac J A O a E₂ q b₂ hb₂)) X x
  have e₂ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J E₂ E'
    _ _ O B (freeAlgebraSheafCoefficientMap J E₂ _) (freeAlgebraSheafCoefficientMap J E' _)
    (canonicalPresentation J E₂ O q) (canonicalPresentation J E' B p)
    (canonicalFreeAlgebraMapOfSquare J E₂ E' O B fst σ) σ
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J E₂ E' O B q p fst σ hfst) X
    ⟨(canonicalFreeAlgebraMapOfSquare J A E₂ O O b₂ (𝟙 O)).hom.app X x,
      Stacks.Sites.Conormal.kernelIdeal_le_comap_square _ _ _ _
        (Stacks.Sites.Conormal.hom_of_square
          (freeAlgebraMapOfSquare_comp_canonicalPresentation J A E₂ O O a q b₂ (𝟙 O)
            (comp_id_eq_comp_of_fac J A O a E₂ q b₂ hb₂))) X x.2⟩
  have e₃ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A A''
    _ _ O B (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap J A'' _)
    (canonicalPresentation J A O a) (canonicalPresentation J A'' B b)
    (canonicalFreeAlgebraMapOfSquare J A A'' O B ψ σ) σ
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A'' O B a b ψ σ hab) X x
  have e₄ := Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, u, u} J A'' E'
    _ _ B B (freeAlgebraSheafCoefficientMap J A'' _) (freeAlgebraSheafCoefficientMap J E' _)
    (canonicalPresentation J A'' B b) (canonicalPresentation J E' B p)
    (canonicalFreeAlgebraMapOfSquare J A'' E' B B bD (𝟙 B)) (𝟙 B)
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A'' E' B B b p bD (𝟙 B)
      (comp_id_eq_comp_of_fac J A'' B b E' p bD hbD)) X
    ⟨(canonicalFreeAlgebraMapOfSquare J A A'' O B ψ σ).hom.app X x,
      Stacks.Sites.Conormal.kernelIdeal_le_comap_square _ _ _ _
        (Stacks.Sites.Conormal.hom_of_square
          (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A'' O B a b ψ σ hab)) X x.2⟩
  have h := congrArg (fun t ↦ t.hom.app X x.1)
    (canonicalFreeAlgebraMap_rectangle J σ ψ bD b₂ fst hbase)
  refine ((congrArg _ e₁).trans e₂).trans (Eq.trans ?_ ((congrArg (fun t ↦
    (naiveCotangentConormalMapOfBase.{u, u, u, u} J A'' B b E' p bD hbD).val.app X t) e₃).trans
      e₄).symm)
  exact congrArg (conormalClass.{u, u, u, u} J E' _ B (freeAlgebraSheafCoefficientMap J E' _)
    (canonicalPresentation J E' B p) X) (Subtype.ext h)

include hbase in
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The rectangle on the scalar extensions of the differentials. -/
theorem tensorMap_rectangle :
    naiveCotangentTensorMapOfBase.{u, u, u, u} J A O a E₂ q b₂ hb₂ ≫
        naiveCotangentTensorMapOfSquare.{u, u, u, u} J E₂ O q E' B p fst σ hfst =
      naiveCotangentTensorMapOfSquare.{u, u, u, u} J A O a A'' B b ψ σ hab ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite σ)).map
          (naiveCotangentTensorMapOfBase.{u, u, u, u} J A'' B b E' p bD hbD) := by
  refine Stacks.Sites.Conormal.tensorSheaf_hom_ext.{u, u, u, u} J A _ O
    (freeAlgebraSheafCoefficientMap J A _) (canonicalPresentation J A O a) _ (fun X x ↦ ?_)
  have e₁ := Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J A E₂
    _ _ O O (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap J E₂ _)
    (canonicalPresentation J A O a) (canonicalPresentation J E₂ O q)
    (canonicalFreeAlgebraMapOfSquare J A E₂ O O b₂ (𝟙 O)) (𝟙 O) b₂
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A E₂ O O a q b₂ (𝟙 O)
      (comp_id_eq_comp_of_fac J A O a E₂ q b₂ hb₂))
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A E₂ _ _ b₂
      (underlyingPresheafMap J O O (𝟙 O))).symm X x
  have e₂ := Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J E₂ E'
    _ _ O B (freeAlgebraSheafCoefficientMap J E₂ _) (freeAlgebraSheafCoefficientMap J E' _)
    (canonicalPresentation J E₂ O q) (canonicalPresentation J E' B p)
    (canonicalFreeAlgebraMapOfSquare J E₂ E' O B fst σ) σ fst
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J E₂ E' O B q p fst σ hfst)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J E₂ E' _ _ fst
      (underlyingPresheafMap J O B σ)).symm X
    ((canonicalFreeAlgebraMapOfSquare J A E₂ O O b₂ (𝟙 O)).hom.app X x)
  have e₃ := Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J A A''
    _ _ O B (freeAlgebraSheafCoefficientMap J A _) (freeAlgebraSheafCoefficientMap J A'' _)
    (canonicalPresentation J A O a) (canonicalPresentation J A'' B b)
    (canonicalFreeAlgebraMapOfSquare J A A'' O B ψ σ) σ ψ
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A'' O B a b ψ σ hab)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A A'' _ _ ψ
      (underlyingPresheafMap J O B σ)).symm X x
  have e₄ := Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential.{u, u, u, u} J A'' E'
    _ _ B B (freeAlgebraSheafCoefficientMap J A'' _) (freeAlgebraSheafCoefficientMap J E' _)
    (canonicalPresentation J A'' B b) (canonicalPresentation J E' B p)
    (canonicalFreeAlgebraMapOfSquare J A'' E' B B bD (𝟙 B)) (𝟙 B) bD
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A'' E' B B b p bD (𝟙 B)
      (comp_id_eq_comp_of_fac J A'' B b E' p bD hbD))
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A'' E' _ _ bD
      (underlyingPresheafMap J B B (𝟙 B))).symm X
    ((canonicalFreeAlgebraMapOfSquare J A A'' O B ψ σ).hom.app X x)
  have h := congrArg (fun t ↦ t.hom.app X x)
    (canonicalFreeAlgebraMap_rectangle J σ ψ bD b₂ fst hbase)
  refine ((congrArg _ e₁).trans e₂).trans (Eq.trans ?_ ((congrArg (fun t ↦
    (naiveCotangentTensorMapOfBase.{u, u, u, u} J A'' B b E' p bD hbD).val.app X t) e₃).trans
      e₄).symm)
  exact congrArg (Stacks.Sites.Conormal.tensorDifferential.{u, u, u, u} J E' _ B
    (freeAlgebraSheafCoefficientMap J E' _) (canonicalPresentation J E' B p) X) h

include hbase in
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The rectangle of Stacks 08TX maps**: the base change `NL_{O/A} ⟶ NL_{O/E₂}` followed by
the map of the square `E₂ ⟶ E'` over `σ` is the map of the square `A ⟶ A''` over `σ` followed by
the base change `NL_{B/A''} ⟶ NL_{B/E'}`, when the two composites `A ⟶ E'` agree. -/
theorem naiveCotangentComplexMap_rectangle :
    naiveCotangentComplexMapOfBase.{u, u, u, u} J A O a E₂ q b₂ hb₂ ≫
        naiveCotangentComplexMapOfSquare.{u, u, u, u} J E₂ O q E' B p fst σ hfst =
      naiveCotangentComplexMapOfSquare.{u, u, u, u} J A O a A'' B b ψ σ hab ≫
        ((_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite σ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (naiveCotangentComplexMapOfBase.{u, u, u, u} J A'' B b E' p bD hbD) := by
  let : HasZeroObject (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    hasZeroObject_of_hasTerminal_object
  refine HomologicalComplex.from_double_hom_ext
    (hi₀₁ := show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) ?_ ?_
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      naiveCotangentComplexMapOfBase_f_negOne, naiveCotangentComplexMapOfSquare_f_negOne,
      naiveCotangentComplexMapOfSquare_f_negOne, naiveCotangentComplexMapOfBase_f_negOne]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Functor.map_comp, eqToHom_map]
    rw [← Category.assoc (naiveCotangentConormalMapOfBase.{u, u, u, u} J A O a E₂ q b₂ hb₂),
      conormalMap_rectangle J a σ ψ b hab p bD hbD q b₂ hb₂ fst hfst hbase]
    simp only [Category.assoc]
    rfl
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      naiveCotangentComplexMapOfBase_f_zero, naiveCotangentComplexMapOfSquare_f_zero,
      naiveCotangentComplexMapOfSquare_f_zero, naiveCotangentComplexMapOfBase_f_zero]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Functor.map_comp, eqToHom_map]
    rw [← Category.assoc (naiveCotangentTensorMapOfBase.{u, u, u, u} J A O a E₂ q b₂ hb₂),
      tensorMap_rectangle J a σ ψ b hab p bD hbD q b₂ hb₂ fst hfst hbase]
    simp only [Category.assoc]
    rfl

end Rectangle

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The base change of naive cotangent complexes depends on the base map only through its
value. -/
theorem naiveCotangentComplexMapOfBase_congr {A O E : Sheaf J CommRingCat.{u}} (a : A ⟶ O)
    (r : E ⟶ O) {b b' : A ⟶ E} (hb : a = b ≫ r) (hb' : a = b' ≫ r) (h : b = b') :
    naiveCotangentComplexMapOfBase.{u, u, u, u} J A O a E r b hb =
      naiveCotangentComplexMapOfBase.{u, u, u, u} J A O a E r b' hb' := by
  subst h
  rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Base changes of naive cotangent complexes compose** (Stacks 08TX): for `a = b₂ ≫ q` and
`q = j ≫ r`, the base change along `b₂` followed by the base change along `j` is the base change
along `b₂ ≫ j`. -/
theorem naiveCotangentComplexMapOfBase_comp {A O E₂ E₃ : Sheaf J CommRingCat.{u}} (a : A ⟶ O)
    (q : E₂ ⟶ O) (r : E₃ ⟶ O) (b₂ : A ⟶ E₂) (j : E₂ ⟶ E₃) (hb₂ : a = b₂ ≫ q)
    (hj : q = j ≫ r) (h : a = (b₂ ≫ j) ≫ r) :
    naiveCotangentComplexMapOfBase.{u, u, u, u} J A O a E₂ q b₂ hb₂ ≫
        naiveCotangentComplexMapOfBase.{u, u, u, u} J E₂ O q E₃ r j hj =
      naiveCotangentComplexMapOfBase.{u, u, u, u} J A O a E₃ r (b₂ ≫ j) h := by
  have hr := naiveCotangentComplexMap_rectangle J a (𝟙 O) (𝟙 A) a
    (by rw [Category.comp_id, Category.id_comp]) r (b₂ ≫ j) h q b₂ hb₂ j
    (comp_id_eq_comp_of_fac J E₂ O q E₃ r j hj) (Category.id_comp _).symm
  refine hr.trans ?_
  rw [naiveCotangentComplexMapOfSquare_id]
  exact Category.id_comp _

end Stacks.SheafOfModules

end
