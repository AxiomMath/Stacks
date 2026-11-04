module

public import StacksFrontier.CategoryTheory.Localization.Monoidal.FunctorBraided
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor

/-!
# Braided functors on derived categories from braided functors preserving K-flatness

In the setting of `StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor`, let
`Comp(A)` and `Comp(B)` be symmetric monoidal and assume that the monoidal functor
`F.mapHomologicalComplex` commutes with the braidings (for the Koszul symmetries this is
`CategoryTheory.Functor.mapHomologicalComplexBraided` for a braided `F`). With the symmetries
induced on `K(A)`, `K(B)`, `D(A)`, `D(B)`, the three monoidal functors of that file are
braided:

* `F.mapHomotopyCategory : K(A) ⥤ K(B)`;
* its restriction `kFlatLift F hF` to the K-flat objects;
* any `Φ : D(A) ⥤ D(B)` computed on K-flat objects by `F`, with the structure
  `CochainComplex.KFlatMonoidal.derivedFunctorMonoidal`.

Each is `CategoryTheory.Localization.Monoidal.functorBraidedOfComp` (or the lift to a full
subcategory).

## Main definitions

* `CochainComplex.KFlatMonoidal.mapHomotopyCategoryBraided`
* `CochainComplex.KFlatMonoidal.kFlatLiftBraided`
* `CochainComplex.KFlatMonoidal.derivedFunctorBraided`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatBifunctor

universe w w' v₁ v₂ u₁ u₂

namespace CochainComplex.KFlatMonoidal

attribute [local instance] homotopyMonoidal homotopyBraided

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ B, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [SymmetricCategory (CochainComplex A ℤ)] [SymmetricCategory (CochainComplex B ℤ)]
  (F : A ⥤ B) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) F]
  (hFβ : ∀ K L : CochainComplex A ℤ,
    Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (β_ K L).hom =
      (β_ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom ≫
        Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) L K)

/-- `F.mapHomologicalComplex`, braided by the hypothesis `hFβ`. -/
@[instance_reducible]
def mapHomologicalComplexBraidedOf : (F.mapHomologicalComplex (ComplexShape.up ℤ)).Braided :=
  { toMonoidal := Functor.mapHomologicalComplexMonoidal F
    braided := hFβ }

/-! ### The homotopy categories -/

/-- **`F.mapHomotopyCategory : K(A) ⥤ K(B)` is braided**, for the symmetries induced by the
symmetries of complexes, with the monoidal structure `mapHomotopyCategoryMonoidal`. -/
@[instance_reducible]
def mapHomotopyCategoryBraided : (F.mapHomotopyCategory (ComplexShape.up ℤ)).Braided :=
  letI := mapHomotopyCategoryLifting F
  letI := mapHomologicalComplexBraidedOf F hFβ
  (Localization.Monoidal.functorBraidedOfComp
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A)))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    F.mapHomotopyCategoryLocalized
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit B))) : F.mapHomotopyCategoryLocalized.Braided)

/-- `mapHomotopyCategoryBraided` extends `mapHomotopyCategoryMonoidal`. -/
lemma mapHomotopyCategoryBraided_toMonoidal :
    (mapHomotopyCategoryBraided F hFβ).toMonoidal = mapHomotopyCategoryMonoidal F :=
  rfl

/-! ### The K-flat objects -/

variable (hF : ∀ K : CochainComplex A ℤ,
  _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K →
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

/-- **The restriction of `F.mapHomotopyCategory` to the K-flat objects is braided**, the K-flat
objects being full braided subcategories on both sides. -/
@[instance_reducible]
def kFlatLiftBraided : (kFlatLift F hF).Braided :=
  letI := mapHomotopyCategoryBraided F hFβ
  { toMonoidal := kFlatLiftMonoidal F hF
    braided := (ObjectProperty.liftLaxBraided _ _ _).braided }

/-- `kFlatLiftBraided` extends `kFlatLiftMonoidal`. -/
lemma kFlatLiftBraided_toMonoidal :
    (kFlatLiftBraided F hFβ hF).toMonoidal = kFlatLiftMonoidal F hF :=
  rfl

/-! ### The derived categories -/

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) P ∧ QuasiIso f)
  (Φ : DerivedCategory A ⥤ DerivedCategory B)
  (e : kFlatQ (curriedTensor A) ⋙ Φ ≅ kFlatLift F hF ⋙ kFlatQ (curriedTensor B))

/-- **A functor `Φ : D(A) ⥤ D(B)` computed on K-flat objects by `F` is braided** when `F` is
braided on complexes, for the monoidal structure `derivedFunctorMonoidal` and the symmetries
`derivedSymmetric` induced by the symmetries of complexes. -/
@[instance_reducible]
def derivedFunctorBraided :
    @Functor.Braided _ _ (derivedMonoidal A hresA) (derivedSymmetric A hresA).toBraidedCategory
      _ _ (derivedMonoidal B hresB) (derivedSymmetric B hresB).toBraidedCategory Φ :=
  letI := kFlatQ_isLocalization (curriedTensor A) hresA
  letI := kFlatQ_isLocalization (curriedTensor B) hresB
  letI := kFlatLiftBraided F hFβ hF
  letI := derivedFunctorLifting F hF hresA hresB Φ e
  (Localization.Monoidal.functorBraidedOfComp
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A))
    (derivedFunctorLocalized hresA hresB Φ)
    (kFlatLift F hF ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor B))
        (kFlatQuasiIso (curriedTensor B))
        (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _)))) :
      (derivedFunctorLocalized hresA hresB Φ).Braided)

/-- `derivedFunctorBraided` extends `derivedFunctorMonoidal`. -/
lemma derivedFunctorBraided_toMonoidal :
    (derivedFunctorBraided F hFβ hF hresA hresB Φ e).toMonoidal =
      derivedFunctorMonoidal F hF hresA hresB Φ e :=
  rfl

end CochainComplex.KFlatMonoidal

end
