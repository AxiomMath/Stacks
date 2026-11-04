module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.CategoryTheory.Monoidal.ScalarUnitor
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# Linearity of the derived tensor product

Let `A` be an `R`-linear abelian monoidal category in which scalars act on a tensor product
through its left factor, `(a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y)`. Then the same holds for the total
tensor product of complexes, and, since scalars then act on every object through the monoidal
unit, it passes along the two monoidal localizations `Comp(A) ⥤ K(A)` and
`K(A)_{K-flat} ⥤ D(A)` which define the derived tensor product of
`CochainComplex.KFlatMonoidal.derivedMonoidal`. Hence the derived tensor product is `R`-linear
in each variable.

## Main results

* `CochainComplex.KFlatMonoidal.smul_id_whiskerRight_cochainComplex`: linearity of the total
  tensor product of complexes in its left variable.
* `CochainComplex.KFlatMonoidal.smul_id_eq_leftUnitor_derived`: scalars act on every object of
  `D(A)` through the unit object.
* `CochainComplex.KFlatMonoidal.derived_smul_id_whiskerRight` and
  `CochainComplex.KFlatMonoidal.derived_whiskerLeft_smul_id`: the derived tensor product is
  `R`-linear in each variable.

## Implementation notes

No representative of an object of `D(A)` is chosen: the identity
`a • 𝟙 X = λ_X⁻¹ ≫ ((a • 𝟙 𝟙) ▷ X) ≫ λ_X` is checked on the image of the localization functor
and transported along an isomorphism, by
`CategoryTheory.MonoidalCategory.smul_id_eq_leftUnitor_map` and
`CategoryTheory.MonoidalCategory.smul_id_eq_leftUnitor_of_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w v u

namespace CochainComplex.KFlatMonoidal

open CochainComplex.KFlatBifunctor

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (R : Type*) [CommRing R] [Linear R A]

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The total tensor product of complexes is linear in its left variable** when the tensor
product of `A` is. -/
theorem smul_id_whiskerRight_cochainComplex
    (hA : ∀ (a : R) (X Y : A), (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y))
    (a : R) (X Y : CochainComplex A ℤ) : (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y) := by
  rw [show (a • 𝟙 X) ▷ Y = HomologicalComplex.tensorHom (a • 𝟙 X) (𝟙 Y) from rfl]
  ext1 n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [curriedTensor_obj_obj, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, curriedTensor_map_app, hA,
    curriedTensor_obj_map, whiskerLeft_id, Category.id_comp, Linear.smul_comp, Linear.comp_smul]
  exact congrArg (a • ·) (Category.comp_id _).symm

attribute [local instance] homotopyMonoidal

variable [SymmetricCategory (CochainComplex A ℤ)]

omit [SymmetricCategory (CochainComplex A ℤ)] in
/-- Scalars act on every object of `K(A)` through the unit object. -/
theorem smul_id_eq_leftUnitor_homotopy
    (hA : ∀ (a : R) (X Y : A), (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y))
    (a : R) (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ _)) ▷ X) ≫ (λ_ X).hom :=
  MonoidalCategory.smul_id_eq_leftUnitor_map (HomotopyCategory.quotient A (ComplexShape.up ℤ)) a
    X.as (by rw [smul_id_whiskerRight_cochainComplex A R hA]; simp)

omit [SymmetricCategory (CochainComplex A ℤ)] in
/-- Scalars act on every K-flat object of `K(A)` through the unit object. -/
theorem smul_id_eq_leftUnitor_kFlat
    (hA : ∀ (a : R) (X Y : A), (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y))
    (a : R) (X : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ _)) ▷ X) ≫ (λ_ X).hom := by
  ext1
  have h1 : ((a • 𝟙 X : X ⟶ X)).hom = a • 𝟙 X.obj := rfl
  have h2 : ((a • 𝟙 (𝟙_ (kFlatObjects (curriedTensor A)).FullSubcategory) :
      𝟙_ (kFlatObjects (curriedTensor A)).FullSubcategory ⟶ _)).hom =
      a • 𝟙 (𝟙_ (HomotopyCategory A (ComplexShape.up ℤ))) := rfl
  simp only [ObjectProperty.FullSubcategory.comp_hom, h1]
  exact (smul_id_eq_leftUnitor_homotopy A R hA a X.obj).trans (by rw [← h2]; rfl)

variable [HasDerivedCategory.{w} A]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- **Scalars act on every object of `D(A)` through the unit object** of the derived tensor
product. -/
theorem smul_id_eq_leftUnitor_derived
    (hA : ∀ (a : R) (X Y : A), (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y))
    (a : R) (X : DerivedCategory A) :
    letI := derivedMonoidal A hres
    a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ _)) ▷ X) ≫ (λ_ X).hom := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := derivedMonoidal A hres
  let := kFlatQMonoidal A hres
  have : (kFlatQ (curriedTensor A)).EssSurj :=
    Localization.essSurj _ (kFlatQuasiIso (curriedTensor A))
  exact MonoidalCategory.smul_id_eq_leftUnitor_of_iso
    ((kFlatQ (curriedTensor A)).objObjPreimageIso X) a
    (MonoidalCategory.smul_id_eq_leftUnitor_map _ a _ (smul_id_eq_leftUnitor_kFlat A R hA a _))

/-- **The derived tensor product is linear in its left variable.** -/
theorem derived_smul_id_whiskerRight
    (hA : ∀ (a : R) (X Y : A), (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y))
    (a : R) (X Y : DerivedCategory A) :
    letI := derivedMonoidal A hres
    (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y) :=
  let := derivedMonoidal A hres
  MonoidalCategory.smul_id_whiskerRight_of_forall R (smul_id_eq_leftUnitor_derived A R hres hA)
    a X Y

/-- **The derived tensor product is linear in its right variable.** -/
theorem derived_whiskerLeft_smul_id
    (hA : ∀ (a : R) (X Y : A), (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y))
    (a : R) (X Y : DerivedCategory A) :
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    X ◁ (a • 𝟙 Y) = a • 𝟙 (X ⊗ Y) :=
  let := derivedMonoidal A hres
  let := derivedSymmetric A hres
  MonoidalCategory.whiskerLeft_smul_id_of_forall (smul_id_eq_leftUnitor_derived A R hres hA)
    a X Y

end CochainComplex.KFlatMonoidal
