module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# An exact monoidal functor preserving K-flatness is monoidal on derived categories

Let `A` and `B` be monoidal abelian categories whose tensor products commute with the
coproducts occurring in a total complex, so that `CochainComplex A ℤ` and `CochainComplex B ℤ`
both carry the total tensor product of `Mathlib.Algebra.Homology.Monoidal`, and assume that
every cochain complex on each side receives a quasi-isomorphism from a K-flat one, so that
`CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(A)` and `D(B)` with the derived tensor
product.  Let `F : A ⥤ B` be an additive, exact, **monoidal** functor which carries K-flat
complexes to K-flat complexes.  This file proves that

  `F.mapDerivedCategory : D(A) ⥤ D(B)`

is a **monoidal** functor for those two derived tensor products.

## Main definitions

* `CategoryTheory.Functor.mapHomotopyCategoryMonoidal`: **`F.mapHomotopyCategory` is monoidal**
  for `CochainComplex.KFlatMonoidal.homotopyMonoidal` on each side.
* `CategoryTheory.Functor.kFlatLift`, with its monoidal structure
  `CategoryTheory.Functor.kFlatLiftMonoidal`: `F.mapHomotopyCategory`, restricted to the K-flat
  objects of the two homotopy categories.
* `CategoryTheory.Functor.mapDerivedCategoryMonoidal`: **`F.mapDerivedCategory` is monoidal**
  for `CochainComplex.KFlatMonoidal.derivedMonoidal` on each side.

## Implementation notes

As in `CochainComplex.KFlatMonoidal`, none of the monoidal structures below is an instance: they
are seated by `letI` where they are used, so that no diamond is introduced for categories
already carrying a monoidal structure. Each structure is first stated at the type synonyms
`CochainComplex.KFlatMonoidal.HomotopyLocalized` and
`CochainComplex.KFlatMonoidal.DerivedLocalized`, which carry the localized monoidal structures,
and then read at the plain `HomotopyCategory` and `DerivedCategory` spellings.

## References

* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN), K-flatness.
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT), the derived tensor
  product as a monoidal structure.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v₁ u₁ v₂ u₂

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ B), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : A ⥤ B) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F]

/-! ### The descent to the homotopy categories -/

/-- `F.mapHomotopyCategory (ComplexShape.up ℤ)`, retyped between the type synonyms on which the
localized monoidal structures of the two homotopy categories live. -/
abbrev Functor.mapHomotopyCategoryLocalized :
    HomotopyLocalized A ⥤ HomotopyLocalized B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ)

/-- The lifting of `F.mapHomotopyCategory c` along the homotopy localization,
`CategoryTheory.Functor.mapHomotopyCategoryFactors` read at the type-synonym spelling of the
localized monoidal structure. -/
@[instance_reducible]
def Functor.mapHomotopyCategoryLifting :
    Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit A)))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Localization.Monoidal.toMonoidalCategory
          (HomotopyCategory.quotient B (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
          (Iso.refl (homotopyUnit B)))
      (Functor.mapHomotopyCategoryLocalized F) :=
  ⟨F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)⟩

/-- **`F.mapHomotopyCategory` is a monoidal functor**, stated at the type synonyms carrying the
localized monoidal structures. -/
@[instance_reducible]
def Functor.mapHomotopyCategoryLocalizedMonoidal :
    (Functor.mapHomotopyCategoryLocalized F).Monoidal :=
  letI := Functor.mapHomotopyCategoryLifting F
  Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A)))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Functor.mapHomotopyCategoryLocalized F)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit B)))

/-- **`F.mapHomotopyCategory (ComplexShape.up ℤ) : K(A) ⥤ K(B)` is a monoidal functor** for the
monoidal structure `CochainComplex.KFlatMonoidal.homotopyMonoidal` on each side. -/
@[instance_reducible]
def Functor.mapHomotopyCategoryMonoidal :
    letI := homotopyMonoidal A
    letI := homotopyMonoidal B
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).Monoidal :=
  Functor.mapHomotopyCategoryLocalizedMonoidal F

/-! ### The K-flat objects of the homotopy categories -/

variable (hF : ∀ K : CochainComplex A ℤ, KFlat (curriedTensor A) K →
  KFlat (curriedTensor B) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

/-- `F.mapHomotopyCategory (ComplexShape.up ℤ)`, restricted to the K-flat objects of the two
homotopy categories. -/
def Functor.kFlatLift :
    (kFlatObjects (curriedTensor A)).FullSubcategory ⥤
      (kFlatObjects (curriedTensor B)).FullSubcategory :=
  (kFlatObjects (curriedTensor B)).lift
    ((kFlatObjects (curriedTensor A)).ι ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun X => hF X.obj.as X.property)

/-- **`CategoryTheory.Functor.kFlatLift` is a monoidal functor** between the full monoidal
subcategories of K-flat objects. -/
@[instance_reducible]
def Functor.kFlatLiftMonoidal :
    letI := homotopyMonoidal A
    letI := homotopyMonoidal B
    (Functor.kFlatLift F hF).Monoidal :=
  letI := homotopyMonoidal A
  letI := homotopyMonoidal B
  letI := Functor.mapHomotopyCategoryMonoidal F
  ObjectProperty.liftMonoidal _ _ _

/-! ### The descent to the derived categories -/

section Derived

variable [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    KFlat (curriedTensor B) P ∧ QuasiIso f)

/-- `F.mapDerivedCategory`, retyped between the type synonyms on which the localized monoidal
structures of the two derived categories live. -/
abbrev Functor.mapDerivedCategoryLocalized :
    DerivedLocalized A hresA ⥤ DerivedLocalized B hresB :=
  F.mapDerivedCategory

/-- The lifting of `F.mapDerivedCategory` along the K-flat localization,
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` whiskered by the inclusion of the K-flat
objects of `K(A)` and read at the type-synonym spelling of the localized monoidal structure. -/
@[instance_reducible]
def Functor.mapDerivedCategoryLifting :
    letI := kFlatQ_isLocalization (curriedTensor A) hresA
    letI := kFlatQ_isLocalization (curriedTensor B) hresB
    Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
      (kFlatQuasiIso (curriedTensor A))
      (Functor.kFlatLift F hF ⋙
        Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor B))
          (kFlatQuasiIso (curriedTensor B))
          (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _))))
      (Functor.mapDerivedCategoryLocalized F hresA hresB) :=
  ⟨isoWhiskerLeft (kFlatObjects (curriedTensor A)).ι F.mapDerivedCategoryFactorsh⟩

/-- **`F.mapDerivedCategory` is a monoidal functor**, stated at the type synonyms carrying the
localized monoidal structures. -/
@[instance_reducible]
def Functor.mapDerivedCategoryLocalizedMonoidal :
    (Functor.mapDerivedCategoryLocalized F hresA hresB).Monoidal :=
  letI := kFlatQ_isLocalization (curriedTensor A) hresA
  letI := kFlatQ_isLocalization (curriedTensor B) hresB
  letI := Functor.kFlatLiftMonoidal F hF
  letI := Functor.mapDerivedCategoryLifting F hF hresA hresB
  Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A))
    (Functor.mapDerivedCategoryLocalized F hresA hresB)
    (Functor.kFlatLift F hF ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor B))
        (kFlatQuasiIso (curriedTensor B))
        (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _))))

/-- **An exact monoidal functor preserving K-flatness is monoidal on derived categories:**

`F.mapDerivedCategory : D(A) ⥤ D(B)`

is a monoidal functor for the derived tensor product
`CochainComplex.KFlatMonoidal.derivedMonoidal` on each side. The structure is strong: its
tensorator is an isomorphism. -/
@[instance_reducible]
def Functor.mapDerivedCategoryMonoidal :
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    F.mapDerivedCategory.Monoidal :=
  Functor.mapDerivedCategoryLocalizedMonoidal F hF hresA hresB

end Derived

end CategoryTheory

end
