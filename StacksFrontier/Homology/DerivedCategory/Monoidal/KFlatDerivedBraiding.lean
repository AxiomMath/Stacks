module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# The commutativity constraint of the derived category on K-flat complexes

`CochainComplex.KFlatMonoidal.derivedTensorIso` identifies the tensor product of
`CochainComplex.KFlatMonoidal.derivedMonoidal` at the images of two K-flat complexes with the
image of their total tensor product.  This file records the remaining clause of Stacks Tag
0FPT for the commutativity constraint: **the braiding of `D(A)` is, through that comparison,
the braiding of `Comp(A)`** — for complexes of modules, the Koszul symmetry.

## Main results

* `CochainComplex.KFlatMonoidal.homotopy_braiding_hom`: the braiding of `K(A)` at the images of
  two complexes is the braiding of `Comp(A)`, conjugated by the tensorator of the homotopy
  localization.
* `CochainComplex.KFlatMonoidal.derived_braiding_hom`: the same one localization up, for the
  braiding of `D(A)` at the images of two K-flat objects of `K(A)`.
* `CochainComplex.KFlatMonoidal.ι_map_braiding`: the braiding of the full monoidal subcategory
  of K-flat objects is the ambient one.

## Implementation notes

`derivedMonoidal` is the monoidal localization of the K-flat objects of `K(A)`, which is itself
the monoidal localization of `Comp(A)` at the homotopy equivalences, so each of the two
statements above is `CategoryTheory.Localization.Monoidal.β_hom_app` at one of those two
localizations.  Both are stated with the monoidal and symmetric structures supplied explicitly:
neither is an instance, and `D(A)` carries more than one monoidal structure.

## References

* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [HasDerivedCategory.{w} A] [SymmetricCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

attribute [local instance] homotopyMonoidal homotopySymmetric

attribute [local implicit_reducible]
  CochainComplex.KFlatBifunctor.KFlat CategoryTheory.LocalizedMonoidal
  CategoryTheory.Localization.Monoidal.toMonoidalCategory
  CategoryTheory.Localization.instCategoryLocalizedMonoidal
  CochainComplex.KFlatMonoidal.homotopyMonoidal CochainComplex.KFlatMonoidal.derivedMonoidal

omit [HasDerivedCategory A] in
/-- The braiding of `K(A)` at the images of two complexes. -/
theorem homotopy_braiding_hom (X Y : CochainComplex A ℤ) :
    (β_ ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X)
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)).hom =
      (homotopyMu A X Y).hom ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (β_ X Y).hom ≫
          (homotopyMu A Y X).inv :=
  Localization.Monoidal.β_hom_app (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A)) X Y

omit [HasDerivedCategory A] in
/-- The braiding of the full monoidal subcategory of K-flat objects of `K(A)` is the braiding
of `K(A)`. -/
theorem ι_map_braiding (X Y : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    (kFlatObjects (curriedTensor A)).ι.map (β_ X Y).hom = (β_ X.1 Y.1).hom :=
  rfl

/-- The braiding of `D(A)` at the images of two K-flat objects of `K(A)`. -/
theorem derived_braiding_hom (X Y : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    (β_ ((DerivedCategory.Qh (C := A)).obj X.1)
          ((DerivedCategory.Qh (C := A)).obj Y.1)).hom =
      (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
            (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) X Y).hom ≫
        (kFlatQ (curriedTensor A)).map (β_ X Y).hom ≫
          (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
            (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) Y X).inv :=
  let := kFlatQ_isLocalization (curriedTensor A) hres
  Localization.Monoidal.β_hom_app (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) X Y

end CochainComplex.KFlatMonoidal

end
