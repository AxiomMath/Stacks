module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal

/-!
# A functor on derived categories computed on K-flat complexes by a monoidal functor is monoidal

`CategoryTheory.Functor.mapDerivedCategoryMonoidal` makes `F.mapDerivedCategory` monoidal for an
*exact* monoidal functor `F : A ⥤ B` preserving K-flatness. Exactness is used there only to have
the functor `F.mapDerivedCategory` and its factorization through the localization of the K-flat
objects. This file isolates what the descent actually consumes: any functor
`LF : D(A) ⥤ D(B)` together with an isomorphism

  `kFlatQ_A ⋙ LF ≅ kFlatLift F ⋙ kFlatQ_B`,

identifying `LF` on K-flat complexes with the degreewise application of `F`, is monoidal. This
applies to left derived functors such as the derived pullback `Lf^*` of a morphism of ringed
spaces, which are computed on K-flat complexes by the underlying (not exact) functor.

## Main definitions

* `CategoryTheory.Functor.kFlatComputedMonoidal` — the monoidal structure on `LF`, for the derived
  tensor product `CochainComplex.KFlatMonoidal.derivedMonoidal` on each side.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
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
  (hF : ∀ K : CochainComplex A ℤ, KFlat (curriedTensor A) K →
    KFlat (curriedTensor B) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    KFlat (curriedTensor B) P ∧ QuasiIso f)
  (LF : DerivedCategory A ⥤ DerivedCategory B)
  (e : kFlatQ (curriedTensor A) ⋙ LF ≅ Functor.kFlatLift F hF ⋙ kFlatQ (curriedTensor B))

/-- `LF`, retyped between the type synonyms carrying the localized monoidal structures. -/
abbrev Functor.kFlatComputedLocalized : DerivedLocalized A hresA ⥤ DerivedLocalized B hresB := LF

/-- The lifting of `LF` along the K-flat localization supplied by `e`. -/
@[instance_reducible]
def Functor.kFlatComputedLifting :
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
      (Functor.kFlatComputedLocalized hresA hresB LF) :=
  ⟨e⟩

/-- **A functor computed on K-flat complexes by a monoidal functor is monoidal**, at the type
synonyms carrying the localized monoidal structures: this is
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` applied to the K-flat localization. -/
@[instance_reducible]
def Functor.kFlatComputedLocalizedMonoidal :
    (Functor.kFlatComputedLocalized hresA hresB LF).Monoidal :=
  letI := kFlatQ_isLocalization (curriedTensor A) hresA
  letI := kFlatQ_isLocalization (curriedTensor B) hresB
  letI := Functor.kFlatLiftMonoidal F hF
  letI := Functor.kFlatComputedLifting F hF hresA hresB LF e
  Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A))
    (Functor.kFlatComputedLocalized hresA hresB LF)
    (Functor.kFlatLift F hF ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor B))
        (kFlatQuasiIso (curriedTensor B))
        (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _))))

/-- **A functor on derived categories computed on K-flat complexes by a monoidal functor
preserving K-flatness is monoidal**, for the derived tensor product
`CochainComplex.KFlatMonoidal.derivedMonoidal` on each side. The structure is strong. -/
@[instance_reducible]
def Functor.kFlatComputedMonoidal :
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    LF.Monoidal :=
  Functor.kFlatComputedLocalizedMonoidal F hF hresA hresB LF e

end CategoryTheory

end
