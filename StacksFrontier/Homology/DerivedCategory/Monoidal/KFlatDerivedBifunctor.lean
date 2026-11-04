module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# The tensor product of the derived category is the derived tensor bifunctor

Let `A` be an abelian category with a braided monoidal structure whose tensor product is
additive in each variable, suppose the total complexes of the tensor double complexes exist,
and suppose every cochain complex of objects of `A` receives a quasi-isomorphism from a K-flat
one.  Then `D(A)` carries the monoidal structure
`CochainComplex.KFlatMonoidal.derivedMonoidal`, obtained by localizing twice, and the generic
K-flat machinery of `CochainComplex.KFlatBifunctor` separately produces the derived bifunctor
`CochainComplex.KFlatBifunctor.derivedBifunctor` of the tensor product.

This file identifies the two: `derivedMonoidalTensorIso` is an isomorphism of bifunctors
between the curried tensor product of `derivedMonoidal` and `derivedBifunctor`.

## Main definitions

* `CochainComplex.KFlatMonoidal.derivedTensorSource`: the bifunctor on the K-flat objects of
  `K(A)` that both sides descend.
* `CochainComplex.KFlatMonoidal.derivedLocalizedTensor`: Mathlib's localized tensor
  bifunctor of the second localization, read at `D(A)` rather than at the type synonym
  `CategoryTheory.LocalizedMonoidal`.

## Main results

* `CochainComplex.KFlatMonoidal.curriedTensor_derivedMonoidal`: the curried tensor product of
  `derivedMonoidal` is definitionally `derivedLocalizedTensor`.
* `CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso`,
  `CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso`: the curried tensor product of
  `derivedMonoidal` is isomorphic to `derivedBifunctor`.

## Implementation notes

The two liftings are supplied by hand: Mathlib states its instance at the type synonym
`CategoryTheory.LocalizedMonoidal`, which instance search does not see through.

The two localizations are instance arguments rather than derived from the resolution hypothesis
inside each declaration, so that `derivedLocalizedTensor` is the same term as the tensor product of
`derivedMonoidal`.

## References

* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

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

attribute [local instance] homotopyMonoidal homotopyBraided

/-! ### The K-flat objects are left-K-flat -/

section Inclusion

variable [BraidedCategory (CochainComplex A ℤ)]

/-- The K-flat objects of `K(A)` are left-K-flat. -/
theorem kFlatObjects_le_kFlatObjectsLeft :
    kFlatObjects (curriedTensor A) ≤ kFlatObjectsLeft (curriedTensor A) :=
  fun _ hX ↦ kFlatLeft_of_kFlat A hX

/-- If every complex receives a quasi-isomorphism from a K-flat one, then every complex receives a
quasi-isomorphism from a left-K-flat one. -/
theorem exists_kFlatLeft_quasiIso
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlat (curriedTensor A) P ∧ QuasiIso f)
    (G : CochainComplex A ℤ) :
    ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft (curriedTensor A) P ∧ QuasiIso f := by
  obtain ⟨P, f, hP, hf⟩ := hres G
  exact ⟨P, f, kFlatLeft_of_kFlat A hP, hf⟩

end Inclusion

/-! ### The two descents of one bifunctor -/

section Comparison

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]

/-- The bifunctor on the K-flat objects of `K(A)` that both the localized monoidal structure
and the generic derived bifunctor descend: the tensor product of the full monoidal
subcategory of K-flat objects, pushed into `D(A)`. -/
abbrev derivedTensorSource : (kFlatObjects (curriedTensor A)).FullSubcategory ⥤
    (kFlatObjects (curriedTensor A)).FullSubcategory ⥤ DerivedCategory A :=
  curriedTensor ((kFlatObjects (curriedTensor A)).FullSubcategory) ⋙
    (Functor.whiskeringRight _ _ _).obj (kFlatQ (curriedTensor A))

/-- Mathlib's localized tensor bifunctor for the second localization, read at `D(A)` rather
than at the type synonym `CategoryTheory.LocalizedMonoidal`. -/
abbrev derivedLocalizedTensor :
    DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A :=
  Localization.Monoidal.tensorBifunctor (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A))
    (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))

/-- `derivedLocalizedTensor` lifts `derivedTensorSource` along `kFlatQ` in each variable. -/
@[instance_reducible]
def derivedLocalizedTensorLifting :
    Localization.Lifting₂ (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (derivedTensorSource A) (derivedLocalizedTensor A) :=
  inferInstanceAs (Localization.Lifting₂
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A)) (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A)) (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (curriedTensor _ ⋙ (Functor.whiskeringRight _ _
      (CategoryTheory.LocalizedMonoidal (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))).obj
      (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))))
    (Localization.Monoidal.tensorBifunctor (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))))

/-- `derivedBifunctor` is a lifting of `derivedTensorSource` along `kFlatQ` in each variable, the
restriction to the K-flat objects of its lifting along `kFlatQLeft` in the first variable. -/
@[instance_reducible]
def derivedBifunctorLiftingKFlatQ :
    Localization.Lifting₂ (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (derivedTensorSource A) (derivedBifunctor (curriedTensor A)) where
  iso := ((Functor.whiskeringLeft _ _ _).obj
      (ObjectProperty.ιOfLE (kFlatObjects_le_kFlatObjectsLeft A))).mapIso
    (Localization.Lifting₂.iso (kFlatQLeft (curriedTensor A)) (kFlatQ (curriedTensor A))
      (kFlatQuasiIsoLeft (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (kFlatToDerived (curriedTensor A)) (derivedBifunctor (curriedTensor A)))

attribute [local instance] derivedLocalizedTensorLifting derivedBifunctorLiftingKFlatQ

/-- **The localized tensor product of `D(A)` is isomorphic to the derived tensor bifunctor.** -/
def derivedLocalizedTensorIso :
    derivedLocalizedTensor A ≅ derivedBifunctor (curriedTensor A) :=
  Localization.lift₂NatIso (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (derivedTensorSource A) (derivedTensorSource A) (derivedLocalizedTensor A)
    (derivedBifunctor (curriedTensor A)) (Iso.refl _)

end Comparison

/-! ### The comparison at the monoidal structure of Tag 0FPT -/

section Monoidal

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **The curried tensor product of `derivedMonoidal` is definitionally
`derivedLocalizedTensor`.** -/
theorem curriedTensor_derivedMonoidal :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    @curriedTensor (DerivedCategory A) _ (derivedMonoidal A hres) =
      derivedLocalizedTensor A := rfl

include hres in
/-- **The tensor product of the monoidal derived category of Tag 0FPT is the derived tensor
bifunctor of Tag 06YU.** -/
def derivedMonoidalTensorIso :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    @curriedTensor (DerivedCategory A) _ (derivedMonoidal A hres) ≅
      derivedBifunctor (curriedTensor A) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  eqToIso (curriedTensor_derivedMonoidal A hres) ≪≫ derivedLocalizedTensorIso A

end Monoidal

end CochainComplex.KFlatMonoidal

end
