module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorTensorCommShift
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctorOnModels
public import StacksFrontier.Homology.KFlat.BifunctorComparisonOneVariable
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoInv
public import StacksFrontier.CategoryTheory.Shift.CommShiftCompOfEqData

/-!
# The K-flat comparison of the derived tensor product is shift-compatible

Let `A` be an abelian braided monoidal category satisfying the hypotheses under which
`CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(A)` with the derived tensor product of
[Stacks, Tag 0FPT].  `CochainComplex.KFlatMonoidal.derivedTensorIso` is the comparison

`Q K ⊗ Q L ≅ Q (K ⊗ L)`

at a pair of K-flat cochain complexes -- the statement that for K-flat representatives the derived
tensor product *is* the total tensor product of complexes.  This file proves that that comparison
commutes with the shift, in each variable separately.

## Main results

* `CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso_commShift₂`: **the identification of the
  monoidal and the bifunctor derived tensor products is shift-compatible in both variables.**
* `CochainComplex.KFlatMonoidal.derivedTensorSecondIso`, with `derivedTensorSecondIso_hom_app` and
  `derivedTensorSecondIso_commShift`: **the comparison at a fixed left K-flat first factor, as an
  isomorphism of functors on the K-flat complexes, with `derivedTensorIso` for its components and
  compatible with the shift.**
* `CochainComplex.KFlatMonoidal.derivedTensorFirstIso`, with `derivedTensorFirstIso_hom_app` and
  `derivedTensorFirstIso_commShift`: the mirror at a fixed K-flat second factor, on the *left*
  K-flat complexes.

## References

* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
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

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

/-! ### The identification of the two derived tensor products -/

include hres in
/-- **The identification of the tensor product of `derivedMonoidal` with the derived tensor
bifunctor is compatible with the shifts in both variables.** -/
theorem derivedMonoidalTensorIso_commShift₂ :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    letI := derivedMonoidal_commShift₂Int A hres
    NatTrans.CommShift₂Int (derivedMonoidalTensorIso A hres).hom := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  let := derivedMonoidal_commShift₂Int A hres
  have := Functor.CommShift₂.ofIsoInt_commShift₂ (derivedMonoidalTensorIso A hres).symm
  exact NatTrans.CommShift₂.of_iso_invInt (derivedMonoidalTensorIso A hres).symm

/-! ### The comparison at a fixed first factor -/

include hres in
/-- **The comparison `derivedTensorIso` at a fixed left K-flat first factor, as an isomorphism of
functors on the K-flat complexes.**  It is the identification of the two derived tensor products
in the second variable, followed by the comparison of [Stacks, Tag 06YU] in the shape
`CochainComplex.KFlatBifunctor.comparisonSecond` gives it. -/
def derivedTensorSecondIso (K : CochainComplex A ℤ) (hK : KFlatLeft (curriedTensor A) K) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    kFlatComplexQ (curriedTensor A) ⋙ tensorLeft (DerivedCategory.Q.obj K) ≅
      (kFlatComplexes (curriedTensor A)).ι ⋙
        ((totalBifunctor (curriedTensor A)).obj K ⋙ DerivedCategory.Q) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  letI := derivedMonoidal A hres
  Functor.isoWhiskerLeft (kFlatComplexQ (curriedTensor A))
      ((derivedMonoidalTensorIso A hres).app (DerivedCategory.Q.obj K)) ≪≫
    comparisonSecond (curriedTensor A) K hK

include hres in
/-- **The components of `derivedTensorSecondIso` are `derivedTensorIso`**, at a first factor which
is two-sided K-flat. -/
theorem derivedTensorSecondIso_hom_app {K : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K)
    (L : (kFlatComplexes (curriedTensor A)).FullSubcategory) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    (derivedTensorSecondIso A hres K (kFlatLeft_of_kFlat A hK)).hom.app L =
      (derivedTensorIso A hres hK L.property).hom := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  dsimp only [derivedTensorSecondIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.app_hom]
  rw [comparisonSecond_hom_app, derivedMonoidalTensorIso_hom]
  exact derivedTensorCompare_comp_comparison A hres hK L.property

include hres in
/-- **The comparison `derivedTensorIso` is compatible with the shift in the second variable.** -/
theorem derivedTensorSecondIso_commShift (K : CochainComplex A ℤ)
    (hK : KFlatLeft (curriedTensor A) K) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    letI := fun M : DerivedCategory A => derivedMonoidal_tensorLeft_commShift A hres M
    NatTrans.CommShift (derivedTensorSecondIso A hres K hK).hom ℤ := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  let := derivedMonoidal_commShift₂Int A hres
  have := derivedMonoidalTensorIso_commShift₂ A hres
  have : NatTrans.CommShift
      ((derivedMonoidalTensorIso A hres).app (DerivedCategory.Q.obj K)).hom ℤ :=
    NatTrans.CommShift₂.commShift_app (τ := (derivedMonoidalTensorIso A hres).hom)
      (h := CommShift₂Setup.int) (DerivedCategory.Q.obj K)
  dsimp only [derivedTensorSecondIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  have hτ : NatTrans.CommShift
      ((kFlatComplexQ (curriedTensor A)).whiskerLeft
        ((derivedMonoidalTensorIso A hres).app (DerivedCategory.Q.obj K)).hom) ℤ := inferInstance
  exact NatTrans.commShift_comp_of_eq_data _ _ hτ
    (comparisonSecond_commShift (curriedTensor A) K hK)

/-! ### The comparison at a fixed second factor -/

include hres in
/-- **The comparison `derivedTensorIso` at a fixed K-flat second factor, as an isomorphism of
functors on the left K-flat complexes.**  It is the identification of the two derived tensor
products in the first variable, followed by `CochainComplex.KFlatBifunctor.comparisonFirst`. -/
def derivedTensorFirstIso (L : CochainComplex A ℤ) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    kFlatComplexQLeft (curriedTensor A) ⋙ tensorRight (DerivedCategory.Q.obj L) ≅
      (kFlatComplexesLeft (curriedTensor A)).ι ⋙
        ((totalBifunctor (curriedTensor A)).flip.obj L ⋙ DerivedCategory.Q) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  letI := derivedMonoidal A hres
  Functor.isoWhiskerLeft (kFlatComplexQLeft (curriedTensor A))
      ((Functor.CommShift₂.flipIso (derivedMonoidalTensorIso A hres)).app
        (DerivedCategory.Q.obj L)) ≪≫
    comparisonFirst (curriedTensor A) L hL

include hres in
/-- **The components of `derivedTensorFirstIso` are `derivedTensorIso`**, at a first factor which
is two-sided K-flat. -/
theorem derivedTensorFirstIso_hom_app {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    (derivedTensorFirstIso A hres L hL).hom.app ⟨K, kFlatLeft_of_kFlat A hK⟩ =
      (derivedTensorIso A hres hK hL).hom := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  dsimp only [derivedTensorFirstIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.app_hom,
    Functor.CommShift₂.flipIso, Functor.mapIso_hom, flipFunctor_map_app_app]
  rw [comparisonFirst_hom_app, derivedMonoidalTensorIso_hom]
  exact derivedTensorCompare_comp_comparison A hres hK hL

include hres in
/-- **The comparison `derivedTensorIso` is compatible with the shift in the first variable.** -/
theorem derivedTensorFirstIso_commShift (L : CochainComplex A ℤ)
    (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    letI := fun M : DerivedCategory A => derivedMonoidal_tensorRight_commShift A hres M
    NatTrans.CommShift (derivedTensorFirstIso A hres L hL).hom ℤ := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  let := derivedMonoidal_commShift₂Int A hres
  have := derivedMonoidalTensorIso_commShift₂ A hres
  have : NatTrans.CommShift
      ((Functor.CommShift₂.flipIso (derivedMonoidalTensorIso A hres)).app
        (DerivedCategory.Q.obj L)).hom ℤ :=
    NatTrans.CommShift₂.commShift_flipApp (τ := (derivedMonoidalTensorIso A hres).hom)
      (h := CommShift₂Setup.int) (DerivedCategory.Q.obj L)
  dsimp only [derivedTensorFirstIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  have hτ : NatTrans.CommShift
      ((kFlatComplexQLeft (curriedTensor A)).whiskerLeft
        ((Functor.CommShift₂.flipIso (derivedMonoidalTensorIso A hres)).app
          (DerivedCategory.Q.obj L)).hom) ℤ := inferInstance
  exact NatTrans.commShift_comp_of_eq_data _ _ hτ
    (comparisonFirst_commShift (curriedTensor A) L hL)

end CochainComplex.KFlatMonoidal

end
