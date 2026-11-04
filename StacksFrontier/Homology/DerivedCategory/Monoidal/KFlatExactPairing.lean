module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# An exact pairing of K-flat complexes descends to the derived category

Let `A` be a monoidal abelian category whose derived category carries the derived tensor
product `CochainComplex.KFlatMonoidal.derivedMonoidal`, the localization of the K-flat objects
of the homotopy category at the quasi-isomorphisms. If two K-flat complexes `P` and `P'` form an
exact pairing in the monoidal category of complexes, their images in `D(A)` form an exact pairing
for the derived tensor product: the pairing is carried to the homotopy category by the monoidal
localization functor, lifted into the full monoidal subcategory of K-flat objects, and carried
to `D(A)` by the monoidal localization functor of the K-flat objects.

This is how a dualizable complex, for instance a strictly perfect complex with its dual complex
(Stacks 0FPR), gives a dualizable object of the derived category.

## Main definitions

* `CochainComplex.KFlatMonoidal.exactPairingQ`: the exact pairing of `Q P` and `Q P'`.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe w v u

namespace CochainComplex.KFlatMonoidal

attribute [local instance] homotopyMonoidal homotopyBraided

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory (CochainComplex A ℤ)] [HasDerivedCategory.{w} A]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- **An exact pairing of K-flat complexes descends to the derived category.** If `P` and `P'`
are K-flat and `P ⊣ P'` is an exact pairing of complexes, then `Q P ⊣ Q P'` is an exact pairing
of `D(A)` for the derived tensor product. -/
@[instance_reducible]
def exactPairingQ {P P' : CochainComplex A ℤ} (hP : KFlat (curriedTensor A) P)
    (hP' : KFlat (curriedTensor A) P') [ExactPairing P P'] :
    letI := derivedMonoidal A hres
    ExactPairing (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj P') := by
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  let q := Localization.Monoidal.toMonoidalCategory
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ)) (Iso.refl (homotopyUnit A))
  letI hq : ExactPairing (q.obj P) (q.obj P') := ExactPairing.map q P P'
  let X : (kFlatObjects (curriedTensor A)).FullSubcategory := ⟨q.obj P, hP⟩
  let Y : (kFlatObjects (curriedTensor A)).FullSubcategory := ⟨q.obj P', hP'⟩
  letI hXY : ExactPairing X Y :=
    @ExactPairing.ofFullyFaithful _ _ _ _ _ _ (kFlatObjects (curriedTensor A)).ι _ _ _ X Y hq
  let d := Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A)) (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
  letI hd : ExactPairing (d.obj X) (d.obj Y) := ExactPairing.map d X Y
  exact @exactPairingCongr _ _ (derivedMonoidal A hres) _ _ _ _ hd
    (derivedQIso A P).symm (derivedQIso A P').symm

end CochainComplex.KFlatMonoidal

end
