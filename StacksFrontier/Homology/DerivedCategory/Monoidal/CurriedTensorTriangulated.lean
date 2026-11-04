module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorCommShift

/-!
# The tensor product of `D(A)` is exact in each variable

Let `A` be an abelian braided monoidal category satisfying the hypotheses under which
`CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(A)` with the monoidal structure of
[Stacks, Tag 0FPT].  This file records that `K ⊗ -` and `- ⊗ L` on `D(A)` are exact functors of
triangulated categories, at the commutation with the shift of
`CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_commShift` and
`CochainComplex.KFlatMonoidal.derivedMonoidal_tensorRight_commShift`.

The exactness itself is that of the derived tensor bifunctor,
`CochainComplex.KFlatBifunctor.derivedBifunctor_isTriangulated_obj` and
`CochainComplex.KFlatBifunctor.derivedBifunctor_isTriangulated_flipObj`; those are stated at the
bifunctor, and what is done here is to move them onto the monoidal spelling, which is the spelling
a dévissage of a morphism of bifunctors consumes.

## Main results

* `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_isTriangulated` and
  `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorRight_isTriangulated`: **`tensorLeft K` and
  `tensorRight L` for the Tag 0FPT monoidal structure are exact.**

## Implementation notes

The transport is `CategoryTheory.Functor.isTriangulated_of_iso` along the same isomorphism
`CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso` that
`CurriedTensorCommShift.lean` transports the commutation with the shift along, so the two
transports agree and no second commutation is introduced.

Its shift compatibility is `CategoryTheory.Functor.CommShift.ofIso_compatibility`, and it has to
be seated with its type written out.  The commutation with the shift on the monoidal side is the
one `CategoryTheory.Functor.CommShift.ofIso` produces, but the statements below seat it through
`derivedMonoidal_tensorLeft_commShift`, whose body is that term behind a `def`; instance search
does not unfold the `def`, so the ascription is what tells the elaborator that the two are the
same structure.  The two `letI`s for the K-flat localizations and the one for `derivedMonoidal`
repeat the preamble of `CurriedTensorCommShift.lean` for the reason recorded there: those terms
are built from `hres` inside each declaration, so a statement about them must build the same
terms the same way.

As in `CurriedTensorCommShift.lean`, the source of the transport for `tensorRight` has to be
written out with the `show ... from` ascription, because `CommShift₂`'s flipped field is indexed
at the `.flip.obj` spelling while `CategoryTheory.flipFunctor` produces another.

## References

* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 05R7](https://stacks.math.columbia.edu/tag/05R7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal homotopyBraided

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **`K ⊗ -` on `D(A)` is exact**, for the monoidal structure of Tag 0FPT and the commutation
with the shift of `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_commShift`.  The
exactness is that of `CochainComplex.KFlatBifunctor.derivedBifunctor` in its second variable,
transported along `CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso`. -/
theorem derivedMonoidal_tensorLeft_isTriangulated (K : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    letI := derivedMonoidal_tensorLeft_commShift A hres K
    (tensorLeft K).IsTriangulated := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  let := derivedMonoidal_tensorLeft_commShift A hres K
  let : NatTrans.CommShift ((derivedMonoidalTensorIso A hres).app K).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility _ ℤ
  exact Functor.isTriangulated_of_iso ((derivedMonoidalTensorIso A hres).app K).symm

include hres in
/-- **`- ⊗ L` on `D(A)` is exact**, for the monoidal structure of Tag 0FPT and the commutation
with the shift of `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorRight_commShift`.  The
mirror of `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_isTriangulated`. -/
theorem derivedMonoidal_tensorRight_isTriangulated (L : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    letI := derivedMonoidal_tensorRight_commShift A hres L
    (tensorRight L).IsTriangulated := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  let := derivedMonoidal_tensorRight_commShift A hres L
  let e : (derivedBifunctor (curriedTensor A)).flip.obj L ≅ tensorRight L :=
    (((flipFunctor _ _ _).mapIso (derivedMonoidalTensorIso A hres)).app L).symm
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility _ ℤ
  exact Functor.isTriangulated_of_iso e

end CochainComplex.KFlatMonoidal

end
