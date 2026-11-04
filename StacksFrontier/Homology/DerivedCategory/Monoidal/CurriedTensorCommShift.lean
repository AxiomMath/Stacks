module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor
public import StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectShift

/-!
# The tensor product of `D(A)` commutes with the shift in each variable

Let `A` be an abelian braided monoidal category satisfying the hypotheses under which
`CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(A)` with the monoidal structure of
[Stacks, Tag 0FPT]. This file transports the two-variable shift coherence of the derived tensor
bifunctor onto that monoidal structure: each `K ⊗ -` and each `- ⊗ L` on `D(A)` commutes with
the shift by `ℤ`.

The consequence this was built for is that a shift of an invertible object of `D(A)` is
invertible, which is `CategoryTheory.MonoidalCategory.IsInvertible.shift` instantiated here.

## Main results

* `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_commShift` and
  `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorRight_commShift`: `tensorLeft K` and
  `tensorRight L` for the Tag 0FPT monoidal structure commute with the shift by `ℤ`.
* `CochainComplex.KFlatMonoidal.isInvertible_shift_derivedMonoidal`: **a shift of an invertible
  object of `D(A)` is invertible**, for the Tag 0FPT monoidal structure.
* `CochainComplex.KFlatMonoidal.isInvertible_shift_iff_derivedMonoidal`: and conversely.

## Implementation notes

The whole file is a transport, in three steps, and no shift computation happens here.

* The coherence itself is `CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int`, the
  two-variable descent of Mathlib's sign coherence on cochain complexes through the homotopy and
  K-flat localizations. That is the only input which is not generic category theory, and it is
  the only reason this module imports
  `StacksFrontier/Homology/KFlat/BifunctorCommShiftTwoInstances.lean`.
* `CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso` identifies `curriedTensor` of
  `derivedMonoidal` with that bifunctor. Recall from `KFlatDerivedBifunctor.lean` that the two
  are equal on the nose in the first instance — `curriedTensor_derivedMonoidal` is `rfl` — and
  the isomorphism is only the further comparison of the two liftings.
* `CategoryTheory.Functor.CommShift.ofIso` moves a `CommShift` along a natural isomorphism, one
  variable at a time. Note that only the per-variable halves of `CommShift₂Int` are consumed;
  the sign coherence `comm` is never used, since the two variables are treated separately.

Two spelling seams had to be crossed by hand, and both are recorded here because neither is
visible from the goal.

* The localizations cannot be instance arguments. `derivedMonoidal A hres` and
  `derivedMonoidalTensorIso A hres` each introduce the two `IsLocalization` witnesses by `letI`
  from `hres`, so a statement about them must introduce *the same terms* the same way; declaring
  them as instance arguments of this module would give different terms and the monoidal
  structure in the goal would not be the one those lemmas talk about. Hence the repeated
  `letI` preamble in every statement and proof below, matching `KFlatDerivedBifunctor.lean`.
* `tensorRight L` is `(curriedTensor _).flip.obj L`, whereas `flipFunctor` produces
  `((flipFunctor _ _ _).obj _).obj L`. These are definitionally equal but not syntactically so,
  and `CommShift₂`'s `commShiftFlipObj` field is indexed at the `.flip.obj` spelling, so
  instance search for the source of the transport fails at the `flipFunctor` spelling and
  reports `failed to synthesize ((flipFunctor ..).obj (derivedBifunctor ..)).obj L).CommShift ℤ`.
  The `show … from` ascription in `derivedMonoidal_tensorRight_commShift` is what crosses it.
  `Functor.flipFunctor` does not exist; the declaration is `CategoryTheory.flipFunctor`.

## References

* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [The Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
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

include hres in
/-- **`K ⊗ -` on `D(A)` commutes with the shift**, for the monoidal structure of Tag 0FPT. The
coherence is that of the derived tensor bifunctor, transported along
`derivedMonoidalTensorIso`. -/
@[instance_reducible]
def derivedMonoidal_tensorLeft_commShift (K : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    (tensorLeft K).CommShift ℤ := by
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  letI := derivedMonoidal A hres
  exact Functor.CommShift.ofIso ((derivedMonoidalTensorIso A hres).app K).symm ℤ

include hres in
/-- **`- ⊗ L` on `D(A)` commutes with the shift**, for the monoidal structure of Tag 0FPT. The
`show … from` ascription moves the source of the transport to the `.flip.obj` spelling at which
`CommShift₂`'s flipped field is indexed. -/
@[instance_reducible]
def derivedMonoidal_tensorRight_commShift (L : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    (tensorRight L).CommShift ℤ := by
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  letI := derivedMonoidal A hres
  exact Functor.CommShift.ofIso
    (show (derivedBifunctor (curriedTensor A)).flip.obj L ≅ tensorRight L from
      (((flipFunctor _ _ _).mapIso (derivedMonoidalTensorIso A hres)).app L).symm) ℤ

/-- The shift-invariance of invertibility, with the instances of the two commutation
statements in scope. -/
private theorem isInvertible_shift_iff_aux (M : DerivedCategory A) (n : ℤ) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    IsInvertible (M⟦n⟧) ↔ IsInvertible M := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  let := fun K : DerivedCategory A => derivedMonoidal_tensorLeft_commShift A hres K
  let := fun L : DerivedCategory A => derivedMonoidal_tensorRight_commShift A hres L
  exact isInvertible_shift_iff M n

include hres in
/-- **A shift of an invertible object of `D(A)` is invertible**, for the monoidal structure of
Tag 0FPT and invertibility in the sense of Tag 0FFN. An inverse of `M⟦n⟧` is `M'⟦-n⟧` for `M'`
an inverse of `M`. -/
theorem isInvertible_shift_derivedMonoidal (M : DerivedCategory A) (n : ℤ) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    IsInvertible M → IsInvertible (M⟦n⟧) := by
  exact (isInvertible_shift_iff_aux A hres M n).2

include hres in
/-- Invertibility in `D(A)` is unaffected by shifting, for the monoidal structure of
Tag 0FPT. -/
theorem isInvertible_shift_iff_derivedMonoidal (M : DerivedCategory A) (n : ℤ) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    IsInvertible (M⟦n⟧) ↔ IsInvertible M := by
  exact isInvertible_shift_iff_aux A hres M n

end CochainComplex.KFlatMonoidal

end
