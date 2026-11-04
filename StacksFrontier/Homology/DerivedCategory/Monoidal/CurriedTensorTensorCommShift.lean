module

public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoOfIso
public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorCommShift

/-!
# The tensor product of `D(A)` acts on morphisms compatibly with the shift

Let `A` be an abelian braided monoidal category satisfying the hypotheses under which
`CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(A)` with the monoidal structure of
[Stacks, Tag 0FPT].  `CurriedTensorCommShift.lean` transports the *objectwise* halves of the
two-variable shift coherence of the derived tensor bifunctor onto that monoidal structure: each
`K ⊗ -` and each `- ⊗ L` commutes with the shift.  This file transports the whole coherence, and
reads off the remaining halves -- the ones about the action on *morphisms* -- as
`CategoryTheory.MonoidalCategory.TensorCommShift`.

That is what lets a natural transformation built from a tensor product of a varying morphism with
a fixed one be whiskered inside `CategoryTheory.NatTrans.CommShift`, which is what the shift
compatibility of the comparison of [Stacks, Tag 08QB] is assembled from
(`CategoryTheory.Adjunction.externalMateTranspose_eq`).

## Main results

* `CochainComplex.KFlatMonoidal.derivedMonoidal_commShift₂Int`: **the curried tensor product of
  `derivedMonoidal` commutes with the shifts in both variables**, with Mathlib's sign.
* `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorCommShift`: **the action of that tensor
  product on morphisms is compatible with those commutations.**

## Implementation notes

Both are transports and no shift computation happens here.  The coherence itself is
`CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int`, and
`CategoryTheory.Functor.CommShift₂.ofIsoInt` moves it along
`CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso`, which is the same isomorphism along
which `CurriedTensorCommShift.lean` moves the two objectwise halves one variable at a time.  The
two transports therefore agree: `CategoryTheory.Functor.CommShift₂.ofIso` defines its
`commShiftObj` and `commShiftFlipObj` fields to be exactly the one-variable
`CategoryTheory.Functor.CommShift.ofIso` at the components of the isomorphism and of its flip,
and `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_commShift` and
`derivedMonoidal_tensorRight_commShift` are those same terms.  So
`derivedMonoidal_tensorCommShift` can be, and is, stated relative to the structures those two
`def`s provide -- the ones every downstream statement about this monoidal structure seats -- and
not relative to a second copy introduced here.

The `letI` preamble is repeated in every statement and proof for the reason recorded in
`CurriedTensorCommShift.lean`: `derivedMonoidal A hres` and `derivedMonoidalTensorIso A hres`
build the two localization witnesses from `hres` inside each declaration, so a statement about
them must build the same terms the same way.

The source of the transport is `(derivedMonoidalTensorIso A hres).symm`, the isomorphism read
from the bifunctor to the monoidal spelling, because `CategoryTheory.Functor.CommShift₂.ofIso`
transports from the source of its argument to the target.

## References

* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
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
/-- **The curried tensor product of `derivedMonoidal` commutes with the shifts in both
variables.**  The coherence is that of the derived tensor bifunctor,
`CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int`, transported along
`derivedMonoidalTensorIso` by `CategoryTheory.Functor.CommShift₂.ofIsoInt`. -/
@[instance_reducible]
def derivedMonoidal_commShift₂Int :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    (curriedTensor (DerivedCategory A)).CommShift₂Int := by
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  letI := derivedMonoidal A hres
  exact Functor.CommShift₂.ofIsoInt (derivedMonoidalTensorIso A hres).symm

include hres in
/-- **The action of the tensor product of `D(A)` on morphisms is compatible with the commutations
of `K ⊗ -` and `- ⊗ L` with the shift**, for the monoidal structure of Tag 0FPT and the
commutations of `derivedMonoidal_tensorLeft_commShift` and
`derivedMonoidal_tensorRight_commShift`.

These are the two remaining halves of `derivedMonoidal_commShift₂Int`, whose objectwise halves
*are* those two `def`s, so no second commutation is introduced; see the implementation notes. -/
theorem derivedMonoidal_tensorCommShift :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    letI := fun K : DerivedCategory A => derivedMonoidal_tensorLeft_commShift A hres K
    letI := fun L : DerivedCategory A => derivedMonoidal_tensorRight_commShift A hres L
    TensorCommShift (DerivedCategory A) ℤ := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  let := derivedMonoidal_commShift₂Int A hres
  exact TensorCommShift.of_commShift₂ (DerivedCategory A) CommShift₂Setup.int

end CochainComplex.KFlatMonoidal

end
