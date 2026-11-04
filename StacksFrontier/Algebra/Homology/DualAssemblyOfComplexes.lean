module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import StacksFrontier.Algebra.Homology.DegreewiseLeftDual
public import StacksFrontier.CategoryTheory.Graded.DualAssembly
import StacksCore.Tactic.StacksAttribute

/-!
# Assembling a dual of complexes out of degreewise duals

Let `C` be a monoidal preadditive category carrying the coproducts that make both
`GradedObject ℤ C` and `CochainComplex C ℤ` monoidal, and let `K` be a cochain complex in `C`
vanishing outside a finite set of degrees. Suppose that in every degree `n` the object
`L^{-n}` of a second complex `L` is a dual of `K^n`. Then `η = ∑ ηₙ` and `ε = ∑ εₙ` exhibit the
*graded* object `L^•` as a dual of `K^•`, by
`CategoryTheory.GradedObject.Monoidal.exactPairingOfDegreewise`; and as soon as those two sums
are morphisms of complexes rather than merely of graded objects, `L` is a dual of `K` in
`CochainComplex C ℤ`. This is the converse of `CochainComplex.exactPairingX`, which reads a dual
pair of complexes degree by degree.

The unit of `CochainComplex C ℤ` is only isomorphic to the unit of the graded monoidal structure,
so the hypotheses compare the images of `coeval` and `eval` under the forgetful functor with the
graded pairing conjugated by the structure maps `η`, `ε`, `μ`, `δ` of
`CochainComplex.forgetMonoidal`.

## Main results

* `CochainComplex.exactPairingOfDegreewiseOfChainMaps`: a dual pair of complexes, out of the
  degreewise duals together with the hypothesis that the assembled `η` and `ε` are chain maps.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
* [Stacks Project, Tag 0FFV](https://stacks.math.columbia.edu/tag/0FFV)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject
open CategoryTheory.GradedObject.Monoidal
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (K L : CochainComplex C ℤ) (s : Finset ℤ)
  (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n)))

/-- The forgetful functor from cochain complexes to graded objects. -/
abbrev forgetGraded : CochainComplex C ℤ ⥤ GradedObject ℤ C :=
  HomologicalComplex.forget C (ComplexShape.up ℤ)

/-- If `K` vanishes outside the finite set `s` and `L^{-n}` is a dual of `K^n` in every degree
`n`, and if `coeval` and `eval` are morphisms of complexes whose underlying morphisms of graded
objects are the assembled `η = ∑ ηₙ` and `ε = ∑ εₙ` (`hcoev`, `heval`), then `L` is a dual of `K`
in `CochainComplex C ℤ`. -/
@[instance_reducible]
noncomputable def exactPairingOfDegreewiseOfChainMaps
    (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (coeval : 𝟙_ (CochainComplex C ℤ) ⟶ K ⊗ L)
    (eval : L ⊗ K ⟶ 𝟙_ (CochainComplex C ℤ))
    (hcoev :
      letI := forgetMonoidal (C := C)
      letI : ExactPairing ((forgetGraded (C := C)).obj K) ((forgetGraded (C := C)).obj L) :=
        exactPairingOfDegreewiseOfIsZero (toGradedObject K) (toGradedObject L) s p hbd
      (forgetGraded (C := C)).map coeval =
        η (forgetGraded (C := C)) ≫
          η_ ((forgetGraded (C := C)).obj K) ((forgetGraded (C := C)).obj L) ≫
            μ (forgetGraded (C := C)) K L)
    (heval :
      letI := forgetMonoidal (C := C)
      letI : ExactPairing ((forgetGraded (C := C)).obj K) ((forgetGraded (C := C)).obj L) :=
        exactPairingOfDegreewiseOfIsZero (toGradedObject K) (toGradedObject L) s p hbd
      (forgetGraded (C := C)).map eval =
        δ (forgetGraded (C := C)) L K ≫
          ε_ ((forgetGraded (C := C)).obj K) ((forgetGraded (C := C)).obj L) ≫
            ε (forgetGraded (C := C))) :
    ExactPairing K L :=
  letI := forgetMonoidal (C := C)
  letI : ExactPairing ((forgetGraded (C := C)).obj K) ((forgetGraded (C := C)).obj L) :=
    exactPairingOfDegreewiseOfIsZero (toGradedObject K) (toGradedObject L) s p hbd
  ExactPairing.ofFaithful (forgetGraded (C := C)) eval coeval heval hcoev

end CochainComplex

end
