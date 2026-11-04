module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech complex as a functor to bounded-below complexes

Let `E` be a family of morphisms of a category with a fixed target `X`, all of whose finite
nonempty fibre products exist. Stacks 03AP is the observation that the Čech complex
construction of Stacks 03AM is functorial in the coefficient presheaf and lands in
bounded-below complexes: it is a functor `PAb(C) ⥤ Comp⁺(Ab)`.

## Main definitions

* `Stacks.CechSite.cechComplexPlusFunctor`: the Čech complex functor, with the nonnegative
  grading of `Stacks.CechSite.cechComplexFunctor` regarded as a bounded-below integer
  grading.

## Implementation notes

The natural-number-graded complex produced by `Stacks.CechSite.cechComplexFunctor` is
extended by zero to an integer-graded complex along `ComplexShape.embeddingUpNat`, which
makes `0` a strict lower bound for it; that bound is the witness placed in
`CochainComplex.Plus`. The construction is stated for presheaves valued in any preadditive
category with a zero object admitting the products the Čech complex needs; taking the target
to be abelian groups gives the functor displayed in the source.

## References

* [Stacks Project, Tag 03AP](https://stacks.math.columbia.edu/tag/03AP)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace Stacks.CechSite

universe w v v' u u'

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

/-- **Stacks 03AP.** The Čech complex as a functor of the coefficient presheaf, with its
nonnegative grading regarded canonically as a bounded-below integer grading. -/
@[stacks 03AP]
public noncomputable def cechComplexPlusFunctor {A : Type u'} [Category.{v'} A]
    [HasProducts.{w} A] [Preadditive A] [HasZeroObject A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    CategoryTheory.Functor (CategoryTheory.Functor Cᵒᵖ A) (CochainComplex.Plus A) :=
  ObjectProperty.lift _ (cechComplexFunctor E ⋙ embeddingUpNat.extendFunctor A)
    (fun F ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE
        (((cechComplexFunctor E).obj F).extend embeddingUpNat) 0
      infer_instance⟩)

end Stacks.CechSite

end
