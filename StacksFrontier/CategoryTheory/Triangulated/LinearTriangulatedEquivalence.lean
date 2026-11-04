module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Equivalences of linear triangulated categories

An equivalence of `R`-linear pretriangulated categories *as `R`-linear triangulated categories* is
an equivalence of categories whose functor commutes with the shifts, preserves distinguished
triangles and is `R`-linear. Its inverse is then of the same kind, and such equivalences compose.
This is the form of the conclusion of Remark 0H1E, which chains several such equivalences.

## Main definitions

* `CategoryTheory.LinearTriangulatedEquivalence R C D`: an equivalence `C ≌ D` with a
  `CommShift ℤ` structure on its functor for which the functor is triangulated and `R`-linear.
* `CategoryTheory.LinearTriangulatedEquivalence.symm`, `.trans`, `.refl`.

## References

* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Pretriangulated

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- **An equivalence of `R`-linear triangulated categories**: an equivalence of categories whose
functor commutes with the shifts, is a triangulated functor and is `R`-linear. -/
structure LinearTriangulatedEquivalence (R : Type w) [Ring R] (C : Type u₁) [Category.{v₁} C]
    [HasZeroObject C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [Linear R C]
    (D : Type u₂) [Category.{v₂} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Linear R D] where
  /-- The underlying equivalence of categories. -/
  equivalence : C ≌ D
  /-- The functor commutes with the shifts. -/
  commShift : equivalence.functor.CommShift ℤ
  /-- The functor is triangulated. -/
  isTriangulated : equivalence.functor.IsTriangulated
  /-- The functor is `R`-linear. -/
  linear : equivalence.functor.Linear R

namespace LinearTriangulatedEquivalence

variable {R : Type w} [Ring R]
  {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Linear R D]
  {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [Preadditive E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E] [Linear R E]

attribute [instance] commShift isTriangulated linear

/-- The identity equivalence. -/
def refl : LinearTriangulatedEquivalence R C C where
  equivalence := Equivalence.refl
  commShift := inferInstanceAs ((𝟭 C).CommShift ℤ)
  isTriangulated := inferInstanceAs (𝟭 C).IsTriangulated
  linear := inferInstanceAs ((𝟭 C).Linear R)

/-- **The inverse of an equivalence of linear triangulated categories is one.** The shift
structure on the inverse is the one compatible with that of the functor, for which the
equivalence commutes with the shifts; the inverse of a triangulated equivalence is triangulated,
and the inverse of a linear equivalence is linear. -/
def symm (e : LinearTriangulatedEquivalence R C D) : LinearTriangulatedEquivalence R D C where
  equivalence := e.equivalence.symm
  commShift := e.equivalence.commShiftInverse ℤ
  isTriangulated := by
    let := e.equivalence.commShiftInverse ℤ
    have := e.equivalence.commShift_of_functor ℤ
    have : e.equivalence.IsTriangulated := Equivalence.IsTriangulated.mk' _ e.isTriangulated
    exact inferInstanceAs e.equivalence.inverse.IsTriangulated
  linear := inferInstanceAs (e.equivalence.inverse.Linear R)

/-- **Equivalences of linear triangulated categories compose.** -/
def trans (e : LinearTriangulatedEquivalence R C D) (e' : LinearTriangulatedEquivalence R D E) :
    LinearTriangulatedEquivalence R C E where
  equivalence := e.equivalence.trans e'.equivalence
  commShift := inferInstanceAs ((e.equivalence.functor ⋙ e'.equivalence.functor).CommShift ℤ)
  isTriangulated := inferInstanceAs (e.equivalence.functor ⋙ e'.equivalence.functor).IsTriangulated
  linear := inferInstanceAs ((e.equivalence.functor ⋙ e'.equivalence.functor).Linear R)

end LinearTriangulatedEquivalence

end CategoryTheory
