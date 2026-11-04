module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Module.Pi
public import Mathlib.CategoryTheory.Linear.Basic
public import StacksCore.CategoryTheory.GradedObject.Abelian

/-!
# Graded objects in a linear category

If `C` is an `R`-linear category, then so is the category `GradedObject β C` of `β`-graded objects
of `C`, with scalars acting degreewise. The preadditive structure is the degreewise one of
`CategoryTheory.GradedObject.preadditive` (Stacks 0126). For `C = ModuleCat F` with `F` a field of
characteristic zero and `R = ℚ`, this gives the `ℚ`-linear structure on graded `F`-vector spaces of
Stacks 0FH1, 0FH2 and 0FH3, found by instance search from `CategoryTheory.GradedObject.linear`,
`ModuleCat.linearOverField` and the `ℚ`-algebra structure `DivisionRing.toRatAlgebra` of `F`.

## Main definitions

* `CategoryTheory.GradedObject.linear`: the degreewise `R`-linear structure.

## Main results

* `CategoryTheory.GradedObject.smul_apply`: scalars act degreewise.
-/

@[expose] public section

namespace CategoryTheory.GradedObject

universe w v u

variable {β : Type w} {C : Type u} [Category.{v} C] [Preadditive C]
  (R : Type*) [Semiring R] [Linear R C]

/-- The degreewise `R`-linear structure on the category of graded objects of an `R`-linear
category. -/
instance linear : Linear R (GradedObject β C) where
  homModule X Y := inferInstanceAs (Module R (∀ b, X b ⟶ Y b))
  smul_comp _ _ _ _ _ _ := funext fun _ => Linear.smul_comp ..
  comp_smul _ _ _ _ _ _ := funext fun _ => Linear.comp_smul ..

variable {R} {X Y : GradedObject β C}

/-- Scalars act on a morphism of graded objects degreewise. -/
@[simp]
lemma smul_apply (r : R) (f : X ⟶ Y) (b : β) : (r • f) b = r • f b := rfl

-- Graded vector spaces over a field of characteristic zero form a `ℚ`-linear category.
example (F : Type*) [Field F] [CharZero F] : Linear ℚ (GradedObject β (ModuleCat F)) :=
  inferInstance

end CategoryTheory.GradedObject
