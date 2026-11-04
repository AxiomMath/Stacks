module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidal
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# The tensor product of the twisted Karoubi envelope is additive and linear

If the tensor product of a graded monoidal category `C` is additive (`R`-linear) in each variable,
so is the tensor product of its twisted Karoubi envelope: morphisms of triples are morphisms of
`C`, and the whiskerings of triples are tensor products of morphisms of `C` with idempotents.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.monoidalPreadditive`: the twisted Karoubi envelope
  of a graded monoidal category with additive tensor product has additive tensor product.
* `CategoryTheory.GradedCategory.TwistedKaroubi.monoidalLinear`: and `R`-linear tensor product
  if that of `C` is.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C] [MonoidalPreadditive C]

/-- The tensor product of the twisted Karoubi envelope is additive in each variable. -/
instance monoidalPreadditive : MonoidalPreadditive (TwistedKaroubi R C) where
  whiskerLeft_zero := by intros; ext; simp; rfl
  zero_whiskerRight := by intros; ext; simp; rfl
  whiskerLeft_add := by intros; ext; simp [MonoidalPreadditive.tensor_add]; rfl
  add_whiskerRight := by intros; ext; simp [MonoidalPreadditive.add_tensor]; rfl

/-- The tensor product of the twisted Karoubi envelope is `R`-linear in each variable. -/
instance monoidalLinear [MonoidalLinear R C] : MonoidalLinear R (TwistedKaroubi R C) where
  whiskerLeft_smul := by intros; ext; simp [tensorHom_def]; rfl
  smul_whiskerRight := by intros; ext; simp [tensorHom_def]; rfl

end CategoryTheory.GradedCategory.TwistedKaroubi
