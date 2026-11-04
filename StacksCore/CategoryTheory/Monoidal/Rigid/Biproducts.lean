module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksCore.CategoryTheory.Monoidal.Rigid.Lemmas

/-! # Duals and biproducts

Stacks 0FFT: in an additive monoidal category, if `Yᵢ` is a left dual of `Xᵢ` for `i = 1, 2`,
then `Y₁ ⊕ Y₂` is a left dual of `X₁ ⊕ X₂`.

Mathlib's `ExactPairing X Y` is Stacks' "`Y` is a left dual of `X`" — the same coevaluation,
evaluation and triangle identities — but Mathlib *names* that `Y` the **right** dual `Xᘁ`. Only
the name differs, so the tag is `CategoryTheory.ExactPairing.biprod` below, together with the
packaged `CategoryTheory.hasRightDualBiprod`. We also give the version for a finite family,
`CategoryTheory.ExactPairing.biproduct`.

Unlike `ExactPairing.tensor`, the biproduct pairing does not reverse the order of the factors.
Beyond `Preadditive` and `MonoidalPreadditive`, only the individual biproducts used in the
statement are needed: neither `HasFiniteBiproducts` nor an ambient additive category is required.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

variable [Preadditive C] [MonoidalPreadditive C]

omit [MonoidalCategory C] [MonoidalPreadditive C] in
/-- Reassemble a sum of the two biproduct legs sandwiched between fixed maps. -/
private lemma comp_biprod_total_comp {W Z Y₁ Y₂ : C} [HasBinaryBiproduct Y₁ Y₂]
    (f : W ⟶ Y₁ ⊞ Y₂) (g : Y₁ ⊞ Y₂ ⟶ Z) :
    f ≫ biprod.fst ≫ biprod.inl ≫ g + f ≫ biprod.snd ≫ biprod.inr ≫ g = f ≫ g := by
  rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
    ← Preadditive.add_comp, biprod.total, Category.id_comp]

section Binary

variable {X₁ X₂ Y₁ Y₂ : C} [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂]
  [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]

/-- **Stacks 0FFT**: the biproduct of two exact pairings is an exact pairing. In Stacks'
language, if `Yᵢ` is a left dual of `Xᵢ` for `i = 1, 2` then `Y₁ ⊕ Y₂` is a left dual of
`X₁ ⊕ X₂`. Note that, unlike `ExactPairing.tensor`, the factors are not reversed. -/
@[stacks 0FFT]
noncomputable instance ExactPairing.biprod : ExactPairing (X₁ ⊞ X₂) (Y₁ ⊞ Y₂) where
  coevaluation' :=
    η_ X₁ Y₁ ≫ (biprod.inl ⊗ₘ biprod.inl) + η_ X₂ Y₂ ≫ (biprod.inr ⊗ₘ biprod.inr)
  evaluation' :=
    (biprod.fst ⊗ₘ biprod.fst) ≫ ε_ X₁ Y₁ + (biprod.snd ⊗ₘ biprod.snd) ≫ ε_ X₂ Y₂
  coevaluation_evaluation' := by
    simp [-whiskerLeft_comp, coevaluation_evaluation_comp, -comp_whiskerRight,
      whiskerRight_coevaluation_evaluation, comp_biprod_total_comp]
  evaluation_coevaluation' := by
    simp [-comp_whiskerRight, evaluation_coevaluation_comp, -whiskerLeft_comp,
      whiskerLeft_evaluation_coevaluation, comp_biprod_total_comp]

lemma ExactPairing.biprod_coevaluation :
    η_ (X₁ ⊞ X₂) (Y₁ ⊞ Y₂)
      = η_ X₁ Y₁ ≫ (biprod.inl ⊗ₘ biprod.inl) + η_ X₂ Y₂ ≫ (biprod.inr ⊗ₘ biprod.inr) :=
  rfl

lemma ExactPairing.biprod_evaluation :
    ε_ (X₁ ⊞ X₂) (Y₁ ⊞ Y₂)
      = (biprod.fst ⊗ₘ biprod.fst) ≫ ε_ X₁ Y₁ + (biprod.snd ⊗ₘ biprod.snd) ≫ ε_ X₂ Y₂ :=
  rfl

end Binary

section Family

-- The index type is `Type 0` only because `biproduct.total` is: it lives in a section declared
-- `variable {J : Type} [Fintype J]` in `Mathlib.CategoryTheory.Preadditive.Biproducts`. Once
-- mathlib#43473 (which generalizes that file's universes) lands in our pin, widen `J` to
-- `Type*` here and the proofs below go through unchanged.
variable {J : Type} [Fintype J] {X Y : J → C} [HasBiproduct X] [HasBiproduct Y]
  [∀ j, ExactPairing (X j) (Y j)]

omit [MonoidalCategory C] [MonoidalPreadditive C] in
/-- The finite-family analogue of `comp_biprod_total_comp`. -/
private lemma comp_biproduct_total_comp {W Z : C} (f : W ⟶ ⨁ Y) (g : ⨁ Y ⟶ Z) :
    (∑ j : J, f ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ g) = f ≫ g := by
  simp [← Category.assoc, ← Preadditive.sum_comp]
  simp [← Preadditive.comp_sum]

/-- **Stacks 0FFT** for a finite family: `⨁ Y` is a left dual of `⨁ X` as soon as each `Y j`
is a left dual of `X j`. -/
@[stacks 0FFT "for an arbitrary finite family"]
noncomputable instance ExactPairing.biproduct : ExactPairing (⨁ X) (⨁ Y) where
  coevaluation' :=
    ∑ j : J, η_ (X j) (Y j) ≫ (biproduct.ι X j ⊗ₘ biproduct.ι Y j)
  evaluation' :=
    ∑ j : J, (biproduct.π Y j ⊗ₘ biproduct.π X j) ≫ ε_ (X j) (Y j)
  coevaluation_evaluation' := by
    simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
      coevaluation_evaluation_comp,  ← comp_biproduct_total_comp (ρ_ (⨁ Y)).hom (λ_ (⨁ Y)).inv]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    all_goals simp +contextual [-comp_whiskerRight, whiskerRight_coevaluation_evaluation]
  evaluation_coevaluation' := by
    simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
      evaluation_coevaluation_comp, ← comp_biproduct_total_comp (λ_ (⨁ X)).hom (ρ_ (⨁ X)).inv]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    all_goals simp +contextual [-whiskerLeft_comp, whiskerLeft_evaluation_coevaluation]

end Family

/-- **Stacks 0FFT**, packaged: a biproduct of objects with right duals has a right dual. -/
@[stacks 0FFT, implicit_reducible]
noncomputable def hasRightDualBiprod {X₁ X₂ : C} [HasRightDual X₁] [HasRightDual X₂]
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct (X₁ᘁ) (X₂ᘁ)] : HasRightDual (X₁ ⊞ X₂) where
  rightDual := X₁ᘁ ⊞ X₂ᘁ

end CategoryTheory
