module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible objects of a monoidal category

An object `X` of a monoidal category `C` is invertible when there is an object `X'` with
`X ⊗ X' ≅ 𝟙_ C` and `X' ⊗ X ≅ 𝟙_ C`. This holds exactly when `tensorLeft X` is an equivalence
of categories, and exactly when `tensorRight X` is.

## Main definitions

* `CategoryTheory.MonoidalCategory.HasInverse`: a two-sided tensor inverse of an object.
* `CategoryTheory.MonoidalCategory.IsInvertible`: an object admitting a two-sided tensor inverse.

## Main results

* `CategoryTheory.MonoidalCategory.HasInverse.inv_iso`: a two-sided tensor inverse is unique up
  to isomorphism.
* `CategoryTheory.MonoidalCategory.invertible_tfae`: `X` is invertible if and only if
  `tensorLeft X` is an equivalence, if and only if `tensorRight X` is.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open CategoryTheory MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- A two-sided tensor inverse for an object `X` of a monoidal category: an object `inv`
together with isomorphisms `X ⊗ inv ≅ 𝟙_ C` and `inv ⊗ X ≅ 𝟙_ C`. -/
@[stacks_fixed 0FFN]
structure HasInverse (X : C) where
  /-- The candidate inverse object. -/
  inv : C
  /-- The isomorphism `X ⊗ inv ≅ 𝟙_ C`. -/
  isoLeft : X ⊗ inv ≅ 𝟙_ C
  /-- The isomorphism `inv ⊗ X ≅ 𝟙_ C`. -/
  isoRight : inv ⊗ X ≅ 𝟙_ C

/-- An object `X` of a monoidal category is *invertible* if it admits a two-sided tensor
inverse, i.e. an object `X'` with `X ⊗ X' ≅ 𝟙_ C` and `X' ⊗ X ≅ 𝟙_ C`. -/
@[stacks 0FFN]
def IsInvertible (X : C) : Prop := Nonempty (HasInverse X)

namespace HasInverse

/-- Two two-sided tensor inverses `X'` and `X''` of `X` are isomorphic, via
`X' ≅ X' ⊗ 𝟙_ C ≅ X' ⊗ (X ⊗ X'') ≅ (X' ⊗ X) ⊗ X'' ≅ 𝟙_ C ⊗ X'' ≅ X''`. -/
noncomputable def inv_iso {X : C} (h₁ h₂ : HasInverse X) : h₁.inv ≅ h₂.inv :=
  (ρ_ h₁.inv).symm ≪≫ tensorIso (Iso.refl h₁.inv) h₂.isoLeft.symm ≪≫
    (α_ h₁.inv X h₂.inv).symm ≪≫ tensorIso h₁.isoRight (Iso.refl h₂.inv) ≪≫ λ_ h₂.inv

/-- The equivalence `tensorLeft X` given by a tensor inverse of `X`, with quasi-inverse
`tensorLeft h.inv`. -/
noncomputable def tensorLeftEquivalence {X : C} (h : HasInverse X) : C ≌ C :=
  .mk (tensorLeft X) (tensorLeft h.inv)
    ((leftUnitorNatIso C).symm
      ≪≫ (tensoringLeft C).mapIso h.isoRight.symm
      ≪≫ tensorLeftTensor h.inv X)
    ((tensorLeftTensor X h.inv).symm
      ≪≫ (tensoringLeft C).mapIso h.isoLeft
      ≪≫ leftUnitorNatIso C)

/-- The equivalence `tensorRight X` given by a tensor inverse of `X`, with quasi-inverse
`tensorRight h.inv`. -/
noncomputable def tensorRightEquivalence {X : C} (h : HasInverse X) : C ≌ C :=
  .mk (tensorRight X) (tensorRight h.inv)
    ((rightUnitorNatIso C).symm
      ≪≫ (tensoringRight C).mapIso h.isoLeft.symm
      ≪≫ tensorRightTensor X h.inv)
    ((tensorRightTensor h.inv X).symm
      ≪≫ (tensoringRight C).mapIso h.isoRight
      ≪≫ rightUnitorNatIso C)

end HasInverse

/-- If `tensorLeft X` is an equivalence, then an essential preimage of `𝟙_ C` is a
two-sided tensor inverse of `X`. -/
noncomputable def hasInverse_of_tensorLeft_isEquivalence {X : C}
    [(tensorLeft X).IsEquivalence] : HasInverse X :=
  let X' : C := (tensorLeft X).objPreimage (𝟙_ C)
  let isoLeft : X ⊗ X' ≅ 𝟙_ C := (tensorLeft X).objObjPreimageIso (𝟙_ C)
  { inv := X'
    isoLeft := isoLeft
    isoRight := (tensorLeft X).preimageIso <|
      (associator X X' X).symm
        ≪≫ tensorIso isoLeft (Iso.refl X)
        ≪≫ leftUnitor X
        ≪≫ (rightUnitor X).symm }

/-- If `tensorRight X` is an equivalence, then an essential preimage of `𝟙_ C` is a
two-sided tensor inverse of `X`. -/
noncomputable def hasInverse_of_tensorRight_isEquivalence {X : C}
    [(tensorRight X).IsEquivalence] : HasInverse X :=
  let X' : C := (tensorRight X).objPreimage (𝟙_ C)
  let isoRight : X' ⊗ X ≅ 𝟙_ C := (tensorRight X).objObjPreimageIso (𝟙_ C)
  { inv := X'
    isoLeft := (tensorRight X).preimageIso <|
      associator X X' X
        ≪≫ tensorIso (Iso.refl X) isoRight
        ≪≫ rightUnitor X
        ≪≫ (leftUnitor X).symm
    isoRight := isoRight }

/-- For an object `X` of a monoidal category, the following are equivalent:
1. `tensorLeft X` is an equivalence;
2. `tensorRight X` is an equivalence;
3. `X` is invertible, i.e. it has a two-sided tensor inverse. -/
@[stacks 0FFM]
theorem invertible_tfae (X : C) :
    [ (tensorLeft X).IsEquivalence,
      (tensorRight X).IsEquivalence,
      IsInvertible X ].TFAE := by
  tfae_have 1 → 3 := fun _ => ⟨hasInverse_of_tensorLeft_isEquivalence⟩
  tfae_have 2 → 3 := fun _ => ⟨hasInverse_of_tensorRight_isEquivalence⟩
  tfae_have 3 → 1 := fun ⟨h⟩ => h.tensorLeftEquivalence.isEquivalence_functor
  tfae_have 3 → 2 := fun ⟨h⟩ => h.tensorRightEquivalence.isEquivalence_functor
  tfae_finish

end CategoryTheory.MonoidalCategory
