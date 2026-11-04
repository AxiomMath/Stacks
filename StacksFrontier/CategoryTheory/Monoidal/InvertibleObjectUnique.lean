module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# Tensor inverses in a monoidal category are unique

Let `C` be a monoidal category and `X` an object of `C`. If `Y ⊗ X ≅ 𝟙_ C` and `X ⊗ Z ≅ 𝟙_ C`
then `Y ≅ Z`: the usual argument

`Z ≅ 𝟙_ C ⊗ Z ≅ (Y ⊗ X) ⊗ Z ≅ Y ⊗ (X ⊗ Z) ≅ Y ⊗ 𝟙_ C ≅ Y`

uses nothing but the unitors and the associator, and in particular needs neither a braiding nor
any rigidity. Consequently the two-sided inverse carried by
`CategoryTheory.MonoidalCategory.HasInverse` is unique up to isomorphism, and a *one*-sided
inverse already determines it.

## Main definitions

* `CategoryTheory.MonoidalCategory.tensorInverseIso`: a left tensor inverse and a right tensor
  inverse of the same object are isomorphic.
* `CategoryTheory.MonoidalCategory.HasInverse.invIsoOfTensorIsoUnit`: any object whose tensor
  product with `X` is the unit is isomorphic to the chosen inverse of `X`.
* `CategoryTheory.MonoidalCategory.HasInverse.invIso`: two two-sided tensor inverses of the same
  object are isomorphic.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open CategoryTheory MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **A left tensor inverse and a right tensor inverse of the same object are isomorphic.**
Given `eY : Y ⊗ X ≅ 𝟙_ C` and `eZ : X ⊗ Z ≅ 𝟙_ C`, the composite

`Z ≅ 𝟙_ C ⊗ Z ≅ (Y ⊗ X) ⊗ Z ≅ Y ⊗ (X ⊗ Z) ≅ Y ⊗ 𝟙_ C ≅ Y`

is an isomorphism `Z ≅ Y`. -/
def tensorInverseIso {X Y Z : C} (eY : Y ⊗ X ≅ 𝟙_ C) (eZ : X ⊗ Z ≅ 𝟙_ C) : Z ≅ Y :=
  (λ_ Z).symm ≪≫ whiskerRightIso eY.symm Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y eZ ≪≫ ρ_ Y

namespace HasInverse

/-- Any right tensor inverse of `X` is isomorphic to the inverse chosen by a `HasInverse X`:
the two-sided inverse of an invertible object is determined by a one-sided inverse. -/
def invIsoOfTensorIsoUnit {X Z : C} (h : HasInverse X) (eZ : X ⊗ Z ≅ 𝟙_ C) : Z ≅ h.inv :=
  tensorInverseIso h.isoRight eZ

/-- The two-sided tensor inverse of an object of a monoidal category is unique up to
isomorphism. -/
def invIso {X : C} (h₁ h₂ : HasInverse X) : h₂.inv ≅ h₁.inv :=
  h₁.invIsoOfTensorIsoUnit h₂.isoLeft

end HasInverse

end CategoryTheory.MonoidalCategory

end
