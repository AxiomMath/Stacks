module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The tensor product of presheaves of modules is additive in each variable

Let `R` be a presheaf of commutative rings on a category `C`. Presheaves of `R`-modules carry
the objectwise tensor product as a monoidal structure (Mathlib's
`PresheafOfModules.monoidalCategory`) and the objectwise addition of morphisms as a preadditive
structure. This file records that the two are compatible:
`CategoryTheory.MonoidalPreadditive` holds.

The content is entirely objectwise. Whiskering a morphism of presheaves of modules is
whiskering of its components, the zero and the sum of morphisms are the componentwise zero and
sum, and `ModuleCat` is `CategoryTheory.MonoidalPreadditive`; so each of the four laws is the
corresponding law in `ModuleCat` at every object of the site.

## Main results

* `Stacks.ProjTwistFunctor.monoidalPreadditive`: presheaves of modules over a presheaf of
  commutative rings are monoidal preadditive.

## Implementation notes

The module universe is equal to the ring universe: Mathlib's monoidal structure on presheaves of
modules exists only at that single universe. The universes of `C` and of the ring are
independent.

No tag attribute is attached: this is a categorical compatibility and the statement of no tag.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.ProjTwistFunctor

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **Presheaves of modules are monoidal preadditive**: the objectwise tensor product of
presheaves of modules is additive in each variable. -/
instance monoidalPreadditive :
    MonoidalPreadditive (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) where
  whiskerLeft_zero {X Y Z} := by
    ext1 U
    change (𝟙 (X.obj U)) ⊗ₘ (0 : Y.obj U ⟶ Z.obj U) = 0
    exact MonoidalPreadditive.tensor_zero _
  zero_whiskerRight {X Y Z} := by
    ext1 U
    change (0 : Y.obj U ⟶ Z.obj U) ⊗ₘ (𝟙 (X.obj U)) = 0
    exact MonoidalPreadditive.zero_tensor _
  whiskerLeft_add {X Y Z} f g := by
    ext1 U
    change (𝟙 (X.obj U)) ⊗ₘ (f.app U + g.app U) = _
    exact MonoidalPreadditive.tensor_add _ _ _
  add_whiskerRight {X Y Z} f g := by
    ext1 U
    change (f.app U + g.app U) ⊗ₘ (𝟙 (X.obj U)) = _
    exact MonoidalPreadditive.add_tensor _ _ _

end Stacks.ProjTwistFunctor

end
