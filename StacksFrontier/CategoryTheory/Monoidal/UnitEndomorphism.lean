module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Endomorphisms of the tensor unit: composition is the tensor product

In a monoidal category the endomorphisms of the tensor unit form a commutative monoid in two
*a priori* different ways — by composition and by tensor product — and the right unit
constraint `ρ_ (𝟙_ C) : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C` identifies the two:

`(a ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ (a ≫ b)`.

This is the one computation behind the statement that an `n`th tensor power of a trivialized
invertible object twists by the `n`th power of the twist of the trivialization: at each step of
the induction a new tensor factor contributes one more composite factor, and that is exactly
what the displayed equation says.

## Main results

* `CategoryTheory.MonoidalCategory.tensorHom_unitEnd_comp_rightUnitor`: the displayed equation.
* `CategoryTheory.MonoidalCategory.tensorIso_unitAut_trans_rightUnitor`: the same for
  isomorphisms.
* `CategoryTheory.MonoidalCategory.tensorIso_trans`: functoriality of the tensor product of
  isomorphisms.
* `CategoryTheory.Iso.autPow`: the `n`-fold composite of an automorphism, with
  `CategoryTheory.Iso.autPow_succ` and `CategoryTheory.Iso.autPow_one`.

## Implementation notes

The proof is the standard coherence argument: `a ⊗ₘ b` factors as `(a ▷ 𝟙) ≫ (𝟙 ◁ b)`, the two
unitors are natural, and `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` by
`CategoryTheory.MonoidalCategory.unitors_equal`. No braiding or symmetry is used, so the
statement holds in a monoidal category which is not braided.

`autPow` is defined by its own recursion rather than taken as the `Monoid.npow` of
`CategoryTheory.Aut`, so that no convention about the order of multiplication in `Aut` is in
play: `autPow a (n + 1) = autPow a n ≪≫ a` is the orientation in which the induction above
produces its factors.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

namespace Iso

variable {C : Type u} [Category.{v} C]

/-- The `n`-fold composite of an automorphism, with the new factor on the right. -/
def autPow {X : C} (a : X ≅ X) : ℕ → (X ≅ X)
  | 0 => Iso.refl X
  | n + 1 => autPow a n ≪≫ a

/-- The `0`-fold composite of an automorphism is the identity. -/
@[simp]
theorem autPow_zero {X : C} (a : X ≅ X) : a.autPow 0 = Iso.refl X := rfl

/-- The `(n + 1)`-fold composite of `a` is the `n`-fold composite followed by `a`. -/
theorem autPow_succ {X : C} (a : X ≅ X) (n : ℕ) : a.autPow (n + 1) = a.autPow n ≪≫ a := rfl

/-- The `1`-fold composite of an automorphism is the automorphism itself. -/
@[simp]
theorem autPow_one {X : C} (a : X ≅ X) : a.autPow 1 = a :=
  Iso.ext (Category.id_comp a.hom)

end Iso

namespace MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Composition of endomorphisms of the tensor unit is their tensor product**, read through
the right unit constraint of the unit. -/
theorem tensorHom_unitEnd_comp_rightUnitor (a b : 𝟙_ C ⟶ 𝟙_ C) :
    (a ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ (a ≫ b) := by
  rw [tensorHom_def, Category.assoc, ← unitors_equal, leftUnitor_naturality,
    unitors_equal, ← Category.assoc, rightUnitor_naturality, Category.assoc]

/-- `tensorHom_unitEnd_comp_rightUnitor` for automorphisms of the tensor unit. -/
theorem tensorIso_unitAut_trans_rightUnitor (a b : (𝟙_ C) ≅ (𝟙_ C)) :
    (a ⊗ᵢ b) ≪≫ ρ_ (𝟙_ C) = ρ_ (𝟙_ C) ≪≫ (a ≪≫ b) :=
  Iso.ext (tensorHom_unitEnd_comp_rightUnitor a.hom b.hom)

/-- The tensor product of isomorphisms is functorial in each argument. -/
theorem tensorIso_trans {X X' X'' Y Y' Y'' : C} (f : X ≅ X') (f' : X' ≅ X'')
    (g : Y ≅ Y') (g' : Y' ≅ Y'') :
    (f ≪≫ f') ⊗ᵢ (g ≪≫ g') = (f ⊗ᵢ g) ≪≫ (f' ⊗ᵢ g') :=
  Iso.ext (tensorHom_comp_tensorHom f.hom g.hom f'.hom g'.hom).symm

end MonoidalCategory

end CategoryTheory

end
