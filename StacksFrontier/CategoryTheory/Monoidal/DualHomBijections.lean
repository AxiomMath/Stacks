module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The hom bijections attached to a left dual

Let `C` be a monoidal category and let `Y` be a left dual of `X` in the sense of Stacks 0FFP,
i.e. there are `η : 𝟙 ⟶ X ⊗ Y` and `ε : Y ⊗ X ⟶ 𝟙` satisfying the two triangle identities. In
Mathlib this is `CategoryTheory.ExactPairing X Y`: its coevaluation `η_ X Y : 𝟙_ C ⟶ X ⊗ Y` and its
evaluation `ε_ X Y : Y ⊗ X ⟶ 𝟙_ C` are exactly the source's `η` and `ε`, with the same triangle
identities (Mathlib calls `Y` a *right* dual of `X`, the opposite naming convention).

Stacks 0FFQ says that then
`Mor(Z' ⊗ X, Z) = Mor(Z', Z ⊗ Y)` and `Mor(Y ⊗ Z', Z) = Mor(Z', X ⊗ Z)`, functorially in `Z` and
`Z'`. A bijection of hom sets natural in both variables is precisely an adjunction, and Mathlib
provides both:

* `CategoryTheory.tensorRightAdjunction X Y : tensorRight X ⊣ tensorRight Y`, whose hom
  bijection is `tensorRightHomEquiv Z' X Y Z : (Z' ⊗ X ⟶ Z) ≃ (Z' ⟶ Z ⊗ Y)`, natural in `Z`
  (`tensorRightHomEquiv_naturality`) and in `Z'` (`tensorRightHomEquiv_symm_naturality`);
* `CategoryTheory.tensorLeftAdjunction X Y : tensorLeft Y ⊣ tensorLeft X`, whose hom bijection is
  `tensorLeftHomEquiv Z' X Y Z : (Y ⊗ Z' ⟶ Z) ≃ (Z' ⟶ X ⊗ Z)`, natural in `Z`
  (`tensorLeftHomEquiv_naturality`) and in `Z'` (`tensorLeftHomEquiv_symm_naturality`).

Both are constructed exactly as in the source's proof, from `η` and `ε`. They are registered here
for Stacks 0FFQ, and nothing is redefined. The two theorems of this file state the naturality of
each bijection in `Z` and `Z'` at once, as a single identity.

## Main results

* `CategoryTheory.tensorRightHomEquiv_whiskerRight_comp_comp`: **Stacks 0FFQ**, the bijection
  `Mor(Z' ⊗ X, Z) = Mor(Z', Z ⊗ Y)` is natural in `Z` and `Z'`.
* `CategoryTheory.tensorLeftHomEquiv_whiskerLeft_comp_comp`: **Stacks 0FFQ**, the bijection
  `Mor(Y ⊗ Z', Z) = Mor(Z', X ⊗ Z)` is natural in `Z` and `Z'`.

## References

* [Stacks Project, Tag 0FFQ](https://stacks.math.columbia.edu/tag/0FFQ)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Stacks Project, Tag 0FFQ**, first bijection. If `Y` is a left dual of `X` (in Mathlib,
`[ExactPairing X Y]`), then `tensorRightHomEquiv Z' X Y Z : Mor(Z' ⊗ X, Z) ≃ Mor(Z', Z ⊗ Y)` is
natural in `Z` and `Z'`: for `a : Z₂' ⟶ Z₁'` and `b : Z₁ ⟶ Z₂` it carries
`(a ⊗ 1_X) ≫ f ≫ b` to `a ≫ e(f) ≫ (b ⊗ 1_Y)`. -/
@[stacks 0FFQ "first bijection, natural in Z and Z'"]
theorem tensorRightHomEquiv_whiskerRight_comp_comp (X Y : C) [ExactPairing X Y] {Z₁' Z₂' Z₁ Z₂ : C}
    (a : Z₂' ⟶ Z₁') (f : Z₁' ⊗ X ⟶ Z₁) (b : Z₁ ⟶ Z₂) :
    tensorRightHomEquiv Z₂' X Y Z₂ (a ▷ X ≫ f ≫ b) =
      a ≫ tensorRightHomEquiv Z₁' X Y Z₁ f ≫ b ▷ Y := by
  rw [← Equiv.eq_symm_apply, tensorRightHomEquiv_symm_naturality,
    ← tensorRightHomEquiv_naturality, Equiv.symm_apply_apply]

/-- **Stacks Project, Tag 0FFQ**, second bijection. If `Y` is a left dual of `X` (in Mathlib,
`[ExactPairing X Y]`), then `tensorLeftHomEquiv Z' X Y Z : Mor(Y ⊗ Z', Z) ≃ Mor(Z', X ⊗ Z)` is
natural in `Z` and `Z'`: for `a : Z₂' ⟶ Z₁'` and `b : Z₁ ⟶ Z₂` it carries
`(1_Y ⊗ a) ≫ f ≫ b` to `a ≫ e(f) ≫ (1_X ⊗ b)`. -/
@[stacks 0FFQ "second bijection, natural in Z and Z'"]
theorem tensorLeftHomEquiv_whiskerLeft_comp_comp (X Y : C) [ExactPairing X Y] {Z₁' Z₂' Z₁ Z₂ : C}
    (a : Z₂' ⟶ Z₁') (f : Y ⊗ Z₁' ⟶ Z₁) (b : Z₁ ⟶ Z₂) :
    tensorLeftHomEquiv Z₂' X Y Z₂ (Y ◁ a ≫ f ≫ b) =
      a ≫ tensorLeftHomEquiv Z₁' X Y Z₁ f ≫ X ◁ b := by
  rw [← Equiv.eq_symm_apply, tensorLeftHomEquiv_symm_naturality,
    ← tensorLeftHomEquiv_naturality, Equiv.symm_apply_apply]

end CategoryTheory

/- Stacks 0FFQ, both bijections packaged with their naturality in `Z` and `Z'` as adjunctions:
`tensorRight X ⊣ tensorRight Y` and `tensorLeft Y ⊣ tensorLeft X`, for `[ExactPairing X Y]`. -/
add_to_stacks 0FFQ "first bijection as the adjunction tensorRight X ⊣ tensorRight Y"
  CategoryTheory.tensorRightAdjunction
add_to_stacks 0FFQ "second bijection as the adjunction tensorLeft Y ⊣ tensorLeft X"
  CategoryTheory.tensorLeftAdjunction

end
