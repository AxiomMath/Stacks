module

public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Conjugates and a change of the left adjoint

Let `adj : L ⊣ R` be an adjunction and let `e : L ≅ L'` be an isomorphism of its left adjoint
with another functor.  Then `CategoryTheory.Adjunction.ofNatIsoLeft` transports the adjunction
to `adj.ofNatIsoLeft e : L' ⊣ R`, and this file records what that does to conjugates: replacing
`adj` by `adj.ofNatIsoLeft e` in a conjugate amounts to composing the 2-cell of left adjoints
with `e`.

## Main results

* `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft_hom`: the conjugate of `e` itself, with
  respect to the transported adjunction and the original one, is the identity of `R`.
* `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft_left` and
  `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft_right`: changing the left adjoint of the
  first, respectively the second, adjunction of a conjugate composes the 2-cell with `e`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Stacks.CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

/-- For an adjunction `adj : L ⊣ R` and an isomorphism `e : L ≅ L'`, the conjugate of `e.hom`
with respect to `adj.ofNatIsoLeft e` and `adj` is the identity of `R`. -/
theorem conjugateEquiv_ofNatIsoLeft_hom {L L' : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (e : L ≅ L') :
    conjugateEquiv (adj.ofNatIsoLeft e) adj e.hom = 𝟙 R := by
  ext d
  refine (adj.homEquiv (R.obj d) d).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, conjugateEquiv_counit]
  simp [Adjunction.ofNatIsoLeft]

/-- For `e : L₁ ≅ L₁'`, the conjugate of a 2-cell `α : L₂ ⟶ L₁'` with respect to the
transported adjunction is the conjugate of `α ≫ e.inv` with respect to the original one. -/
theorem conjugateEquiv_ofNatIsoLeft_left {L₁ L₁' L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁)
    (e : L₁ ≅ L₁') (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁') :
    conjugateEquiv (adj₁.ofNatIsoLeft e) adj₂ α = conjugateEquiv adj₁ adj₂ (α ≫ e.inv) := by
  have h := conjugateEquiv_comp (adj₁ := adj₁.ofNatIsoLeft e) (adj₂ := adj₁) (adj₃ := adj₂)
    (α := e.hom) (β := α ≫ e.inv)
  rw [conjugateEquiv_ofNatIsoLeft_hom, Category.id_comp, Category.assoc, e.inv_hom_id,
    Category.comp_id] at h
  exact h.symm

/-- For `e : L₂ ≅ L₂'`, the conjugate of a 2-cell `α : L₂' ⟶ L₁` with respect to the
transported adjunction is the conjugate of `e.hom ≫ α` with respect to the original one. -/
theorem conjugateEquiv_ofNatIsoLeft_right {L₁ L₂ L₂' : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₂') (α : L₂' ⟶ L₁) :
    conjugateEquiv adj₁ (adj₂.ofNatIsoLeft e) α = conjugateEquiv adj₁ adj₂ (e.hom ≫ α) := by
  have h := conjugateEquiv_comp (adj₁ := adj₁) (adj₂ := adj₂.ofNatIsoLeft e) (adj₃ := adj₂)
    (α := α) (β := e.hom)
  rwa [conjugateEquiv_ofNatIsoLeft_hom, Category.comp_id] at h

end Stacks.CategoryTheory

end
