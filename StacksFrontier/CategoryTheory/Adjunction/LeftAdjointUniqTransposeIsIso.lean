module

public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# Invertibility of a transpose along two adjunctions of one functor

Let `adj₁ : L₁ ⊣ R` and `adj₂ : L₂ ⊣ R` be two adjunctions with the same right adjoint. The two
transposes of one morphism `g : X ⟶ R Y` differ by the canonical comparison of the two left
adjoints, so one is invertible exactly when the other is. This file proves that in the forms a
comparison map arrives in: the right adjoints only isomorphic, and the two morphisms being
transposed related by a square whose vertical sides are isomorphisms.

## Main results

* `CategoryTheory.Adjunction.homEquiv_symm_eq_leftAdjointUniq_inv_app_comp`
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_rightAdjointEq`
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_natIsoRight`
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_square`
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_isoSquare`

The transposition identity they rest on is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_app_comp`.
-/

@[expose] public section

universe v₀ v₁ u₀ u₁

namespace CategoryTheory.Adjunction

open CategoryTheory

variable {C : Type u₀} {D : Type u₁} [Category.{v₀} C] [Category.{v₁} D]

/-- The transpose of a morphism `g : X ⟶ R Y` for one of two adjunctions of `R` is the comparison
of the two left adjoints followed by its transpose for the other.

This is `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_app_comp` with the transpose on
the inside rather than the morphism. -/
public theorem homEquiv_symm_eq_leftAdjointUniq_inv_app_comp {L₁ L₂ : C ⥤ D} {R : D ⥤ C}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) {X : C} {Y : D} (g : X ⟶ R.obj Y) :
    (adj₂.homEquiv X Y).symm g =
      (leftAdjointUniq adj₁ adj₂).inv.app X ≫ (adj₁.homEquiv X Y).symm g :=
  (adj₂.homEquiv X Y).injective (by
    rw [Equiv.apply_symm_apply, homEquiv_leftAdjointUniq_inv_app_comp,
      Equiv.apply_symm_apply])

/-- **A transpose is invertible for one of two adjunctions of a functor exactly when it is
invertible for the other.** Let `adj₁ : L₁ ⊣ R` and `adj₂ : L₂ ⊣ R` be two adjunctions with the
same right adjoint and let `g : X ⟶ R Y`.  The two transposes of `g`, one out of `L₁ X` and one
out of `L₂ X`, differ by the canonical comparison of the two left adjoints, which is invertible.

Invertibility of a 2-cell and of its mate are in general different conditions — the
Beck–Chevalley phenomenon — so this is a statement about *one* morphism transposed along two
adjunctions of *one* functor, not about mates of a square. -/
public theorem isIso_homEquiv_symm_iff_of_rightAdjointEq {L₁ L₂ : C ⥤ D} {R : D ⥤ C}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) {X : C} {Y : D} (g : X ⟶ R.obj Y) :
    IsIso ((adj₁.homEquiv X Y).symm g) ↔ IsIso ((adj₂.homEquiv X Y).symm g) := by
  rw [homEquiv_symm_eq_leftAdjointUniq_inv_app_comp adj₁ adj₂ g,
    isIso_comp_left_iff ((leftAdjointUniq adj₁ adj₂).inv.app X)]

/-- **A transpose is invertible for one of two adjunctions of isomorphic functors exactly when it
is invertible for the other.** Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions whose
right adjoints are isomorphic by `e : R₁ ≅ R₂`, and let `g : X ⟶ R₁ Y`.  Then the transpose of
`g` along `adj₁` is invertible exactly when the transpose of `g ≫ e_Y` along `adj₂` is.

This is `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_rightAdjointEq` at
`adj₂.ofNatIsoRight e.symm`, the second adjunction read with the first right adjoint. -/
public theorem isIso_homEquiv_symm_iff_of_natIsoRight {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) {X : C} {Y : D} (g : X ⟶ R₁.obj Y) :
    IsIso ((adj₁.homEquiv X Y).symm g) ↔
      IsIso ((adj₂.homEquiv X Y).symm (g ≫ e.hom.app Y)) := by
  have hiff := isIso_homEquiv_symm_iff_of_rightAdjointEq adj₁ (adj₂.ofNatIsoRight e.symm) g
  rwa [homEquiv_ofNatIsoRight_symm_apply] at hiff

/-- **Two transposes related by a square with invertible vertical sides are invertible
together.** Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions with `e : R₁ ≅ R₂`, let
`α : X₁ ≅ X₂` and `β : Y₁ ≅ Y₂` be isomorphisms, and let `u : X₁ ⟶ R₁ Y₁` and `v : X₂ ⟶ R₂ Y₂`
satisfy `u ≫ e_{Y₁} ≫ R₂ β = α ≫ v`.  Then the transpose of `u` along `adj₁` is invertible
exactly when the transpose of `v` along `adj₂` is.

It is the form in which a comparison map is compared with another: two comparison maps built as
transposes over two spellings of one and the same functor, and identified only up to the
isomorphisms `α` and `β` of their sources and targets, are invertible together. -/
public theorem isIso_homEquiv_symm_iff_of_square {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) {X₁ X₂ : C} {Y₁ Y₂ : D} (α : X₁ ≅ X₂)
    (β : Y₁ ≅ Y₂) (u : X₁ ⟶ R₁.obj Y₁) (v : X₂ ⟶ R₂.obj Y₂)
    (hsq : u ≫ e.hom.app Y₁ ≫ R₂.map β.hom = α.hom ≫ v) :
    IsIso ((adj₁.homEquiv X₁ Y₁).symm u) ↔ IsIso ((adj₂.homEquiv X₂ Y₂).symm v) := by
  rw [isIso_homEquiv_symm_iff_of_natIsoRight adj₁ adj₂ e u]
  have hstep : (adj₂.homEquiv X₁ Y₁).symm (u ≫ e.hom.app Y₁) ≫ β.hom =
      L₂.map α.hom ≫ (adj₂.homEquiv X₂ Y₂).symm v := by
    rw [← homEquiv_naturality_right_symm, Category.assoc, hsq,
      homEquiv_naturality_left_symm]
  rw [← isIso_comp_right_iff _ β.hom, hstep,
    isIso_comp_left_iff (L₂.map α.hom) ((adj₂.homEquiv X₂ Y₂).symm v)]

/-- `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_square` for one adjunction: two
morphisms into the right adjoint related by a square whose vertical sides are isomorphisms have
invertible transposes together. -/
public theorem isIso_homEquiv_symm_iff_of_isoSquare {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {X₁ X₂ : C} {Y₁ Y₂ : D} (α : X₁ ≅ X₂) (β : Y₁ ≅ Y₂) (u : X₁ ⟶ R.obj Y₁)
    (v : X₂ ⟶ R.obj Y₂) (hsq : u ≫ R.map β.hom = α.hom ≫ v) :
    IsIso ((adj.homEquiv X₁ Y₁).symm u) ↔ IsIso ((adj.homEquiv X₂ Y₂).symm v) :=
  isIso_homEquiv_symm_iff_of_square adj adj (Iso.refl R) α β u v (by simpa using hsq)

end CategoryTheory.Adjunction

end
