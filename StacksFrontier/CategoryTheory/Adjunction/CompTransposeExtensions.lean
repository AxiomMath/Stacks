module

public import StacksFrontier.CategoryTheory.Adjunction.CompTranspose
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Additions to `CompTranspose`

Declarations this development adds alongside `StacksFrontier.CategoryTheory.Adjunction.CompTranspose`,
kept in their own module so that the base file is unchanged: 1 declaration(s) that the base file
does not have, with the section variables, namespaces and options they are stated in.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C]

/-- **A composition law for left adjoints, from its transpose.** Let `adj₁ : L₁ ⊣ R₁`,
`adj₂ : L₂ ⊣ R₂` and `adj : L ⊣ R` be adjunctions together with an isomorphism
`e : R₂ ⋙ R₁ ≅ R`, so that `L₁ ⋙ L₂` and `L` are both left adjoint to `R` and are identified by
uniqueness of left adjoints. Then `L₂` of a morphism `c₁` followed by `c₂` is that
identification followed by `c` as soon as the transposes match: the adjunct of `c₁`, followed by
`R₁` of the adjunct of `c₂`, followed by `e`, is the adjunct of `c`.

This is the step every composition law for a pair of left adjoints given by uniqueness of left
adjoints is proved by; `Stacks.CategoryTheory.homEquiv_comp_map_comp` computes the transpose of
the left-hand side, and the transpose of the right-hand side is `c`'s own. -/
theorem map_comp_eq_leftAdjointUniq_hom_app_comp {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C}
    {R₂ : C ⥤ B} {L : A ⥤ C} {R : C ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) {X : A} {Y : B} {Z : C} (c₁ : L₁.obj X ⟶ Y) (c₂ : L₂.obj Y ⟶ Z)
    (c : L.obj X ⟶ Z)
    (h : adj₁.homEquiv X Y c₁ ≫ R₁.map (adj₂.homEquiv Y Z c₂) ≫ e.hom.app Z =
      adj.homEquiv X Z c) :
    L₂.map c₁ ≫ c₂ =
      (Adjunction.leftAdjointUniq ((adj₁.comp adj₂).ofNatIsoRight e) adj).hom.app X ≫ c := by
  refine (((adj₁.comp adj₂).ofNatIsoRight e).homEquiv X Z).injective ?_
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, homEquiv_comp_map_comp,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, ← h, Category.assoc]

end Stacks.CategoryTheory

end
