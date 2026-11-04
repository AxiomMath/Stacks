module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Iso

/-!
# Natural transformations out of a reflector are determined by the unit

Let `L ⊣ R` be an adjunction whose counit is an isomorphism, so that `R` is fully faithful and
`L ⋙ R` is an idempotent monad with unit `η`. If `H` is a functor which inverts every morphism
inverted by `L`, then a natural transformation `ρ : L ⋙ R ⟶ H` is determined by its composite
`η ≫ ρ` with the unit.

## Main results

* `CategoryTheory.Adjunction.natTrans_ext_of_unit_comp`: two natural transformations
  `L ⋙ R ⟶ H` with equal composites with the unit are equal.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}

/-- At an object in the image of `R` the unit of an adjunction with invertible counit is an
isomorphism. -/
theorem isIso_unit_app_obj_of_isIso_counit (adj : L ⊣ R) [IsIso adj.counit] (Y : D) :
    IsIso (adj.unit.app (R.obj Y)) :=
  have : IsIso (adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y)) := by
    rw [adj.right_triangle_components Y]; exact IsIso.id _
  IsIso.of_isIso_comp_right _ (R.map (adj.counit.app Y))

/-- The left adjoint of an adjunction with invertible counit inverts every component of the
unit. -/
theorem isIso_map_unit_app_of_isIso_counit (adj : L ⊣ R) [IsIso adj.counit] (X : C) :
    IsIso (L.map (adj.unit.app X)) :=
  have : IsIso (L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X)) := by
    rw [adj.left_triangle_components X]; exact IsIso.id _
  IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj X))

/-- **Natural transformations out of a reflector are determined by the unit.** Let `L ⊣ R`
have invertible counit and let `H` invert every morphism which `L` inverts. Two natural
transformations `ρ ρ' : L ⋙ R ⟶ H` with `η ≫ ρ = η ≫ ρ'` are equal. -/
theorem natTrans_ext_of_unit_comp (adj : L ⊣ R) [IsIso adj.counit] {H : C ⥤ C}
    (hH : ∀ ⦃X Y : C⦄ (φ : X ⟶ Y), IsIso (L.map φ) → IsIso (H.map φ))
    {ρ ρ' : L ⋙ R ⟶ H} (h : adj.unit ≫ ρ = adj.unit ≫ ρ') : ρ = ρ' := by
  ext X
  have := isIso_unit_app_obj_of_isIso_counit adj (L.obj X)
  have := hH _ (isIso_map_unit_app_of_isIso_counit adj X)
  have key : ∀ σ : L ⋙ R ⟶ H, σ.app X = (L ⋙ R).map (adj.unit.app X) ≫
      inv (adj.unit.app (R.obj (L.obj X))) ≫ (adj.unit ≫ σ).app (R.obj (L.obj X)) ≫
        inv (H.map (adj.unit.app X)) := by
    intro σ
    have hn : (L ⋙ R).map (adj.unit.app X) ≫ σ.app (R.obj (L.obj X)) =
        σ.app X ≫ H.map (adj.unit.app X) := σ.naturality _
    rw [NatTrans.comp_app, Category.assoc, IsIso.inv_hom_id_assoc, ← Category.assoc, hn,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [key ρ, key ρ', h]

end CategoryTheory.Adjunction
