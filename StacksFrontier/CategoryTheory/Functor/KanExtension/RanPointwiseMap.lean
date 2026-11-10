module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# `ran.map` read on the limit cones of a pointwise right Kan extension

For a functor `L : C ⥤ D` along which right Kan extensions exist, the value
`(L.ran.obj W).obj X` of the right Kan extension of `W` at an object `X` of `D` is, when the
extension is pointwise, the limit of `W` over the structured arrow category of `X` under `L`; the
cone is `CategoryTheory.Functor.RightExtension.coneAt` of the extension given by
`CategoryTheory.Functor.ranCounit`.

This module records the one compatibility this presentation needs and Mathlib does not state: the
morphism `(L.ran.map τ).app X` induced by a morphism `τ : W₁ ⟶ W₂` of coefficients is the
comparison of those two limits, i.e. its composite with a projection of the second cone is the
corresponding projection of the first followed by `τ`.

## Main results

* `CategoryTheory.Functor.ran_map_app_comp_coneAt_π` — the compatibility above.  It is naturality
  of `L.ran.map τ` together with naturality of the Kan extension counit in the coefficients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃} [Category.{v₁} C] [Category.{v₂} D]
  [Category.{v₃} H] (L : C ⥤ D) [∀ W : C ⥤ H, L.HasRightKanExtension W]

/-- **The morphism induced on right Kan extensions by a morphism of coefficients is the
comparison of the limit cones.**  Read against the projection of the cone
`RightExtension.coneAt` at a structured arrow, `(L.ran.map τ).app X` is the projection of the
cone of the source followed by `τ`.

Both sides are the composite `(L.ran.obj W₁).map d.hom` with the counit at `d.right` and with
`τ`, in the two possible orders: this is naturality of `L.ran.map τ` in `D` together with
naturality of `L.ranCounit` in the coefficients. -/
theorem ran_map_app_comp_coneAt_π {W₁ W₂ : C ⥤ H} (τ : W₁ ⟶ W₂) (X : D)
    (d : StructuredArrow X L) :
    (L.ran.map τ).app X ≫ ((RightExtension.mk _ (L.ranCounit.app W₂)).coneAt X).π.app d =
      ((RightExtension.mk _ (L.ranCounit.app W₁)).coneAt X).π.app d ≫ τ.app d.right := by
  have hnat : (L.ran.map τ).app X ≫ (L.ran.obj W₂).map d.hom =
      (L.ran.obj W₁).map d.hom ≫ (L.ran.map τ).app (L.obj d.right) :=
    ((L.ran.map τ).naturality d.hom).symm
  have hcounit : (L.ran.map τ).app (L.obj d.right) ≫ (L.ranCounit.app W₂).app d.right =
      (L.ranCounit.app W₁).app d.right ≫ τ.app d.right :=
    congr_app (L.ranCounit.naturality τ) d.right
  change (L.ran.map τ).app X ≫ (L.ran.obj W₂).map d.hom ≫ (L.ranCounit.app W₂).app d.right =
    ((L.ran.obj W₁).map d.hom ≫ (L.ranCounit.app W₁).app d.right) ≫ τ.app d.right
  rw [← Category.assoc, hnat, Category.assoc, hcounit, Category.assoc]

end CategoryTheory.Functor

end
