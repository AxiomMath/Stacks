module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# The canonical map to the global sections of a direct image

Global sections of a direct image along a continuous functor `u` are reached from the global
sections downstairs with nothing to prove, provided one uses the *limit* description of
`CategoryTheory.Sheaf.Γ`: a global section of `H` restricts to each object `u V`, those
restrictions form a cone over the underlying presheaf of `u_* H`, and
`CategoryTheory.Sheaf.isLimitConeΓ` turns that cone into a map.

## Main results

* `CategoryTheory.Sheaf.ΓPushforwardComparison`: the map.
* `CategoryTheory.Sheaf.ΓRes_ΓPushforwardComparison`: its restriction compatibility, which is the
  limit's `fac`.

## Implementation notes

The only hypothesis on `u` is `u.IsContinuous J K`. No morphism of sites, terminal object, finality
of `u` or left exactness of its inverse image is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v₂ u₂

namespace CategoryTheory.Sheaf

variable {A : Type u} [Category.{v} A] {B : Type u} [Category.{v} B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  (W : Type u₂) [Category.{v₂} W]
  [HasWeakSheafify J W] [HasWeakSheafify K W]
  [HasGlobalSectionsFunctor J W] [HasGlobalSectionsFunctor K W]
  [u.IsContinuous J K]

/-- **The canonical map from the global sections of a sheaf to the global sections of its direct
image.** The restrictions of a global section of `H` to the objects `u V` form a cone over the
underlying presheaf of `u_* H` — it is `CategoryTheory.Sheaf.coneΓ` of `H` whiskered by `u.op` —
and global sections of `u_* H` are the limit of that presheaf. -/
noncomputable def ΓPushforwardComparison (H : Sheaf K W) :
    (Γ K W).obj H ⟶ (Γ J W).obj ((u.sheafPushforwardContinuous W J K).obj H) :=
  ((u.sheafPushforwardContinuous W J K).obj H).isLimitConeΓ.lift (H.coneΓ.whisker u.op)

/-- **The canonical map to the global sections of a direct image is compatible with
restrictions**: restricting its value to `V` is restricting the original global section to `u V`.
This is `CategoryTheory.Limits.IsLimit.fac` for the cone that defines the map. -/
@[simp]
lemma ΓRes_ΓPushforwardComparison (H : Sheaf K W) (V : Aᵒᵖ) :
    ΓPushforwardComparison u J K W H ≫
        ((u.sheafPushforwardContinuous W J K).obj H).ΓRes V =
      H.ΓRes (u.op.obj V) :=
  ((u.sheafPushforwardContinuous W J K).obj H).isLimitConeΓ.fac _ V

omit [HasWeakSheafify J W] [HasWeakSheafify K W]
  [HasGlobalSectionsFunctor J W] [HasGlobalSectionsFunctor K W] in
/-- **The right adjunct of a morphism out of an inverse image, read at an object.** For any
adjunction whose right adjoint is the direct image along `u`, the component at `V` of the adjunct
of `ψ` is the component of the unit at `V` followed by the component of `ψ` at `u V`. -/
lemma rightAdjunct_hom_app {L : Sheaf J W ⥤ Sheaf K W}
    (adj : L ⊣ u.sheafPushforwardContinuous W J K) {P : Sheaf J W} {H : Sheaf K W}
    (ψ : L.obj P ⟶ H) (V : Aᵒᵖ) :
    (adj.homEquiv P H ψ).hom.app V =
      (adj.unit.app P).hom.app V ≫ ψ.hom.app (u.op.obj V) := by
  rw [adj.homEquiv_unit]
  rfl

end CategoryTheory.Sheaf

end
