module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward

/-!
# The projection formula at the unit as a natural transformation

For an adjunction `F ⊣ G` between categories with tensor bifunctors `TC`, `TD`, a comparison `μ`
of `F` with the tensor products and a left unitor `lam : O ⊗ - ≅ 𝟭` on `D`, the projection
formula map at the unit `G O ⊗ N ⟶ G(O ⊗ F N) ≅ G F N`
(`CategoryTheory.PullbackInternalHom.projectionUnitMap`) is natural in `N`.

## Main definitions

* `CategoryTheory.PullbackInternalHom.projectionUnitNatTrans`: `G O ⊗ - ⟶ F ⋙ G`.
-/

@[expose] public section

namespace CategoryTheory.PullbackInternalHom

open scoped CategoryTheory.Prod

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
  (O : D) (lam : TD.obj O ≅ 𝟭 D)

/-- **The projection formula at the unit is natural**: `ρ_N : G O ⊗ N ⟶ G F N` is the component
at `N` of a natural transformation `G O ⊗ - ⟶ F ⋙ G`. -/
def projectionUnitNatTrans : TC.obj (G.obj O) ⟶ F ⋙ G where
  app N := projectionUnitMap adj TC TD μ O lam N
  naturality N N' k := by
    have h := adjunctionTensorMap_natural adj (Functor.uncurry.obj TC)
      (Functor.uncurry.obj TD) μ.hom (𝟙 O) k
    have hl := lam.hom.naturality (F.map k)
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Functor.id_map] at h hl
    simp only [projectionUnitMap, Functor.comp_map, ← Category.assoc, h]
    simp only [Category.assoc, ← G.map_comp, hl, Functor.id_obj]

/-- The component of `projectionUnitNatTrans` at `N` is `projectionUnitMap` at `N`. -/
@[simp]
lemma projectionUnitNatTrans_app (N : C) :
    (projectionUnitNatTrans adj TC TD μ O lam).app N = projectionUnitMap adj TC TD μ O lam N :=
  rfl

end CategoryTheory.PullbackInternalHom
