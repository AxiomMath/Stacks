module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Descending a transformation of precomposites along a left adjoint with invertible counit

Let `adj : L ⊣ R` be an adjunction whose counit is invertible, so that `R` is fully faithful and
`R ⋙ L ≅ 𝟭`, and let `A B : D ⥤ E` be two functors out of the codomain of `L`. A natural
transformation of the *precomposites* `L ⋙ A ⟶ L ⋙ B` then descends to one of `A ⟶ B`: conjugate
the transformation taken at `R N` by the counit at `N`.

The descent is exact rather than merely up to isomorphism: its component at `L X` is the given
component at `X` on the nose (`CategoryTheory.Adjunction.descend_app_obj`), because the counit at
`L X` is inverse to the image under `L` of the unit at `X`, which is the left triangle identity.

The use this is written for is a question of the form "is this morphism invertible?" which is
known after restricting to an open and is wanted before: a natural transformation defined on the
large category, whiskered into the restriction, becomes a transformation of precomposites, and the
descent is the transformation on the small category to which a rigidity criterion there applies.

## Main definitions

* `CategoryTheory.Adjunction.descend` — the descended transformation `A ⟶ B`.

## Main results

* `CategoryTheory.Adjunction.descend_app_obj` — the descent at `L X` is the original at `X`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.counit] {A B : D ⥤ E}

/-- **A transformation of the precomposites with a left adjoint whose counit is invertible
descends.** Its value at `N` is the value of `ρ` at `R N`, conjugated by the images under `A` and
`B` of the counit at `N`. -/
noncomputable def descend (ρ : L ⋙ A ⟶ L ⋙ B) : A ⟶ B where
  app N := A.map (inv (adj.counit.app N)) ≫ ρ.app (R.obj N) ≫ B.map (adj.counit.app N)
  naturality N N' h := by
    have hε := adj.counit.naturality h
    have hρ := ρ.naturality (R.map h)
    dsimp at hε hρ ⊢
    have key : h ≫ inv (adj.counit.app N') = inv (adj.counit.app N) ≫ L.map (R.map h) := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact hε.symm
    rw [← A.map_comp_assoc, key, A.map_comp, Category.assoc, reassoc_of% hρ, ← B.map_comp, hε,
      B.map_comp]
    simp only [Category.assoc]

/-- The component of the descended transformation at `N`. -/
theorem descend_app (ρ : L ⋙ A ⟶ L ⋙ B) (N : D) :
    (descend adj ρ).app N =
      A.map (inv (adj.counit.app N)) ≫ ρ.app (R.obj N) ≫ B.map (adj.counit.app N) := rfl

/-- The counit at `L X` is inverse to the image under `L` of the unit at `X`: the left triangle
identity exhibits the latter as a one-sided inverse, and a one-sided inverse of an isomorphism is
*the* inverse. -/
theorem inv_counit_app_obj (X : C) : inv (adj.counit.app (L.obj X)) = L.map (adj.unit.app X) :=
  IsIso.inv_eq_of_inv_hom_id (adj.left_triangle_components X)

/-- **The descent recovers the original transformation on the image of `L`**: its component at
`L X` is the component of `ρ` at `X`, on the nose. So invertibility of the descent at `L X` and
invertibility of `ρ` at `X` are the same statement. -/
theorem descend_app_obj (ρ : L ⋙ A ⟶ L ⋙ B) (X : C) :
    (descend adj ρ).app (L.obj X) = ρ.app X := by
  have hρ := ρ.naturality (adj.unit.app X)
  dsimp at hρ
  rw [descend_app, inv_counit_app_obj, ← Category.assoc, hρ, Category.assoc, ← B.map_comp,
    adj.left_triangle_components, B.map_id, Category.comp_id]

end CategoryTheory.Adjunction

end
