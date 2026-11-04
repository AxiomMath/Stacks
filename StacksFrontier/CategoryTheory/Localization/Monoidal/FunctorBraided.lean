module

public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-!
# Braided functors out of a braided localization

Let `L : C ⥤ D` be a braided monoidal localization functor and `F : D ⥤ E` a functor which lifts
along `L` to a braided monoidal functor `G : C ⥤ E`. Then the monoidal structure
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` on `F` is braided.

## Main definitions

* `CategoryTheory.Localization.Monoidal.functorBraidedOfComp`

## Main results

* `CategoryTheory.Functor.LaxMonoidal.braided_of_iso`: the braiding axiom of a lax monoidal
  functor at a pair of objects only depends on the pair up to isomorphism.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

/-- **The braiding axiom of a lax monoidal functor transports along isomorphisms**: if it holds
at `(X, Y)`, it holds at every pair isomorphic to `(X, Y)`. -/
theorem Functor.LaxMonoidal.braided_of_iso {D : Type u₂} {E : Type u₃} [Category.{v₂} D]
    [Category.{v₃} E]
    [MonoidalCategory D] [MonoidalCategory E] [BraidedCategory D] [BraidedCategory E]
    (F : D ⥤ E) [F.LaxMonoidal] {X Y X' Y' : D} (a : X ≅ X') (b : Y ≅ Y')
    (h : μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X) :
    μ F X' Y' ≫ F.map (β_ X' Y').hom = (β_ (F.obj X') (F.obj Y')).hom ≫ μ F Y' X' := by
  rw [← cancel_epi (F.map a.hom ⊗ₘ F.map b.hom), μ_natural_assoc, ← Functor.map_comp,
    BraidedCategory.braiding_naturality, Functor.map_comp, reassoc_of% h,
    BraidedCategory.braiding_naturality_assoc, μ_natural]

namespace Localization.Monoidal

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} [Category.{v₁} C] [Category.{v₂} D]
  [Category.{v₃} E] [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Braided]
  (F : D ⥤ E) (G : C ⥤ E) [G.Braided] [W.ContainsIdentities] [Lifting L W G F]

/-- The braiding axiom of `functorMonoidalOfComp` at the images of two objects. -/
private theorem functorMonoidalOfComp_braided_obj (X Y : C) :
    letI := functorMonoidalOfComp L W F G
    Functor.LaxMonoidal.μ F (L.obj X) (L.obj Y) ≫ F.map (β_ (L.obj X) (L.obj Y)).hom =
      (β_ (F.obj (L.obj X)) (F.obj (L.obj Y))).hom ≫
        Functor.LaxMonoidal.μ F (L.obj Y) (L.obj X) := by
  let := functorMonoidalOfComp L W F G
  have hβ : (β_ (L.obj X) (L.obj Y)).hom =
      Functor.LaxMonoidal.μ L X Y ≫ L.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ L Y X := by
    rw [Functor.map_braiding, assoc, assoc, Functor.Monoidal.μ_δ, comp_id,
      Functor.Monoidal.μ_δ_assoc]
  have he : (Lifting.iso L W G F).inv.app (X ⊗ Y) ≫ F.map (L.map (β_ X Y).hom) =
      G.map (β_ X Y).hom ≫ (Lifting.iso L W G F).inv.app (Y ⊗ X) :=
    ((Lifting.iso L W G F).inv.naturality (β_ X Y).hom).symm
  rw [functorMonoidalOfComp_μ, functorMonoidalOfComp_μ, hβ, assoc, assoc, assoc,
    ← Functor.map_comp, Functor.Monoidal.δ_μ_assoc, Functor.map_comp, reassoc_of% he,
    Functor.LaxBraided.braided_assoc, BraidedCategory.braiding_naturality_assoc]
  rfl

/-- **A functor out of a braided localization which lifts to a braided monoidal functor is
braided**, for the monoidal structure `functorMonoidalOfComp`. -/
@[instance_reducible]
noncomputable def functorBraidedOfComp : F.Braided :=
  letI := functorMonoidalOfComp L W F G
  { braided := fun X' Y' ↦ by
      have := Localization.essSurj L W
      exact Functor.LaxMonoidal.braided_of_iso F (L.objObjPreimageIso X')
        (L.objObjPreimageIso Y')
        (functorMonoidalOfComp_braided_obj L W F G (L.objPreimage X') (L.objPreimage Y')) }

/-- The braided structure `functorBraidedOfComp` extends `functorMonoidalOfComp`. -/
lemma functorBraidedOfComp_toMonoidal :
    (functorBraidedOfComp L W F G).toMonoidal = functorMonoidalOfComp L W F G :=
  rfl

end Localization.Monoidal

end CategoryTheory
