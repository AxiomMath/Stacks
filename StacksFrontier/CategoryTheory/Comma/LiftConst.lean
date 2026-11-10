module

public import Mathlib.CategoryTheory.Comma.Basic

/-!
# Functors into a comma category with constant right-hand side

Given functors `L : A ⥤ T` and `R : B ⥤ T`, a functor `P : C ⥤ A`, an object `Y` of `B` and a
family of morphisms `φ c : L (P c) ⟶ R Y` natural in `c`, the triples `(P c, Y, φ c)` form a
functor `C ⥤ Comma L R` whose morphisms have identity right-hand components. A natural
transformation `P ⟶ P'` together with a morphism `Y ⟶ Y'` compatible with the `φ`'s induces a
natural transformation of such functors.

## Main definitions

* `CategoryTheory.Comma.liftConst`: the functor `c ↦ (P c, Y, φ c)` into `Comma L R`.
* `CategoryTheory.Comma.liftConstHom`: the natural transformation of such functors induced by
  `β : P ⟶ P'` and `g : Y ⟶ Y'`.

## Main results

* `CategoryTheory.Comma.liftConstHom_id`: `liftConstHom` sends `𝟙 P` and `𝟙 Y` to the identity.
* `CategoryTheory.Comma.liftConstHom_comp`: `liftConstHom` sends composites to composites.

## Implementation notes

The functor laws are proved here once, at variable categories: at concrete categories in which a
composite of identities is expensive to compare with an identity, nothing has to be unfolded.
-/

@[expose] public section

namespace CategoryTheory.Comma

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T] {C : Type u₄} [Category.{v₄} C] {L : A ⥤ T} {R : B ⥤ T}

/-- **The functor `c ↦ (P c, Y, φ c)`** into a comma category. -/
@[simps]
def liftConst (P : C ⥤ A) (Y : B) (φ : ∀ c, L.obj (P.obj c) ⟶ R.obj Y)
    (hφ : ∀ {c' c : C} (u : c' ⟶ c), L.map (P.map u) ≫ φ c = φ c') : C ⥤ Comma L R where
  obj c := ⟨P.obj c, Y, φ c⟩
  map {c' c} u := ⟨P.map u, 𝟙 Y, by rw [R.map_id, Category.comp_id, hφ u]⟩
  map_id c := Comma.hom_ext _ _ (P.map_id c) rfl
  map_comp u v := Comma.hom_ext _ _ (P.map_comp u v) (Category.comp_id (𝟙 Y)).symm

/-- **The natural transformation of functors `c ↦ (P c, Y, φ c)`** induced by a natural
transformation `P ⟶ P'` and a compatible morphism `Y ⟶ Y'`. -/
@[simps]
def liftConstHom {P P' : C ⥤ A} {Y Y' : B} {φ : ∀ c, L.obj (P.obj c) ⟶ R.obj Y}
    {φ' : ∀ c, L.obj (P'.obj c) ⟶ R.obj Y'}
    (hφ : ∀ {c' c : C} (u : c' ⟶ c), L.map (P.map u) ≫ φ c = φ c')
    (hφ' : ∀ {c' c : C} (u : c' ⟶ c), L.map (P'.map u) ≫ φ' c = φ' c')
    (β : P ⟶ P') (g : Y ⟶ Y') (hβ : ∀ c, L.map (β.app c) ≫ φ' c = φ c ≫ R.map g) :
    liftConst P Y φ hφ ⟶ liftConst P' Y' φ' hφ' where
  app c := ⟨β.app c, g, hβ c⟩
  naturality _ _ u := Comma.hom_ext _ _ (β.naturality u)
    ((Category.id_comp g).trans (Category.comp_id g).symm)

/-- The natural transformation `liftConstHom` induced by `β = 𝟙 P` and `g = 𝟙 Y` is the
identity. -/
theorem liftConstHom_id {P : C ⥤ A} {Y : B} {φ : ∀ c, L.obj (P.obj c) ⟶ R.obj Y}
    (hφ : ∀ {c' c : C} (u : c' ⟶ c), L.map (P.map u) ≫ φ c = φ c')
    (β : P ⟶ P) (g : Y ⟶ Y) (hβ : ∀ c, L.map (β.app c) ≫ φ c = φ c ≫ R.map g)
    (hβ₁ : β = 𝟙 P) (hg₁ : g = 𝟙 Y) :
    liftConstHom hφ hφ β g hβ = 𝟙 _ := by
  subst hβ₁ hg₁
  exact NatTrans.ext (funext fun c => Comma.hom_ext _ _ rfl rfl)

/-- The natural transformation `liftConstHom` induced by the composites `β ≫ β'` and `g ≫ g'` is
the composite of those induced by `β, g` and by `β', g'`. -/
theorem liftConstHom_comp {P P' P'' : C ⥤ A} {Y Y' Y'' : B} {φ : ∀ c, L.obj (P.obj c) ⟶ R.obj Y}
    {φ' : ∀ c, L.obj (P'.obj c) ⟶ R.obj Y'} {φ'' : ∀ c, L.obj (P''.obj c) ⟶ R.obj Y''}
    (hφ : ∀ {c' c : C} (u : c' ⟶ c), L.map (P.map u) ≫ φ c = φ c')
    (hφ' : ∀ {c' c : C} (u : c' ⟶ c), L.map (P'.map u) ≫ φ' c = φ' c')
    (hφ'' : ∀ {c' c : C} (u : c' ⟶ c), L.map (P''.map u) ≫ φ'' c = φ'' c')
    (β : P ⟶ P') (g : Y ⟶ Y') (hβ : ∀ c, L.map (β.app c) ≫ φ' c = φ c ≫ R.map g)
    (β' : P' ⟶ P'') (g' : Y' ⟶ Y'') (hβ' : ∀ c, L.map (β'.app c) ≫ φ'' c = φ' c ≫ R.map g')
    (β'' : P ⟶ P'') (g'' : Y ⟶ Y'') (hβ'' : ∀ c, L.map (β''.app c) ≫ φ'' c = φ c ≫ R.map g'')
    (hcomp : β'' = β ≫ β') (hg : g'' = g ≫ g') :
    liftConstHom hφ hφ'' β'' g'' hβ'' =
      liftConstHom hφ hφ' β g hβ ≫ liftConstHom hφ' hφ'' β' g' hβ' := by
  subst hcomp hg
  exact NatTrans.ext (funext fun c => Comma.hom_ext _ _ rfl rfl)

end CategoryTheory.Comma

end
