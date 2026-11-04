module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # The colimit-indexing category `I^u_V`

For a functor `u : C ⥤ D` and an object `V : D`, Stacks 07 §5 describes a category `I^u_V` by
```
Ob(I^u_V)                        = {(U, φ) | U : C, φ : V ⟶ u U}
Mor_{I^u_V}((U, φ), (U', φ'))    = {f : U ⟶ U' | u f ∘ φ = φ'}
```
That category is the structured arrow category `V ↓ u`, which is
`CategoryTheory.StructuredArrow V u` in Mathlib. This file identifies `I^u_V` with it and proves
the two displayed descriptions as type-level equivalences.

## Main results

* `ColimCategory.I`: the indexing category `I^u_V`.
* `ColimCategory.objEquiv`: its objects are the dependent pairs `Σ U : C, (V ⟶ u U)`
  (Stacks 053L, object description).
* `ColimCategory.homEquiv`: its morphisms `(U, φ) ⟶ (U', φ')` are the morphisms `f : U ⟶ U'`
  of `C` with `φ ≫ u f = φ'` (Stacks 053L, morphism description).
* `ColimCategory.objEquiv_mk`, `ColimCategory.homEquiv_homMk`, `ColimCategory.homEquiv_id`,
  `ColimCategory.homEquiv_comp`: compatibility of these equivalences with `StructuredArrow.mk`,
  `StructuredArrow.homMk`, identities and composition.

Tags covered: 053L.
-/

@[expose] public section

namespace ColimCategory

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (V : D)

/-- The indexing category `I^u_V`, defined to be the structured arrow category `V ↓ u` from
Mathlib. Its objects are pairs `(U, φ)` with `U : C` and `φ : V ⟶ u U`, and its morphisms
`(U, φ) ⟶ (U', φ')` are morphisms `f : U ⟶ U'` in `C` such that `φ ≫ u f = φ'`. -/
abbrev I : Type max u₁ v₂ := CategoryTheory.StructuredArrow V u

/-- The type of *objects* of `I^u_V` is exactly the comprehension
`{(U, φ) | U : Ob C, φ : V ⟶ u U}`, formalized as the dependent pair type
`Σ U : C, (V ⟶ u U)`. -/
@[stacks 053L "Ob"]
def objEquiv : I u V ≃ Σ U : C, (V ⟶ u.obj U) where
  toFun X := ⟨X.right, X.hom⟩
  invFun p := StructuredArrow.mk p.2
  left_inv X := by
    cases X
    rfl
  right_inv p := rfl

/-- The type of *morphisms* in `I^u_V` from `(U, φ)` to `(U', φ')` is exactly the comprehension
`{f : U ⟶ U' | u f ∘ φ = φ'}`, formalized as the subtype of morphisms `f : U ⟶ U'` satisfying
`φ ≫ u f = φ'` (note the diagrammatic-order composition in Mathlib). -/
@[stacks 053L "Mor"]
def homEquiv (X Y : I u V) :
    (X ⟶ Y) ≃ { f : X.right ⟶ Y.right // X.hom ≫ u.map f = Y.hom } where
  toFun g := ⟨g.right, StructuredArrow.w g⟩
  invFun f := StructuredArrow.homMk f.1 f.2
  left_inv g := by
    ext
    rfl
  right_inv f := rfl

/-- Compatibility: the object equivalence sends `StructuredArrow.mk φ` to the pair
`⟨U, φ⟩`, matching the comprehension notation `(U, φ)`. -/
theorem objEquiv_mk (U : C) (φ : V ⟶ u.obj U) :
    objEquiv u V (StructuredArrow.mk φ) = ⟨U, φ⟩ := rfl

/-- Compatibility: the morphism equivalence sends `StructuredArrow.homMk f h` to
the pair `⟨f, h⟩`, matching the comprehension notation. -/
theorem homEquiv_homMk (X Y : I u V) (f : X.right ⟶ Y.right)
    (h : X.hom ≫ u.map f = Y.hom) :
    homEquiv u V X Y (StructuredArrow.homMk f h) = ⟨f, h⟩ := rfl

/-- The identity morphism in `I^u_V` corresponds (under `homEquiv`) to the identity of the
underlying object of `C`. -/
theorem homEquiv_id (X : I u V) :
    (homEquiv u V X X (𝟙 X)).1 = 𝟙 X.right := rfl

/-- Composition in `I^u_V` corresponds (under `homEquiv`) to composition of the underlying
morphisms in `C`. -/
theorem homEquiv_comp {X Y Z : I u V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (homEquiv u V X Z (f ≫ g)).1 = (homEquiv u V X Y f).1 ≫ (homEquiv u V Y Z g).1 :=
  rfl

end ColimCategory
