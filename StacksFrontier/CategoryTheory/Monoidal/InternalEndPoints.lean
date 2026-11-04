module

public import StacksFrontier.CategoryTheory.Monoidal.InternalEndMonoid
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The points of an internal endomorphism monoid are the endomorphisms

Let `C` be a monoidal closed category and `X` an object. A *point* of an object `A` of `C` is a
morphism `𝟙_ C ⟶ A`, and `CategoryTheory.MonoidalClosed.curryHomEquiv'` identifies the points of
the internal hom `X ⟶[C] Y` with the morphisms `X ⟶ Y`. This file records that for `Y = X` the
identification is multiplicative for the monoid structure of
`CategoryTheory.MonoidalClosed.internalEnd`: the unit of the monoid is the identity of `X`, and
the multiplication of two points is the composite of the two morphisms.

Consequently a morphism of monoid objects `θ : internalEnd X ⟶ internalEnd Y` induces a map
`MonoidalClosed.pointMap θ : (X ⟶ X) → (Y ⟶ Y)` which preserves the identity and composition, and
is a bijection when `θ` is an isomorphism.

## Main definitions

* `CategoryTheory.MonoidalClosed.pointMap`: the map on endomorphisms induced by a morphism of
  internal endomorphism monoids.

## Main results

* `CategoryTheory.MonoidalClosed.one_hom_comp` and
  `CategoryTheory.MonoidalClosed.mul_hom_comp`: a morphism of internal endomorphism monoids
  commutes with `MonoidalClosed.id` and `MonoidalClosed.comp`, which are the unit and the
  multiplication of `internalEnd`.
* `CategoryTheory.MonoidalClosed.pointMap_id` and `CategoryTheory.MonoidalClosed.pointMap_comp`:
  **the induced map on endomorphisms preserves the identity and composition.**
* `CategoryTheory.MonoidalClosed.pointMap_internalEndCongr`: for the isomorphism induced by
  `e : X ≅ Y` the induced map is conjugation by `e`.
* `CategoryTheory.MonoidalClosed.pointEquiv`: an isomorphism of internal endomorphism monoids
  induces a bijection of the endomorphism monoids.
* `CategoryTheory.MonoidalClosed.curry'_comp_inv_hom_eq_iff`: **two isomorphisms of a monoid
  object with `internalEnd X` read an endomorphism of `X` as the same point exactly when the
  comparison automorphism fixes that endomorphism.**
* `CategoryTheory.MonoidalClosed.curry'_add`, `CategoryTheory.MonoidalClosed.uncurry'_add` and
  `CategoryTheory.MonoidalClosed.pointMap_add`: in a preadditive monoidal closed category whose
  tensor product is additive, the identification and the induced map are additive, so the induced
  map is a morphism of rings, and a ring isomorphism when `θ` is an isomorphism.

## Implementation notes

Everything here is formal: the two laws come from Mathlib's `MonoidalClosed.curry'_id` and
`MonoidalClosed.curry'_comp` together with `CategoryTheory.IsMonHom.one_hom` and
`CategoryTheory.IsMonHom.mul_hom`, and `internalEnd`'s unit and multiplication are
`MonoidalClosed.id` and `MonoidalClosed.comp` by definition
(`CategoryTheory.MonoidalClosed.internalEnd_one` and `internalEnd_mul`).

Additivity is separated out because it needs the tensor product to be additive
(`CategoryTheory.MonoidalPreadditive`), which the multiplicative statements do not.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- A morphism of internal endomorphism monoids sends the unit `MonoidalClosed.id X` to
`MonoidalClosed.id Y`. -/
theorem one_hom_comp {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) :
    MonoidalClosed.id X ≫ θ.hom = MonoidalClosed.id Y :=
  IsMonHom.one_hom θ.hom

/-- A morphism `θ` of internal endomorphism monoids commutes with the multiplications
`MonoidalClosed.comp X X X` and `MonoidalClosed.comp Y Y Y`. -/
theorem mul_hom_comp {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) :
    MonoidalClosed.comp X X X ≫ θ.hom = (θ.hom ⊗ₘ θ.hom) ≫ MonoidalClosed.comp Y Y Y :=
  IsMonHom.mul_hom θ.hom

/-- The map on endomorphisms induced by a morphism `internalEnd X ⟶ internalEnd Y` of monoid
objects: read an endomorphism of `X` as a point of `internalEnd X`, push it forward, and read the
result as an endomorphism of `Y`. -/
def pointMap {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) (f : X ⟶ X) : Y ⟶ Y :=
  uncurry' (curry' f ≫ θ.hom)

/-- The point of `internalEnd Y` corresponding to `pointMap θ f` is the image under `θ` of the
point corresponding to `f`. -/
@[simp]
theorem curry'_pointMap {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) (f : X ⟶ X) :
    curry' (pointMap θ f) = curry' f ≫ θ.hom :=
  curry'_uncurry' _

/-- **The induced map on endomorphisms preserves the identity.** -/
@[simp]
theorem pointMap_id {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) :
    pointMap θ (𝟙 X) = 𝟙 Y := by
  apply curry'_injective
  rw [curry'_pointMap, curry'_id, curry'_id, one_hom_comp]

/-- **The induced map on endomorphisms preserves composition.** -/
theorem pointMap_comp {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) (f g : X ⟶ X) :
    pointMap θ (f ≫ g) = pointMap θ f ≫ pointMap θ g := by
  apply curry'_injective
  rw [curry'_pointMap, curry'_comp f g, curry'_comp (pointMap θ f) (pointMap θ g),
    curry'_pointMap, curry'_pointMap, Category.assoc, Category.assoc, mul_hom_comp,
    ← tensorHom_comp_tensorHom_assoc]

/-- The map induced by a composite of morphisms of internal endomorphism monoids. -/
theorem pointMap_trans {X Y Z : C} (θ : internalEnd X ⟶ internalEnd Y)
    (ψ : internalEnd Y ⟶ internalEnd Z) (f : X ⟶ X) :
    pointMap (θ ≫ ψ) f = pointMap ψ (pointMap θ f) := by
  apply curry'_injective
  rw [curry'_pointMap, curry'_pointMap, curry'_pointMap, Category.assoc]
  rfl

/-- The identity morphism of `internalEnd X` induces the identity map on endomorphisms of `X`. -/
@[simp]
theorem pointMap_self {X : C} (f : X ⟶ X) : pointMap (𝟙 (internalEnd X)) f = f := by
  apply curry'_injective
  rw [curry'_pointMap]
  simp

/-- **An isomorphism of internal endomorphism monoids induces a bijection of the endomorphism
monoids.** -/
@[simps]
def pointEquiv {X Y : C} (θ : internalEnd X ≅ internalEnd Y) : (X ⟶ X) ≃ (Y ⟶ Y) where
  toFun := pointMap θ.hom
  invFun := pointMap θ.inv
  left_inv f := by rw [← pointMap_trans, θ.hom_inv_id, pointMap_self]
  right_inv g := by rw [← pointMap_trans, θ.inv_hom_id, pointMap_self]

/-- **For the isomorphism of internal endomorphism monoids induced by an isomorphism `e : X ≅ Y`
of objects, the induced map on endomorphisms is conjugation by `e`.** -/
theorem pointMap_internalEndCongr {X Y : C} (e : X ≅ Y) (f : X ⟶ X) :
    pointMap (internalEndCongr e).hom f = e.inv ≫ f ≫ e.hom := by
  have h : (internalEndCongr e).hom.hom = internalEndCongrHom e := rfl
  rw [pointMap, uncurry', h, uncurry_natural_left, uncurry_internalEndCongrHom,
    MonoidalCategory.whisker_exchange_assoc, whiskerLeft_curry'_ihom_ev_app_assoc,
    ← MonoidalCategory.rightUnitor_inv_naturality_assoc]
  simp

omit [MonoidalClosed C] in
/-- The underlying morphism of an isomorphism of monoid objects is an isomorphism. -/
theorem isIso_hom_hom {A B : Mon C} (e : A ≅ B) : IsIso e.hom.hom :=
  ⟨e.inv.hom, congrArg Mon.Hom.hom e.hom_inv_id, congrArg Mon.Hom.hom e.inv_hom_id⟩

/-- Two isomorphisms `a b : A ≅ internalEnd X` of monoid objects read an endomorphism `f` of `X`
as the same point of `A` exactly when the automorphism `a⁻¹ ≫ b` of `internalEnd X` fixes `f`. -/
theorem curry'_comp_inv_hom_eq_iff {A : Mon C} {X : C} (a b : A ≅ internalEnd X) (f : X ⟶ X) :
    curry' f ≫ a.inv.hom = curry' f ≫ b.inv.hom ↔ pointMap (a.inv ≫ b.hom) f = f := by
  have hbi : b.inv.hom ≫ b.hom.hom = 𝟙 (internalEnd X).X := congrArg Mon.Hom.hom b.inv_hom_id
  have hbh : b.hom.hom ≫ b.inv.hom = 𝟙 A.X := congrArg Mon.Hom.hom b.hom_inv_id
  have key : curry' (pointMap (a.inv ≫ b.hom) f) = curry' f ≫ a.inv.hom ≫ b.hom.hom := by
    rw [curry'_pointMap]
    rfl
  refine ⟨fun h => curry'_injective ?_, fun h => ?_⟩
  · rw [key, ← Category.assoc, h, Category.assoc, hbi, Category.comp_id]
  · calc curry' f ≫ a.inv.hom = (curry' f ≫ a.inv.hom ≫ b.hom.hom) ≫ b.inv.hom := by
          simp only [Category.assoc, hbh, Category.comp_id]
      _ = curry' f ≫ b.inv.hom := by rw [← key, h]

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- The identification of `X ⟶ Y` with the points of the internal hom is additive. -/
theorem curry'_add {X Y : C} (f g : X ⟶ Y) : curry' (f + g) = curry' f + curry' g := by
  rw [curry', curry', curry', Preadditive.comp_add]
  exact (ihom.adjunction X).homAddEquiv_add _ _ _ _

/-- The identification of the points of the internal hom with `X ⟶ Y` is additive. -/
theorem uncurry'_add {X Y : C} (f g : 𝟙_ C ⟶ (ihom X).obj Y) :
    uncurry' (f + g) = uncurry' f + uncurry' g := by
  rw [uncurry', uncurry', uncurry', uncurry_eq, uncurry_eq, uncurry_eq,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

/-- **The map induced on endomorphisms by a morphism of internal endomorphism monoids is
additive**, so together with `pointMap_id` and `pointMap_comp` it is a morphism of rings. -/
theorem pointMap_add {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) (f g : X ⟶ X) :
    pointMap θ (f + g) = pointMap θ f + pointMap θ g := by
  rw [pointMap, curry'_add, Preadditive.add_comp, uncurry'_add]
  rfl

end Preadditive

end CategoryTheory.MonoidalClosed

end
