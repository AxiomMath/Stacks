module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Scalars acting through the monoidal unit

Let `𝒞` be a monoidal category which is `R`-linear for a commutative ring `R`. Multiplication by
`a ∈ R` on the unit object, whiskered on the right with an object `X` and conjugated by the left
unitor, is an endomorphism of `X`; when it is multiplication by `a` for every `X`, the scalars
act on the tensor product through either factor:

`(a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y)` and, if `𝒞` is braided, `X ◁ (a • 𝟙 Y) = a • 𝟙 (X ⊗ Y)`.

The condition is stable under isomorphism of objects and is carried along any monoidal
`R`-linear functor, so it passes from a monoidal category to its monoidal localizations, which is
how the monoidal categories built by localization (sheaves, homotopy and derived categories)
acquire it.

## Main results

* `CategoryTheory.MonoidalCategory.smul_id_eq_leftUnitor_of_iso`: invariance under isomorphism.
* `CategoryTheory.MonoidalCategory.smul_id_eq_leftUnitor_map`: transport along a monoidal linear
  functor.
* `CategoryTheory.MonoidalCategory.smul_id_whiskerRight_of_forall` and
  `CategoryTheory.MonoidalCategory.whiskerLeft_smul_id_of_forall`: linearity of whiskering.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable {R : Type*} [CommRing R] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear R 𝒞]
  [MonoidalCategory 𝒞]

/-- The action of a scalar through the unit object is compatible with isomorphisms: if
multiplication by `a` on `X` is the action through the unit, so is multiplication by `a` on any
object isomorphic to `X`. -/
theorem smul_id_eq_leftUnitor_of_iso {X Y : 𝒞} (e : X ≅ Y) (a : R)
    (h : a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ 𝒞)) ▷ X) ≫ (λ_ X).hom) :
    a • 𝟙 Y = (λ_ Y).inv ≫ ((a • 𝟙 (𝟙_ 𝒞)) ▷ Y) ≫ (λ_ Y).hom := by
  have h' : a • 𝟙 Y = e.inv ≫ (a • 𝟙 X) ≫ e.hom := by simp
  rw [h', h]
  simp only [Category.assoc]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]
  simp

variable (R) in
/-- **Scalars act on a tensor product through the left factor**, as soon as every scalar acts on
every object through the unit object. -/
theorem smul_id_whiskerRight_of_forall
    (h : ∀ (a : R) (X : 𝒞), a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ 𝒞)) ▷ X) ≫ (λ_ X).hom)
    (a : R) (X Y : 𝒞) : (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y) := by
  rw [h a X, h a (X ⊗ Y), whiskerRight_tensor]
  simp only [comp_whiskerRight, leftUnitor_inv_whiskerRight, leftUnitor_whiskerRight,
    Category.assoc]

/-- **Scalars act on a tensor product through the right factor**, in a braided category in
which every scalar acts on every object through the unit object. -/
theorem whiskerLeft_smul_id_of_forall [BraidedCategory 𝒞]
    (h : ∀ (a : R) (X : 𝒞), a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ 𝒞)) ▷ X) ≫ (λ_ X).hom)
    (a : R) (X Y : 𝒞) : X ◁ (a • 𝟙 Y) = a • 𝟙 (X ⊗ Y) := by
  rw [← cancel_mono (β_ X Y).hom, BraidedCategory.braiding_naturality_right,
    smul_id_whiskerRight_of_forall R h]
  simp

variable {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [Linear R 𝒟] [MonoidalCategory 𝒟]

/-- A monoidal `R`-linear functor carries the action of a scalar through the unit object to the
action through the unit object. -/
theorem smul_id_eq_leftUnitor_map (L : 𝒞 ⥤ 𝒟) [L.Monoidal] [L.Linear R] (a : R) (X : 𝒞)
    (h : a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ 𝒞)) ▷ X) ≫ (λ_ X).hom) :
    a • 𝟙 (L.obj X) = (λ_ (L.obj X)).inv ≫ ((a • 𝟙 (𝟙_ 𝒟)) ▷ L.obj X) ≫ (λ_ (L.obj X)).hom := by
  have hL : a • 𝟙 (L.obj X) = L.map (a • 𝟙 X) := by simp
  rw [hL, h, L.map_comp, L.map_comp, Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc, L.map_smul, L.map_id]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simp [Functor.Monoidal.ε_η]

end CategoryTheory.MonoidalCategory
