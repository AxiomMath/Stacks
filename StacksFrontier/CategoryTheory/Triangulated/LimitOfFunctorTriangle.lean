module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Products and triangles of functors

Let `F, G : 𝒦 ⥤ D` be functors into a pre-triangulated category with countable products, and
suppose that `G` is a cone of an endomorphism of `F`: there are natural transformations
`τ : F ⟶ F`, `u : F ⟶ G` and `δ : G ⟶ F ⋙ [1]` making
`F X ⟶ F X ⟶ G X ⟶ (F X)⟦1⟧` distinguished for every `X`. If `F` carries a family of maps
`P ⟶ xⱼ` of `𝒦` to a product diagram of `D`, then so does `G`.

## Main results

* `CategoryTheory.Pretriangulated.isIso_lift_map_of_distTriang`: a cone of an endomorphism of a
  functor preserves a product which the functor itself preserves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

variable {𝒦 : Type*} [Category 𝒦] {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A cone of an endomorphism of a functor preserves a product** which the functor itself
preserves: if `F` carries the maps `π j : P ⟶ x j` to a product diagram, so does `G`. -/
theorem isIso_lift_map_of_distTriang {J : Type*} [HasProductsOfShape J D]
    {x : J → 𝒦} {P : 𝒦} (π : ∀ j, P ⟶ x j) {F G : 𝒦 ⥤ D} (τ : F ⟶ F) (u : F ⟶ G)
    (δ : G ⟶ F ⋙ shiftFunctor D (1 : ℤ))
    (hT : ∀ X, Triangle.mk (τ.app X) (u.app X) (δ.app X) ∈ distTriang D)
    (hF : IsIso (Pi.lift fun j ↦ F.map (π j))) : IsIso (Pi.lift fun j ↦ G.map (π j)) := by
  let T : J → Triangle D := fun j ↦ Triangle.mk (τ.app (x j)) (u.app (x j)) (δ.app (x j))
  let φ : ∀ j, Triangle.mk (τ.app P) (u.app P) (δ.app P) ⟶ T j := fun j ↦
    { hom₁ := F.map (π j)
      hom₂ := F.map (π j)
      hom₃ := G.map (π j)
      comm₁ := (τ.naturality _).symm
      comm₂ := (u.naturality _).symm
      comm₃ := (δ.naturality _).symm }
  exact isIso₃_of_isIso₁₂ (productTriangle.lift T φ) (hT P)
    (productTriangle_distinguished T fun j ↦ hT (x j)) hF hF

end CategoryTheory.Pretriangulated
