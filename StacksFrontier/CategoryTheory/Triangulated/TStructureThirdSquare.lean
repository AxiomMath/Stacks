module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# The third square of a morphism of triangles, from a t-structure

Let `T` and `T'` be distinguished triangles of a pretriangulated category with a t-structure
`t`, and let `φ₁ : T.obj₁ ⟶ T'.obj₁`, `φ₂ : T.obj₂ ⟶ T'.obj₂`, `φ₃ : T.obj₃ ⟶ T'.obj₃` be
morphisms making the first two squares commute. In general the third square
`T.mor₃ ≫ φ₁⟦1⟧' = φ₃ ≫ T'.mor₃` need not commute. It does as soon as `T.obj₁` is `t`-bounded
above by `0` and `T'.obj₃` is `t`-bounded below by `0`: completing `(φ₁, φ₂)` to a morphism of
triangles gives some `c` making all three squares commute, the difference `φ₃ - c` is killed by
`T.mor₂` and hence factors through `T.mor₃`, and the factor is a morphism from an object
bounded above by `-1` to one bounded below by `0`, which is zero.

This is the case of the triangles `A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0]⟦1⟧` of short exact sequences in a
derived category and their images under exact functors: a morphism between two of them is
determined by its components, and any family of components compatible with the first two
morphisms is one.

## Main results

* `CategoryTheory.Pretriangulated.comm₃_of_isLE_of_isGE` — the third square commutes.
* `CategoryTheory.Pretriangulated.triangleHomOfIsLEOfIsGE` — the resulting morphism of triangles.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)
  {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
  (φ₁ : T.obj₁ ⟶ T'.obj₁) (φ₂ : T.obj₂ ⟶ T'.obj₂) (φ₃ : T.obj₃ ⟶ T'.obj₃)
  (h₁ : T.mor₁ ≫ φ₂ = φ₁ ≫ T'.mor₁) (h₂ : T.mor₂ ≫ φ₃ = φ₂ ≫ T'.mor₂)

include hT hT' h₁ h₂ in
/-- **The third square of a morphism of triangles commutes when the first object of the source
is `t`-bounded above by `0` and the third object of the target is `t`-bounded below by `0`.**
The components are then determined by the first two squares. -/
theorem comm₃_of_isLE_of_isGE [t.IsLE T.obj₁ 0] [t.IsGE T'.obj₃ 0] :
    T.mor₃ ≫ φ₁⟦(1 : ℤ)⟧' = φ₃ ≫ T'.mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism T T' hT hT' φ₁ φ₂ h₁
  have hz : T.mor₂ ≫ (φ₃ - c) = 0 := by
    rw [Preadditive.comp_sub, h₂, hc₂, sub_self]
  obtain ⟨x, hx⟩ := Triangle.yoneda_exact₃ T hT (φ₃ - c) hz
  have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) := t.isLE_shift T.obj₁ 0 1 (-1)
  have hx0 : x = 0 := t.zero x (-1) 0
  have hc : φ₃ = c := by
    rw [hx0, comp_zero] at hx
    exact sub_eq_zero.mp hx
  rw [hc, hc₃]

/-- **The morphism of triangles with prescribed components**, when the first object of the
source is `t`-bounded above by `0` and the third object of the target is `t`-bounded below by
`0`: compatibility with the first two morphisms is enough. -/
@[simps]
def triangleHomOfIsLEOfIsGE [t.IsLE T.obj₁ 0] [t.IsGE T'.obj₃ 0] : T ⟶ T' where
  hom₁ := φ₁
  hom₂ := φ₂
  hom₃ := φ₃
  comm₁ := h₁
  comm₂ := h₂
  comm₃ := comm₃_of_isLE_of_isGE t hT hT' φ₁ φ₂ φ₃ h₁ h₂

end CategoryTheory.Pretriangulated
