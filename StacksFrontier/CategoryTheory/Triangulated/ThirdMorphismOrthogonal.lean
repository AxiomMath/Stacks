module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# The third morphism of a morphism of triangles, when it is forced

Let `T`, `T'` be distinguished triangles in a pretriangulated category and `a`, `b`, `c` maps
between their three objects which commute with the first two morphisms. In general `c` need not
commute with the third morphisms: a completion `c'` of `(a, b)` exists (axiom TR3), and
`c - c'` vanishes on `T.obj₂`, so it factors as `T.mor₃ ≫ g` for some `g : T.obj₁⟦1⟧ ⟶ T'.obj₃`.
If every such `g` is zero, then `c = c'` and `(a, b, c)` is a morphism of triangles
(`Stacks.Triangulated.mor₃_comp_shift_map_eq_of_forall_eq_zero`). For a t-structure this holds
when `T.obj₁` is `≤ n` and `T'.obj₃` is `≥ n`
(`Stacks.Triangulated.mor₃_comp_shift_map_eq_of_isLE`).

This is how the truncation `K ⟶ τ^{≥ n} K` is seen to commute with the connecting morphisms of a
triangle all of whose objects are `≤ n`: the truncated triangle is the triangle of a short exact
sequence in the heart, and the comparison is forced. It is the step of degree one in the
compatibility of the top-degree trace `Rf_! f⁻¹ ⟶ (-)[-2]` of a relative curve with classes in
`Ext` (proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.Triangulated.mor₃_comp_shift_map_eq_of_forall_eq_zero`.
* `Stacks.Triangulated.mor₃_comp_shift_map_eq_of_isLE`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated

namespace Stacks.Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A morphism of the first two terms of distinguished triangles is one of triangles** as
soon as every morphism `T.obj₁⟦1⟧ ⟶ T'.obj₃` is zero: the completion given by TR3 differs from
`c` by a morphism factoring through `T.mor₃`. -/
theorem mor₃_comp_shift_map_eq_of_forall_eq_zero {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (a : T.obj₁ ⟶ T'.obj₁) (b : T.obj₂ ⟶ T'.obj₂)
    (c : T.obj₃ ⟶ T'.obj₃) (hab : T.mor₁ ≫ b = a ≫ T'.mor₁) (hbc : T.mor₂ ≫ c = b ≫ T'.mor₂)
    (hzero : ∀ g : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃, g = 0) :
    T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T'.mor₃ := by
  obtain ⟨c', hc'₂, hc'₃⟩ := complete_distinguished_triangle_morphism T T' hT hT' a b hab
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T hT (c - c')
    (by rw [Preadditive.comp_sub, hbc, hc'₂, sub_self])
  have hcc' : c = c' := by
    rw [← sub_eq_zero, hg, hzero g, Limits.comp_zero]
  rw [hcc', hc'₃]

/-- **The third morphism is forced by a t-structure**: if `T.obj₁` is `≤ n` and `T'.obj₃` is
`≥ n` for a t-structure `t`, a morphism of the first two terms of distinguished triangles `T`,
`T'` commuting with them is one of triangles, since `T.obj₁⟦1⟧` is `≤ n - 1`. -/
theorem mor₃_comp_shift_map_eq_of_isLE (t : TStructure C) (n : ℤ) {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) [t.IsLE T.obj₁ n] [t.IsGE T'.obj₃ n]
    (a : T.obj₁ ⟶ T'.obj₁) (b : T.obj₂ ⟶ T'.obj₂) (c : T.obj₃ ⟶ T'.obj₃)
    (hab : T.mor₁ ≫ b = a ≫ T'.mor₁) (hbc : T.mor₂ ≫ c = b ≫ T'.mor₂) :
    T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T'.mor₃ := by
  have := t.isLE_shift T.obj₁ n 1 (n - 1) (by omega)
  exact mor₃_comp_shift_map_eq_of_forall_eq_zero hT hT' a b c hab hbc
    fun g => t.zero g (n - 1) n (by omega)

end Stacks.Triangulated
