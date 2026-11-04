module

public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# A scalar killing the two ends of a distinguished triangle squares to zero on the third

Let `C` be a pre-triangulated category, linear over a commutative ring `A` with `A`-linear shift
functors, and let `(X, Y, Z, f, g, h)` be a distinguished triangle.

* If `a : A` kills the identity of `X` and the identity of `Y`, then `a ^ 2` kills the identity
  of `Z`.
* If the first morphism of the triangle *is* `a • 𝟙 X`, so that `Z` is the cone of
  multiplication by `a`, then `a ^ 2` kills the identity of `Z` as well -- even though `a` need
  not kill the identity of `X`.

Both are [Stacks, Tag 05QP] -- an endomorphism of a distinguished triangle whose outer
components vanish has middle component squaring to zero -- applied to the rotation of the
triangle, whose middle object is `Z`. They are the step by which [Stacks, Tag 08EK] makes an
iterated cone construction land in the objects supported on `V(g_1, …, g_s)`: starting from a
perfect object and coning off multiplication by each `g_j` in turn, each `g_j` ends up killing
the identity of the result to some power.

## Main results

* `Stacks.Triangulated.comp_self_eq_zero_of_comp_mor₂_eq_zero`: [Stacks, Tag 05QP] read on the
  rotation -- an endomorphism of the third object killed by the second morphism on the left and
  killing the third morphism on the right squares to zero.
* `Stacks.Triangulated.smul_id_obj₃_sq_eq_zero`: the first statement above.
* `Stacks.Triangulated.smul_id_obj₃_sq_eq_zero_of_mor₁_eq_smul_id`: the second.

## Implementation notes

The common core is stated for an arbitrary endomorphism `b` of the third object rather than for
a scalar multiple of the identity, because the two scalar cases verify the two commutativity
conditions of the endomorphism of the rotated triangle in different ways: the first from the
hypotheses on the two ends, the second from `g ∘ f = 0` and `f[1] ∘ h = 0` for the triangle
itself. Isolating it also keeps the construction of the
`CategoryTheory.Pretriangulated.TriangleMorphism` out of both corollaries.

The `A`-linearity of the shift functors is what turns `(a • 𝟙 X)⟦1⟧` into `a • 𝟙 (X⟦1⟧)`; it is
an instance for the derived category of an `A`-linear abelian category, and without it the
second commutativity condition cannot be checked.

## References

* [Stacks Project, Lemma 13.4.5 (Tag 05QP)](https://stacks.math.columbia.edu/tag/05QP)
* [Stacks Project, Lemma 36.13.10 (Tag 08EK)](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Triangulated

universe v u

variable {A : Type*} [Semiring A] {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  [Linear A C]

/-- **[Stacks, Tag 05QP] read on the rotation of a distinguished triangle.** Let
`T = (X, Y, Z, f, g, h)` be distinguished and let `b : Z ⟶ Z` satisfy `g ≫ b = 0` and
`b ≫ h = 0`. Then `b ≫ b = 0`.

The triple `(0, b, 0)` is an endomorphism of the rotated triangle `(Y, Z, X⟦1⟧, g, h, -f⟦1⟧)`,
whose two commutativity conditions are exactly the two hypotheses, and
`CategoryTheory.Pretriangulated.comp_middle_zero_of_endomorphisms` applies to it twice. -/
theorem comp_self_eq_zero_of_comp_mor₂_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (b : T.obj₃ ⟶ T.obj₃) (h1 : T.mor₂ ≫ b = 0) (h2 : b ≫ T.mor₃ = 0) : b ≫ b = 0 := by
  let φ : TriangleMorphism T.rotate T.rotate :=
    { hom₁ := 0
      hom₂ := b
      hom₃ := 0
      comm₁ := by rw [Limits.zero_comp]; exact h1
      comm₂ := by rw [Limits.comp_zero]; exact h2.symm
      comm₃ := by
        rw [CategoryTheory.Functor.map_zero, Limits.comp_zero, Limits.zero_comp] }
  exact comp_middle_zero_of_endomorphisms T.rotate (rot_of_distTriang T hT) φ φ rfl rfl

/-- If `a` kills the second and third morphisms of a distinguished triangle, then `a * a` kills
the identity of its third object. -/
private theorem smul_id_obj₃_sq_eq_zero_of_smul_mor_eq_zero (T : Triangle C)
    (hT : T ∈ distTriang C) (a : A) (h1 : a • T.mor₂ = 0) (h2 : a • T.mor₃ = 0) :
    (a * a) • 𝟙 T.obj₃ = 0 := by
  have key : (a • 𝟙 T.obj₃) ≫ (a • 𝟙 T.obj₃) = 0 := by
    refine comp_self_eq_zero_of_comp_mor₂_eq_zero T hT _ ?_ ?_
    · rwa [Linear.comp_smul, Category.comp_id]
    · rwa [Linear.smul_comp, Category.id_comp]
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at key
  exact key

variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Linear A]

omit [HasZeroObject C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Shifting a scalar multiple of an identity is the scalar multiple of the identity. -/
theorem shift_smul_id (a : A) (X : C) :
    (CategoryTheory.shiftFunctor C (1 : ℤ)).map (a • 𝟙 X) = a • 𝟙 (X⟦(1 : ℤ)⟧) := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- **A scalar killing the identities of the two ends of a distinguished triangle squares to
zero on the third.** -/
theorem smul_id_obj₃_sq_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) (a : A)
    (h1 : a • 𝟙 T.obj₁ = 0) (h2 : a • 𝟙 T.obj₂ = 0) : (a * a) • 𝟙 T.obj₃ = 0 := by
  refine smul_id_obj₃_sq_eq_zero_of_smul_mor_eq_zero T hT a ?_ ?_
  · rw [← Category.id_comp T.mor₂, ← Linear.smul_comp, h2, Limits.zero_comp]
  · rw [← Category.comp_id T.mor₃, ← Linear.comp_smul, ← shift_smul_id a T.obj₁, h1,
      CategoryTheory.Functor.map_zero, Limits.comp_zero]

/-- **The cone of multiplication by `a` is killed by `a ^ 2`.** If the first morphism of a
distinguished triangle is `a • 𝟙 X`, then `a * a` kills the identity of its third object -- `a`
itself need not kill the identity of `X`.

The two hypotheses of `Stacks.Triangulated.comp_self_eq_zero_of_comp_mor₂_eq_zero` are here the
vanishing of the two composites of consecutive morphisms of the triangle,
`CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂` and
`CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₃₁`. -/
theorem smul_id_obj₃_sq_eq_zero_of_mor₁_eq_smul_id {X Z : C} (a : A) (v : X ⟶ Z)
    (w : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk (a • 𝟙 X) v w ∈ distTriang C) :
    (a * a) • 𝟙 Z = 0 := by
  refine smul_id_obj₃_sq_eq_zero_of_smul_mor_eq_zero (Triangle.mk (a • 𝟙 X) v w) hT a ?_ ?_
  · change a • v = 0
    rw [← Category.id_comp v, ← Linear.smul_comp]
    exact comp_distTriang_mor_zero₁₂ _ hT
  · change a • w = 0
    rw [← Category.comp_id w, ← Linear.comp_smul, ← shift_smul_id a X]
    exact comp_distTriang_mor_zero₃₁ _ hT

end Stacks.Triangulated

end
