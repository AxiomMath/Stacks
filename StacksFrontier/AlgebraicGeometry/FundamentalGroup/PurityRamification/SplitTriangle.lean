module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# A distinguished triangle whose first morphism is a split monomorphism up to an isomorphism

Let `X ⟶ K ⟶ Y ⟶ X⟦1⟧` be a distinguished triangle in a pretriangulated category, and suppose
some morphism `φ : K ⟶ N` makes the composite `X ⟶ K ⟶ N` an isomorphism. Then the third
morphism `Y ⟶ X⟦1⟧` vanishes, so every morphism into `Y` lifts to `K`; in particular an object
`Z` with no nonzero morphism to `K` has no nonzero morphism to `Y` either.

This is the formal core of the proof of [Stacks, Tag 0EA2]. There the triangle is the truncation
triangle `A ⟶ Rf_*𝒪_X ⟶ R¹f_*𝒪_X[-1] ⟶ A[1]` in `D(A)`, the morphism `φ` is the trace
`Rf_*𝒪_X ⟶ ω_A` composed with the section `𝒪_X ⟶ 𝒪_X(E) = ω_X`, whose composite with
`A ⟶ Rf_*𝒪_X` the source shows to be an isomorphism, and `Z = κ[-1]`, which has no nonzero
morphism to `Rf_*𝒪_X` by [Stacks, Tag 0AXC]. The conclusion is that `R¹f_*𝒪_X` has no nonzero
map from `κ`.

## Main results

* `Stacks.PurityRamification.mor₃_eq_zero_of_isIso_mor₁_comp`: the third morphism vanishes.
* `Stacks.PurityRamification.eq_zero_of_isIso_mor₁_comp_of_forall_eq_zero`: the lifting
  consequence.

## References

* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace Stacks.PurityRamification

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If the first morphism of a distinguished triangle becomes an isomorphism after composing with
some morphism out of the second object, the third morphism of the triangle is zero: it is killed
by the shift of the first morphism, hence by the shift of that isomorphism. -/
theorem mor₃_eq_zero_of_isIso_mor₁_comp (T : Triangle C) (hT : T ∈ distTriang C) {N : C}
    (φ : T.obj₂ ⟶ N) [IsIso (T.mor₁ ≫ φ)] : T.mor₃ = 0 := by
  have h : T.mor₃ ≫ (T.mor₁ ≫ φ)⟦(1 : ℤ)⟧' = 0 := by
    rw [Functor.map_comp, comp_distTriang_mor_zero₃₁_assoc T hT, zero_comp]
  simpa using h =≫ inv ((T.mor₁ ≫ φ)⟦(1 : ℤ)⟧')

/-- In a distinguished triangle `X ⟶ K ⟶ Y ⟶ X⟦1⟧` whose first morphism becomes an isomorphism
after composing with some `φ : K ⟶ N`, an object with no nonzero morphism to `K` has no nonzero
morphism to `Y`: by `mor₃_eq_zero_of_isIso_mor₁_comp` every morphism into `Y` lifts along
`K ⟶ Y`. -/
theorem eq_zero_of_isIso_mor₁_comp_of_forall_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    {N : C} (φ : T.obj₂ ⟶ N) [IsIso (T.mor₁ ≫ φ)] {Z : C} (hZ : ∀ l : Z ⟶ T.obj₂, l = 0)
    (g : Z ⟶ T.obj₃) : g = 0 := by
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₃ T hT g
    (by rw [mor₃_eq_zero_of_isIso_mor₁_comp T hT φ, comp_zero])
  rw [hl, hZ l, zero_comp]

end Stacks.PurityRamification

end
