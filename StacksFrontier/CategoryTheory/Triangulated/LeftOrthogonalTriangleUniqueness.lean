module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Uniqueness of the triangle splitting off a subcategory

Let `𝒫` be a full subcategory of a pretriangulated category `𝒞`, stable under all shifts, and let
`X` be an object of `𝒞`. A distinguished triangle

`A ⟶ X ⟶ B ⟶ A⟦1⟧`

with `A` left orthogonal to `𝒫` and `B` in `𝒫` is unique up to an isomorphism of triangles which
is the identity on `X`. This is the sense in which such a triangle is *canonical* in
[Stacks, Tag 0CQP]: if `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` is another one, the morphisms `A ⟶ X` and
`A' ⟶ X` factor through each other because `Hom(A, B') = Hom(A', B) = 0`, the factorizations are
mutually inverse because `Hom(A, B⟦-1⟧) = Hom(A', B'⟦-1⟧) = 0`, and an isomorphism of the first
morphisms of two distinguished triangles extends to an isomorphism of triangles.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_of_leftOrthogonal`: the uniqueness statement.

## References

* [Stacks Project, Tag 0CQP](https://stacks.math.columbia.edu/tag/0CQP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]

/-- A morphism `u : A ⟶ A` out of an object left orthogonal to `𝒫` which is killed by the first
morphism `A ⟶ X` of a distinguished triangle `A ⟶ X ⟶ B ⟶ A⟦1⟧` with `B` in `𝒫` is zero: it
factors through `B⟦-1⟧`, which lies in `𝒫`. -/
lemma eq_zero_of_comp_mor₁_eq_zero_of_leftOrthogonal (T : Triangle C) (hT : T ∈ distTriang C)
    (hA : P.leftOrthogonal T.obj₁) (hB : P T.obj₃) {u : T.obj₁ ⟶ T.obj₁}
    (hu : u ≫ T.mor₁ = 0) : u = 0 := by
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) u hu
  rw [hg, hA g (P.le_shift (-1 : ℤ) _ hB), Limits.zero_comp]
  rfl

/-- If `f' = φ ≫ f` and `f = ψ ≫ f'` for the first morphisms of two distinguished triangles, the
first with `A` left orthogonal to `𝒫` and the third object in `𝒫`, then `ψ ≫ φ = 𝟙 A`. -/
private lemma comp_eq_id_of_leftOrthogonal {X A A' B : C} {f : A ⟶ X} {g : X ⟶ B}
    {h : B ⟶ A⟦(1 : ℤ)⟧} {f' : A' ⟶ X} (hT : Triangle.mk f g h ∈ distTriang C)
    (hA : P.leftOrthogonal A) (hB : P B) {φ : A' ⟶ A} {ψ : A ⟶ A'} (hφ : f' = φ ≫ f)
    (hψ : f = ψ ≫ f') : ψ ≫ φ = 𝟙 A := by
  refine sub_eq_zero.1 (eq_zero_of_comp_mor₁_eq_zero_of_leftOrthogonal P _ hT hA hB ?_)
  dsimp
  rw [Preadditive.sub_comp, Category.assoc, ← hφ, ← hψ, Category.id_comp, sub_self]

/-- **The triangle splitting off `𝒫` is unique** ([Stacks, Tag 0CQP]): two distinguished
triangles `A ⟶ X ⟶ B ⟶ A⟦1⟧` and `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` with `A`, `A'` left orthogonal to `𝒫`
and `B`, `B'` in `𝒫` are isomorphic by an isomorphism of triangles which is the identity on
`X`. -/
theorem exists_iso_of_leftOrthogonal {X A₁ A₂ B₁ B₂ : C} (f₁ : A₁ ⟶ X) (g₁ : X ⟶ B₁)
    (h₁ : B₁ ⟶ A₁⟦(1 : ℤ)⟧) (f₂ : A₂ ⟶ X) (g₂ : X ⟶ B₂) (h₂ : B₂ ⟶ A₂⟦(1 : ℤ)⟧)
    (hT₁ : Triangle.mk f₁ g₁ h₁ ∈ distTriang C) (hT₂ : Triangle.mk f₂ g₂ h₂ ∈ distTriang C)
    (hA₁ : P.leftOrthogonal A₁) (hA₂ : P.leftOrthogonal A₂) (hB₁ : P B₁) (hB₂ : P B₂) :
    ∃ e : Triangle.mk f₁ g₁ h₁ ≅ Triangle.mk f₂ g₂ h₂, e.hom.hom₂ = 𝟙 X := by
  obtain ⟨φ, hφ⟩ := Triangle.coyoneda_exact₂ _ hT₁ f₂ (hA₂ (f₂ ≫ g₁) hB₁)
  obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₂ _ hT₂ f₁ (hA₁ (f₁ ≫ g₂) hB₂)
  dsimp at hφ hψ
  change A₂ ⟶ A₁ at φ
  change A₁ ⟶ A₂ at ψ
  have h₁₁ := comp_eq_id_of_leftOrthogonal P hT₁ hA₁ hB₁ hφ hψ
  have h₂₂ := comp_eq_id_of_leftOrthogonal P hT₂ hA₂ hB₂ hψ hφ
  obtain ⟨e, -, he₂⟩ := exists_iso_of_arrow_iso _ _ hT₁ hT₂
    (Arrow.isoMk ⟨ψ, φ, h₁₁, h₂₂⟩ (Iso.refl X) (by simp [hψ]))
  exact ⟨e, he₂⟩

end CategoryTheory.Pretriangulated
