module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# The self fibre product of a base change

Let `f : X ⟶ Y` and `g : V ⟶ Y` be morphisms, let `P` be a chosen fibre product of `f` and `g`
and let `XX` be a chosen fibre product of `f` with itself. The projection `P.p₂ : P ⟶ V` is the
base change of `f` along `g`, and its self fibre product over `V` is the base change of `XX`
along `g`: a chosen fibre product of `XX.p : XX ⟶ Y` and `g` serves as a chosen fibre product
of `P.p₂` with itself.

## Main definitions

* `CategoryTheory.Limits.ChosenPullback.baseChangedSelf`: the chosen fibre product of `P.p₂`
  with itself obtained in this way.

## Main results

* `CategoryTheory.Limits.ChosenPullback.baseChangedSelf_p`,
  `CategoryTheory.Limits.ChosenPullback.baseChangedSelf_p₁_fst` and
  `CategoryTheory.Limits.ChosenPullback.baseChangedSelf_p₂_fst`: its structure morphism and the
  two projections, read through the projection `P.p₁`.

## Implementation notes

The two projections are the two liftings of the pair consisting of a projection of `XX`
followed by `XX.p₁` or `XX.p₂`, and the projection to `V`; the universal property is checked
directly on a cone, by lifting first into `XX` and then into the chosen fibre product of `XX.p`
and `g`.

Nothing here carries a Stacks attribute: this is a general fact about fibre products, and the
source states none of it.
-/

@[expose] public section

namespace CategoryTheory.Limits.ChosenPullback

universe v u

variable {C : Type u} [Category.{v} C] {X Y V : C} (f : X ⟶ Y) (g : V ⟶ Y)
  (P : ChosenPullback f g) (XX : ChosenPullback f f) (Z : ChosenPullback XX.p g)

/-- **The self fibre product of a base change is the base change of the self fibre product.**
A chosen fibre product of `XX.p : X ×_Y X ⟶ Y` with `g : V ⟶ Y` is a chosen fibre product of
the base change `P.p₂ : X ×_Y V ⟶ V` of `f` along `g` with itself. -/
noncomputable def baseChangedSelf : ChosenPullback P.p₂ P.p₂ := by
  let a : Z.pullback ⟶ P.pullback := P.isPullback.lift
    (Z.p₁ ≫ XX.p₁) Z.p₂ (by rw [Category.assoc, XX.hp₁, Z.condition])
  let b : Z.pullback ⟶ P.pullback := P.isPullback.lift
    (Z.p₁ ≫ XX.p₂) Z.p₂ (by rw [Category.assoc, XX.hp₂, Z.condition])
  have hab : a ≫ P.p₂ = b ≫ P.p₂ :=
    (P.isPullback.lift_snd _ _ _).trans (P.isPullback.lift_snd _ _ _).symm
  refine { pullback := Z.pullback, p₁ := a, p₂ := b, condition := hab, isLimit := ?_ }
  refine PullbackCone.IsLimit.mk hab ?_ ?_ ?_ ?_
  · intro s
    let c : s.pt ⟶ XX.pullback := XX.isPullback.lift
      (s.fst ≫ P.p₁) (s.snd ≫ P.p₁) (by
        simp only [Category.assoc, P.condition]
        simpa only [Category.assoc] using s.condition =≫ g)
    exact Z.isPullback.lift c (s.fst ≫ P.p₂) (by
      calc
        c ≫ XX.p = (c ≫ XX.p₁) ≫ f := by rw [← XX.hp₁, Category.assoc]
        _ = (s.fst ≫ P.p₁) ≫ f := by rw [XX.isPullback.lift_fst]
        _ = (s.fst ≫ P.p₂) ≫ g := by rw [Category.assoc, P.condition, Category.assoc])
  · intro s
    apply P.hom_ext <;> simp [a]
  · intro s
    apply P.hom_ext
    · simp [b]
    · simpa [b] using s.condition
  · intro s m hm₁ hm₂
    apply Z.hom_ext
    · apply XX.hom_ext
      · simpa [a] using hm₁ =≫ P.p₁
      · simpa [b] using hm₂ =≫ P.p₁
    · simpa [a] using hm₁ =≫ P.p₂

/-- The structure morphism of `CategoryTheory.Limits.ChosenPullback.baseChangedSelf` is the
second projection of the chosen fibre product it is built from. -/
theorem baseChangedSelf_p : (baseChangedSelf f g P XX Z).p = Z.p₂ := by
  simp [baseChangedSelf]

/-- The first projection of `CategoryTheory.Limits.ChosenPullback.baseChangedSelf`, read
through the first projection of `P`. -/
theorem baseChangedSelf_p₁_fst :
    (baseChangedSelf f g P XX Z).p₁ ≫ P.p₁ = Z.p₁ ≫ XX.p₁ := by
  simp [baseChangedSelf]

/-- The second projection of `CategoryTheory.Limits.ChosenPullback.baseChangedSelf`, read
through the first projection of `P`. -/
theorem baseChangedSelf_p₂_fst :
    (baseChangedSelf f g P XX Z).p₂ ≫ P.p₁ = Z.p₁ ≫ XX.p₂ := by
  simp [baseChangedSelf]

end CategoryTheory.Limits.ChosenPullback

end
