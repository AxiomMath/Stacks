module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.GuitartExact.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Cofinality for the slice functors of a cartesian square

Let
```
  U' --a--> U
  |b        |c
  V' --d--> V
```
be a commutative square in a category `C`. Applying `CategoryTheory.Over.map` to its four
morphisms gives a commutative square of slice categories, and this file records three facts
about it:

* the square of slice functors commutes *on the nose*, as an equality of functors
  `Over.map b ⋙ Over.map d = Over.map a ⋙ Over.map c` (`overMapSquareEq`);
* the associated `CategoryTheory.TwoSquare` is Guitart exact as soon as the original square is
  cartesian (`guitartExact_overMapSquare`);
* equivalently, each comparison functor
  `CostructuredArrow (Over.map b) W ⥤ CostructuredArrow (Over.map c) ((Over.map d).obj W)`
  is final (`final_costructuredArrow_map₂_overMap`).

The third statement is hypothesis (4) of Stacks 0FN1 for the square of slice functors.

## Main definitions

* `Stacks.Sites.RelocalizationCofinality.overMapSquare`: the `2`-square
  `Over.map a ⋙ Over.map c ⟶ Over.map b ⋙ Over.map d` of the commutative square, namely the
  transport along `overMapSquareEq`.
* `Stacks.Sites.RelocalizationCofinality.costructuredArrowComparison`: the comparison functor
  `CostructuredArrow (Over.map b) W ⥤ CostructuredArrow (Over.map c) ((Over.map d).obj W)`,
  sending `ψ : (Over.map b)(W') ⟶ W` to `(Over.map d)(ψ)`.

## Main results

* `Stacks.Sites.RelocalizationCofinality.overMapSquareEq`: the square of slice functors commutes
  as an equality of functors.
* `Stacks.Sites.RelocalizationCofinality.guitartExact_overMapSquare`: for a cartesian square, the
  `2`-square of slice functors is Guitart exact.
* `Stacks.Sites.RelocalizationCofinality.final_costructuredArrow_map₂_overMap`: for a cartesian
  square, every comparison functor is final.

## References

* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
* [Stacks Project, Tag 0EYV](https://stacks.math.columbia.edu/tag/0EYV)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH), the relocalization
  morphisms attached to `Over.map`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v u

namespace Stacks.Sites.RelocalizationCofinality

variable {C : Type u} [Category.{v} C] {U' U V' V : C} {a : U' ⟶ U} {b : U' ⟶ V'} {c : U ⟶ V}
  {d : V' ⟶ V}

/-- **The square of slice functors of a commutative square commutes on the nose.** For a
commutative square `a ≫ c = b ≫ d` in `C`, the two composites of slice functors
`Over U' ⥤ Over V` are equal. -/
theorem overMapSquareEq (sq : CommSq a b c d) :
    Over.map b ⋙ Over.map d = Over.map a ⋙ Over.map c := by
  refine CategoryTheory.Functor.ext (fun W => ?_) (fun W₁ W₂ f => ?_)
  · exact congrArg Over.mk (by simp [sq.w])
  · exact Over.OverMorphism.ext (by simp)

/-- The `2`-square of slice functors attached to a commutative square of `C`: the transport
`Over.map a ⋙ Over.map c ⟶ Over.map b ⋙ Over.map d` along `overMapSquareEq`. -/
def overMapSquare (sq : CommSq a b c d) :
    TwoSquare (Over.map a) (Over.map b) (Over.map c) (Over.map d) :=
  TwoSquare.mk _ _ _ _ (eqToHom (overMapSquareEq sq).symm)

/-- The component of the `2`-square of slice functors is the identity on underlying objects of
`C`: the two composites differ only in how the structure morphism is written. -/
@[simp]
theorem overMapSquare_app_left (sq : CommSq a b c d) (W : Over U') :
    ((overMapSquare sq).app W).left = 𝟙 W.left := by
  rw [overMapSquare, TwoSquare.mk, eqToHom_app]
  simp

/-- **The `2`-square of slice functors of a cartesian square is Guitart exact.** -/
theorem guitartExact_overMapSquare (hsq : IsPullback a b c d) :
    (overMapSquare hsq.toCommSq).GuitartExact where
  isConnected_rightwards {X₂ X₃} g := by
    have hw : X₂.hom ≫ c = (g.left ≫ X₃.hom) ≫ d := by simpa using (Over.w g).symm
    let P : (overMapSquare hsq.toCommSq).StructuredArrowRightwards g :=
      TwoSquare.StructuredArrowRightwards.mk _ _
        (Over.mk (hsq.lift X₂.hom (g.left ≫ X₃.hom) hw))
        (Over.homMk (𝟙 X₂.left) (by simp)) (Over.homMk g.left (by simp))
        (by ext; simp)
    have := Nonempty.intro P
    have φ : ∀ Q : (overMapSquare hsq.toCommSq).StructuredArrowRightwards g,
        Nonempty (P ⟶ Q) := fun Q => by
      obtain ⟨X₁, a₀, b₀, comm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
      have hcomm : a₀.left ≫ b₀.left = g.left := by simpa using (Over.forget V).congr_map comm
      have hfst : a₀.left ≫ X₁.hom ≫ a = X₂.hom := by simpa using Over.w a₀
      have hsnd : b₀.left ≫ X₃.hom = X₁.hom ≫ b := Over.w b₀
      have hχ : a₀.left ≫ X₁.hom = hsq.lift X₂.hom (g.left ≫ X₃.hom) hw :=
        hsq.hom_ext (by simp [hfst]) (by simp [← hcomm, hsnd])
      refine ⟨StructuredArrow.homMk (CostructuredArrow.homMk (Over.homMk a₀.left hχ) ?_) ?_⟩
      · exact Over.OverMorphism.ext (by simpa [P] using hcomm)
      · exact CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (Category.id_comp _))
    refine zigzag_isConnected fun Q₁ Q₂ => ?_
    obtain ⟨f₁⟩ := φ Q₁
    obtain ⟨f₂⟩ := φ Q₂
    exact (Zigzag.of_inv f₁).trans (Zigzag.of_hom f₂)

/-- **The comparison functor of the square at an object `W` of `Over V'`**, sending an object
`ψ : (Over.map b)(W') ⟶ W` of `CostructuredArrow (Over.map b) W` to `(Over.map d)(ψ)`, read
through the transport of `overMapSquareEq`. -/
abbrev costructuredArrowComparison (sq : CommSq a b c d) (W : Over V') :
    CostructuredArrow (Over.map b) W ⥤
      CostructuredArrow (Over.map c) ((Over.map d).obj W) :=
  CostructuredArrow.map₂ (F := Over.map a) (G := Over.map d)
    (eqToHom (overMapSquareEq sq).symm) (𝟙 ((Over.map d).obj W))

/-- The comparison functor of the square is isomorphic to the functor
`(overMapSquare sq).costructuredArrowRightwards W` on which Guitart exactness is a condition. -/
def costructuredArrowComparisonIso (sq : CommSq a b c d) (W : Over V') :
    costructuredArrowComparison sq W ≅
      (overMapSquare sq).costructuredArrowRightwards W :=
  NatIso.ofComponents
    (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _)
      (by simp [overMapSquare, TwoSquare.costructuredArrowRightwards, Comma.mapLeft,
            CostructuredArrow.post, CostructuredArrow.pre]))
    (by intros
        apply CostructuredArrow.hom_ext
        simp [overMapSquare, TwoSquare.costructuredArrowRightwards, Comma.mapLeft,
          CostructuredArrow.post, CostructuredArrow.pre])

/-- **The cofinality condition for a cartesian square.** For a cartesian square of `C` and every
object `W` of `Over V'`, the comparison functor
`CostructuredArrow (Over.map b) W ⥤ CostructuredArrow (Over.map c) ((Over.map d).obj W)` is
final. -/
theorem final_costructuredArrow_map₂_overMap (hsq : IsPullback a b c d) (W : Over V') :
    (CostructuredArrow.map₂ (S := Over.map b) (T := W) (U := Over.map c)
        (V := (Over.map d).obj W) (F := Over.map a) (G := Over.map d)
        (eqToHom (overMapSquareEq hsq.toCommSq).symm)
        (𝟙 ((Over.map d).obj W))).Final :=
  have := guitartExact_overMapSquare hsq
  Functor.final_of_natIso (costructuredArrowComparisonIso hsq.toCommSq W).symm

end Stacks.Sites.RelocalizationCofinality

end
