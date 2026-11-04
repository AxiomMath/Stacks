module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentEtaleLocal
public import StacksFrontier.CategoryTheory.Sites.Descent.BaseChangeMatePasting

/-!
# Pasting the base-change `2`-cells on the spaces-étale topoi

For a cartesian square of algebraic spaces over `S`
```
X' --i--> X
|f'       |f
Y' --g--> Y
```
the base-change `2`-cell `AlgebraicGeometry.Space.spacesToposBaseChangeSquare` is the comparison
`g⁻¹ f_* ⟶ f'_* i⁻¹` of functors from sheaves on `X` to sheaves on `Y'`. This file proves that it
is compatible with pasting cartesian squares horizontally (along the bottom arrow), in the form
of the consequences for invertibility. Vertical pasting is used in the form of
`CategoryTheory.Pseudofunctor.isIso_mateEquiv_commSqTwoSquare_comp_of_paste_vert`, through
`AlgebraicGeometry.Space.spacesToposBaseChangeSquare_eq_mateEquiv`.

## Main results

* `AlgebraicGeometry.Space.spacesToposBaseChangeSquare_eq_mateEquiv`: the `2`-cell is the mate of
  the comparison isomorphism of the pseudofunctor of spaces-étale inverse images.
* `AlgebraicGeometry.Space.isIso_spacesToposBaseChangeSquare_paste_horiz`,
  `AlgebraicGeometry.Space.isIso_whiskerRight_of_paste_horiz` and
  `AlgebraicGeometry.Space.isIso_whiskerLeft_of_paste_horiz` (with their componentwise forms
  `AlgebraicGeometry.Space.isIso_spacesEtaleInverseImage_map_of_paste_horiz` and
  `AlgebraicGeometry.Space.isIso_app_of_paste_horiz`): two of the three `2`-cells being
  invertible, so is (the relevant whiskering of) the third.

## Implementation notes

`AlgebraicGeometry.Space.mateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq` identifies the
`2`-cell with the mate, across the adjunctions of the two vertical arrows, of the comparison
isomorphism of the pseudofunctor of spaces-étale inverse images attached to the square. The
invertibility statements are then the general ones of
`StacksFrontier.CategoryTheory.Sites.Descent.BaseChangeMatePasting`. They are transported along that
identification of natural transformations only, never componentwise: the two descriptions of the
functors involved agree only after unfolding the pseudofunctor, which is cheap for the natural
transformations and expensive for their components.

## References

* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base-change `2`-cell of a cartesian square is the mate, across the adjunctions of the two
vertical arrows written through the pseudofunctor of spaces-étale inverse images, of the
comparison isomorphism of that pseudofunctor attached to the square. -/
theorem spacesToposBaseChangeSquare_eq_mateEquiv {X Y X' Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback i f' f g) :
    spacesToposBaseChangeSquare B S hS i f' f g sq =
      (mateEquiv (spacesEtalePseudofunctorAdjunction B S hS f)
        (spacesEtalePseudofunctorAdjunction B S hS f')
        (Pseudofunctor.commSqTwoSquare (spacesEtalePseudofunctor B S hS) sq.w)).natTrans :=
  (mateEquiv_spacesEtalePseudofunctor_isoMapOfCommSq B S hS i f' f g sq).symm

section Horiz

variable {X Y X' Y' X'' Y'' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (e : Y'' ⟶ Y')
  (sq₁ : IsPullback i f' f g) (sq₂ : IsPullback j f'' f' e)

/-- **The outer square of two horizontally pasted cartesian squares has invertible base-change
`2`-cell** as soon as the two squares have. -/
theorem isIso_spacesToposBaseChangeSquare_paste_horiz
    (h₁ : IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq₁))
    (h₂ : IsIso (spacesToposBaseChangeSquare B S hS j f'' f' e sq₂)) :
    IsIso (spacesToposBaseChangeSquare B S hS (j ≫ i) f'' f (e ≫ g) (sq₂.paste_horiz sq₁)) := by
  rw [spacesToposBaseChangeSquare_eq_mateEquiv] at h₁ h₂ ⊢
  exact Pseudofunctor.isIso_mateEquiv_commSqTwoSquare_paste_horiz _ i f' f g j f'' e sq₁.w
    sq₂.w (sq₂.paste_horiz sq₁).w _ _ _ h₁ h₂

/-- **Cancelling the second square.** If the outer square of two horizontally pasted cartesian
squares and the second square have invertible base-change `2`-cells, then the inverse image along
`e` of the `2`-cell of the first square is invertible. -/
theorem isIso_whiskerRight_of_paste_horiz
    (hout : IsIso (spacesToposBaseChangeSquare B S hS (j ≫ i) f'' f (e ≫ g)
      (sq₂.paste_horiz sq₁)))
    (h₂ : IsIso (spacesToposBaseChangeSquare B S hS j f'' f' e sq₂)) :
    IsIso (Functor.whiskerRight (spacesToposBaseChangeSquare B S hS i f' f g sq₁)
      (spacesEtaleInverseImage B S hS e)) := by
  rw [spacesToposBaseChangeSquare_eq_mateEquiv] at hout h₂ ⊢
  exact Pseudofunctor.isIso_whiskerRight_mateEquiv_commSqTwoSquare_of_paste_horiz _ i f' f g j
    f'' e sq₁.w sq₂.w (sq₂.paste_horiz sq₁).w _ _ _ hout h₂

/-- The same, at a sheaf. -/
theorem isIso_spacesEtaleInverseImage_map_of_paste_horiz
    (hout : IsIso (spacesToposBaseChangeSquare B S hS (j ≫ i) f'' f (e ≫ g)
      (sq₂.paste_horiz sq₁)))
    (h₂ : IsIso (spacesToposBaseChangeSquare B S hS j f'' f' e sq₂))
    (M : spacesEtaleSheafCat B S hS X) :
    IsIso ((spacesEtaleInverseImage B S hS e).map
      ((spacesToposBaseChangeSquare B S hS i f' f g sq₁).app M)) :=
  have := isIso_whiskerRight_of_paste_horiz B S hS i f' f g j f'' e sq₁ sq₂ hout h₂
  NatIso.isIso_app_of_isIso (Functor.whiskerRight
    (spacesToposBaseChangeSquare B S hS i f' f g sq₁) (spacesEtaleInverseImage B S hS e)) M

/-- **Cancelling the first square.** If the outer square of two horizontally pasted cartesian
squares and the first square have invertible base-change `2`-cells, then the `2`-cell of the
second square is invertible after precomposition with the inverse image along `i`. -/
theorem isIso_whiskerLeft_of_paste_horiz
    (hout : IsIso (spacesToposBaseChangeSquare B S hS (j ≫ i) f'' f (e ≫ g)
      (sq₂.paste_horiz sq₁)))
    (h₁ : IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq₁)) :
    IsIso (Functor.whiskerLeft (spacesEtaleInverseImage B S hS i)
      (spacesToposBaseChangeSquare B S hS j f'' f' e sq₂)) := by
  rw [spacesToposBaseChangeSquare_eq_mateEquiv] at hout h₁ ⊢
  exact Pseudofunctor.isIso_whiskerLeft_mateEquiv_commSqTwoSquare_of_paste_horiz _ i f' f g j
    f'' e sq₁.w sq₂.w (sq₂.paste_horiz sq₁).w _ _ _ hout h₁

/-- The same, at a sheaf. -/
theorem isIso_app_of_paste_horiz
    (hout : IsIso (spacesToposBaseChangeSquare B S hS (j ≫ i) f'' f (e ≫ g)
      (sq₂.paste_horiz sq₁)))
    (h₁ : IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq₁))
    (M : spacesEtaleSheafCat B S hS X) :
    IsIso ((spacesToposBaseChangeSquare B S hS j f'' f' e sq₂).app
      ((spacesEtaleInverseImage B S hS i).obj M)) :=
  have := isIso_whiskerLeft_of_paste_horiz B S hS i f' f g j f'' e sq₁ sq₂ hout h₁
  NatIso.isIso_app_of_isIso (Functor.whiskerLeft (spacesEtaleInverseImage B S hS i)
    (spacesToposBaseChangeSquare B S hS j f'' f' e sq₂)) M

end Horiz

end AlgebraicGeometry.Space

end
