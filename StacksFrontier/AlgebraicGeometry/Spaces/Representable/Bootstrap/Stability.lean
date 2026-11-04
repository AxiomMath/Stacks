module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces

/-!
# Stability of representability by algebraic spaces

A morphism of presheaves on the big fppf site of a scheme `S` is *representable by algebraic
spaces* when every one of its base changes along a scheme-valued point of its target is an
algebraic space over `S`.  This file collects the stability properties of that notion: every
morphism of algebraic spaces has it, a base change of such a morphism along a morphism from
an algebraic space is again an algebraic space, and the class of such morphisms is closed
under composition and under binary products.  It also records the permanence property: a
first factor of a composite is representable by algebraic spaces as soon as the composite is
and the relative diagonal of the second factor is.

## Main results

* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace`:
  **Stacks 03BN**.
* `AlgebraicGeometry.Space.isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 03XY**.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_comp`: **Stacks 03Y1**.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_prod_map`: **Stacks 046D**.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_comp`: **Stacks 0AMN**.
* `CategoryTheory.IsPullback.of_prod_snd_with_id`: the square expressing that the second
  projection of a binary product is a base change of itself along a map of the first factor.

## Implementation notes

The transport of the algebraic-space condition along an isomorphism of presheaves is
`AlgebraicGeometry.IsAlgebraicSpace.of_iso`, so the three clauses of
`AlgebraicGeometry.IsAlgebraicSpace` are never re-verified by hand here: each proof
identifies the relevant presheaf with a chosen pullback and transports.

`CategoryTheory.IsPullback.of_prod_snd_with_id` is the mirror image of Mathlib's
`CategoryTheory.IsPullback.of_prod_fst_with_id`; both are needed because the product of two
morphisms factors as a product with an identity on either side, and the two factorisations
are base changes of the two given morphisms along opposite projections.

## References

* [Stacks Project, Tag 03BN](https://stacks.math.columbia.edu/tag/03BN)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 03Y1](https://stacks.math.columbia.edu/tag/03Y1)
* [Stacks Project, Tag 046D](https://stacks.math.columbia.edu/tag/046D)
* [Stacks Project, Tag 0AMN](https://stacks.math.columbia.edu/tag/0AMN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsPullback

variable {C : Type u} [Category.{v} C]

/-- Given a morphism `f : A ⟶ B` and an object `X`, the square
```
X ⨯ A ⟶ A
  |      |
  v      v
X ⨯ B ⟶ B
```
whose horizontal arrows are the second projections and whose left-hand arrow is
`prod.map (𝟙 X) f` is cartesian. -/
lemma of_prod_snd_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct X A]
    [HasBinaryProduct X B] :
    IsPullback (prod.snd : X ⨯ A ⟶ A) (prod.map (𝟙 X) f) f (prod.snd : X ⨯ B ⟶ B) := by
  refine IsPullback.mk' (by simp)
    (fun _ _ _ h₁ h₂ => prod.hom_ext
      (by simpa [Category.assoc] using congrArg (· ≫ prod.fst) h₂) h₁)
    (fun _ a b h => ⟨prod.lift (b ≫ prod.fst) a, by simp, ?_⟩)
  exact prod.hom_ext (by simp) (by simpa using h)

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03BN.** A morphism between algebraic spaces over `S` is representable by
algebraic spaces: its base change along a scheme-valued point of its target is a fibre
product of three algebraic spaces. -/
@[stacks 03BN]
theorem isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsRepresentableByAlgebraicSpaces B S hS f := fun U ξ =>
  isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS U) hX hY

/-- **Stacks 03XY.** The fibre product of an algebraic space over `S` with the source of a
morphism representable by algebraic spaces, over the target of that morphism, is an
algebraic space over `S`. -/
@[stacks 03XY]
theorem isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces
    {F G X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (f : X ⟶ G)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hX : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpace B S hS (pullback f a) :=
  isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces B S hS (pullback.fst f a)
    (isRepresentableByAlgebraicSpaces_of_isPullback B S hS (pullback.snd f a)
      (pullback.fst f a) a f (IsPullback.of_hasPullback f a).flip ha) hX

/-- **Stacks 03Y1.** A composite of morphisms of presheaves on the big fppf site of `S`
representable by algebraic spaces is representable by algebraic spaces.

The base change of `a ≫ b` along `ξ` is the base change of `a` along the second projection
of the base change of `b` along `ξ`, which is an algebraic space by Stacks 03XY. -/
@[stacks 03Y1]
theorem isRepresentableByAlgebraicSpaces_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hb : IsRepresentableByAlgebraicSpaces B S hS b) :
    IsRepresentableByAlgebraicSpaces B S hS (a ≫ b) := fun U ξ =>
  (isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS a
    (pullback.snd ξ b) ha (hb U ξ)).of_iso (pullbackLeftPullbackSndIso ξ b a)

/-- **Stacks 046D.** The product of two morphisms of presheaves on the big fppf site of `S`
representable by algebraic spaces is representable by algebraic spaces.

The product `a₁ ⨯ a₂` is the composite of `a₁ ⨯ 𝟙` with `𝟙 ⨯ a₂`, and each of these is a
base change of one of the two factors along a projection. -/
@[stacks 046D]
lemma isRepresentableByAlgebraicSpaces_prod_map
    {F₁ F₂ G₁ G₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (h₁ : IsRepresentableByAlgebraicSpaces B S hS a₁)
    (h₂ : IsRepresentableByAlgebraicSpaces B S hS a₂) :
    IsRepresentableByAlgebraicSpaces B S hS (prod.map a₁ a₂) := by
  simpa [prod.map_map] using
    (isRepresentableByAlgebraicSpaces_comp B S hS
      (prod.map a₁ (𝟙 F₂)) (prod.map (𝟙 G₁) a₂)
      (isRepresentableByAlgebraicSpaces_of_isPullback B S hS
        prod.fst (prod.map a₁ (𝟙 F₂)) a₁ prod.fst
        (IsPullback.of_prod_fst_with_id a₁ F₂) h₁)
      (isRepresentableByAlgebraicSpaces_of_isPullback B S hS
        prod.snd (prod.map (𝟙 G₁) a₂) a₂ prod.snd
        (IsPullback.of_prod_snd_with_id a₂ G₁) h₂))

/-- **Stacks 0AMN.** If the relative diagonal of `b` and the composite `a ≫ b` are
representable by algebraic spaces, then so is `a`.

The base change of `a` along `ξ` is the base change of the relative diagonal of `b` along
the canonical morphism from the base change of `a ≫ b` along `ξ ≫ b` to `pullback b b`. -/
@[stacks 0AMN]
theorem isRepresentableByAlgebraicSpaces_of_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (pullback.diagonal b))
    (hcomp : IsRepresentableByAlgebraicSpaces B S hS (a ≫ b)) :
    IsRepresentableByAlgebraicSpaces B S hS a := by
  intro U ξ
  refine (isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS
    (pullback.diagonal b)
    (pullback.map (ξ ≫ b) (a ≫ b) b b ξ a (𝟙 _) (by simp) (by simp)) hdiag
    (hcomp U (ξ ≫ b))).of_iso ?_
  exact pullbackSymmetry _ _ ≪≫ pullbackDiagonalMapIdIso ξ a b

end AlgebraicGeometry.Space

end
