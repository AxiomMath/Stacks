module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct

/-!
# The filler of a cancelled iterated 2-fibre product, assembled from the two fillers (Stacks 02XD)

`CategoryTheory.CatFiberedInGroupoids.cancelSndSquare` and
`CategoryTheory.CatFiberedInGroupoids.cancelFstSquare` exhibit an iterated 2-fibre product of
categories fibred in groupoids as a 2-commutative square over the outer cospan (**Stacks 003O**,
**Stacks 02XD**). Each of them *defines* its filler as the filler of a canonical square read
through the comparison 1-morphism of Stacks 02XD, because written that way the compatibility
square of Stacks 003O holds for that comparison with identity comparison 2-cells.

This module states, for both cancellations, that this filler is *the same 2-cell* as the one
assembled from the fillers of the two canonical squares and from the given invertible 2-cell `θ`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare_iso` and
  `CategoryTheory.CatFiberedInGroupoids.cancelFstSquare_iso`: the filler of each cancellation,
  assembled from the filler of the inner canonical square, the filler of the outer one and `θ`.

## Implementation notes

The identities are stated at the level of the invertible 2-cell rather than of its `hom`
component, so that a consumer reading the square through
`CategoryTheory.Bicategory.TwoCommSq.swap` — which inverts the filler — gets the `inv` direction
from the same lemma.

The two chains differ in exactly one place, and it is the place the two cancellations differ: the
second-factor cancellation runs through the filler of the inner square in its `hom` direction,
the first-factor one in its `inv` direction, because the leg of the inner square that the outer
product is formed over is the second one in the first case and the first one in the second.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒵 𝒳 𝒴 𝒰 : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

/-- **The filler of the second-factor cancellation, assembled from the two fillers and `θ`.**
Reading the first leg of `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare` as the composite
of the outer projection with the first leg of the inner square, its filler is: the filler of the
inner square, whiskered by the outer projection; the filler of the outer square, whiskered by
`f`; and `θ`, whiskered by the second outer projection. -/
theorem cancelSndSquare_iso (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒳) (G : 𝒰 ⟶ 𝒴)
    (θ : c ≫ f ≅ G) :
    (cancelSndSquare.{v₁, v₂, u₁, u₂} g f c G θ).iso
      = whiskerLeftIso (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).fst
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).iso
        ≪≫ whiskerRightIso (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).iso f
        ≪≫ whiskerLeftIso (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).snd θ := rfl

/-- **The filler of the first-factor cancellation, assembled from the two fillers and `θ`.** The
companion of `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare_iso`; the inner square's
filler enters in its `inv` direction, the outer product here being formed over the *first* leg of
the inner square. -/
theorem cancelFstSquare_iso (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒵) (G : 𝒰 ⟶ 𝒴)
    (θ : c ≫ g ≅ G) :
    (cancelFstSquare.{v₁, v₂, u₁, u₂} g f c G θ).iso
      = whiskerLeftIso (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).fst
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).iso.symm
        ≪≫ whiskerRightIso (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).iso g
        ≪≫ whiskerLeftIso (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).snd θ := rfl

end CategoryTheory.CatFiberedInGroupoids

end
