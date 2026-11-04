module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibresDiagonal

/-!
# The projections of the comparison of Stacks 02XI

The comparison `(𝒳 ×_𝒮 𝒴)_U ⥤ 𝒳_U ×_{𝒮_U} 𝒴_U` of Stacks 02XI sends `(U, x, y, φ)` to
`(x, y, φ)`, so its two projections are the functors induced on fibres by the two projections of
the 2-fibre product. This file records that -- before and after the universe lift -- which is what
exhibits the 02XI square at a fibre as a 2-commutative square whose comparison functor is an
equivalence.

## Main results

* `CategoryTheory.TwoFibreProductOver.toFiberPullback_comp_π₁` and `…_π₂`.
* `CategoryTheory.TwoFibreProductOver.asSmallFiberPullback_comp_π₁` and `…_π₂`.

## References

* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

open Limits

universe t v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₂} [Category.{v₂} 𝒴] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
  (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (U : 𝒞)

/-- **The first projection of the comparison of Stacks 02XI is the fibre of the first
projection.** -/
lemma toFiberPullback_comp_π₁ :
    toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U ⋙
        CategoricalPullback.π₁ (Functor.fiberMap p𝒳 p𝒮 F hF U)
          (Functor.fiberMap p𝒴 p𝒮 G hG U) =
      Functor.fiberFunctorOfCompEq (fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮)
        (F := F) (G := G)) U := rfl

/-- **The second projection of the comparison of Stacks 02XI is the fibre of the second
projection.** -/
lemma toFiberPullback_comp_π₂ :
    toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U ⋙
        CategoricalPullback.π₂ (Functor.fiberMap p𝒳 p𝒮 F hF U)
          (Functor.fiberMap p𝒴 p𝒮 G hG U) =
      Functor.fiberFunctorOfCompEq (snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮)
        (F := F) (G := G)) U := rfl

/-- **The first projection of the comparison of Stacks 02XI after the universe lift.** -/
lemma asSmallFiberPullback_comp_π₁ :
    asSmallFiberPullback.{t} p𝒳 p𝒴 p𝒮 F G hF hG U ⋙
        CategoricalPullback.π₁
          (AsSmall.down.{v₂, u₂, t} ⋙ Functor.fiberMap p𝒳 p𝒮 F hF U ⋙
            AsSmall.up.{v₂, u₂, t})
          (AsSmall.down.{v₂, u₂, t} ⋙ Functor.fiberMap p𝒴 p𝒮 G hG U ⋙
            AsSmall.up.{v₂, u₂, t}) =
      AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮)
          (F := F) (G := G)) U ⋙ AsSmall.up.{v₂, u₂, t} := rfl

/-- **The second projection of the comparison of Stacks 02XI after the universe lift.** -/
lemma asSmallFiberPullback_comp_π₂ :
    asSmallFiberPullback.{t} p𝒳 p𝒴 p𝒮 F G hF hG U ⋙
        CategoricalPullback.π₂
          (AsSmall.down.{v₂, u₂, t} ⋙ Functor.fiberMap p𝒳 p𝒮 F hF U ⋙
            AsSmall.up.{v₂, u₂, t})
          (AsSmall.down.{v₂, u₂, t} ⋙ Functor.fiberMap p𝒴 p𝒮 G hG U ⋙
            AsSmall.up.{v₂, u₂, t}) =
      AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮)
          (F := F) (G := G)) U ⋙ AsSmall.up.{v₂, u₂, t} := rfl

end CategoryTheory.TwoFibreProductOver

end
