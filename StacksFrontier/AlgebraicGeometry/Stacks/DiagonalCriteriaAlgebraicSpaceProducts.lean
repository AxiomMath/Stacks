module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources

/-!
# The criteria for a representable diagonal: conditions (7) and (8) (Stacks 045G)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Condition (7) of Stacks 045G says that every 1-morphism
to `𝒳` out of a category fibred in groupoids representable by an algebraic space over `S` is
representable by algebraic spaces, and condition (8) says that the 2-fibre product over `𝒳` of any
two such 1-morphisms is representable by an algebraic space. The source calls this equivalence
formal, and it is: both conditions are about the same 2-fibre products.

Condition (7) implies condition (8) by Stacks 0300, which is exactly the statement that a 2-fibre
product one of whose legs is representable by algebraic spaces and whose other factor is
representable by an algebraic space is representable by an algebraic space. Conversely, the
2-fibre product of a scheme-valued point of `𝒳` with the given 1-morphism is an instance of
condition (8) — a slice of the site is representable by an algebraic space — and the pointwise
criterion
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct` turns that
into condition (7).

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_precomposeFst_iff`: the
  2-fibre product over `𝒳` is representable by an algebraic space exactly when the one obtained by
  precomposing its first leg with an equivalence over the site is.
* `isRepresentableFromAlgebraicSpaces_iff_hasAlgebraicSpaceProducts`, in the namespace
  `AlgebraicGeometry.Stack`: **Stacks 045G**, the equivalence of conditions (7) and (8).

## Implementation notes

Both conditions quantify over categories fibred in groupoids at the universes
`(max u v₁, max (u+1) w₁)` for the first factor and `(max u v₂, max (u+1) w₂)` for the second,
while condition (7) names only the first pair. So in each direction the hypothesis has to be
instantiated at the factor whose universes it fits, and the resulting 2-fibre product comes out
with its factors in the opposite order to the one the goal asks for;
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff` repairs that.

Going up, the first factor is a slice of the site, which lives at `(u, u+1)` and must be replaced
by its universe lift `CategoryTheory.CatFiberedInGroupoids.ulift` to be an admissible argument of
the quantifier of condition (8), exactly as in the equivalence of conditions (5) and (6). The
comparison of the two 2-fibre products is `CategoryTheory.TwoFibreProductOver.precomposeFst` along
`CategoryTheory.BasedCategory.uliftDown`, isolated here as
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_precomposeFst_iff`; it is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_precompose_iff` with the
second factor left alone, which is what is wanted here because the second factor is the given
category fibred in groupoids and does not move.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂ a₁ b₁ a₂ b₂ a₃ b₃

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **The 2-fibre product over `𝒳` does not see an equivalence of its first factor.** If `t` is a
1-morphism over the site whose underlying functor is an equivalence, then the 2-fibre product of
`x` and `y` over `𝒳` is representable by an algebraic space exactly when the 2-fibre product of
`t ≫ x` and `y` is.

This is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_precompose_iff` with the
second factor left alone. As there, the hypothesis that `t` is an equivalence is explicit, not an
instance argument: the total categories are those of `CategoryTheory.BasedCategory`s, whose
`Category` instance is not the one instance search finds for the same type. -/
theorem isRepresentableByAlgebraicSpace_twoFibreProduct_precomposeFst_iff
    (𝒯₁ : CatFiberedInGroupoids.{u, a₁, u + 1, b₁} (BigFppfOver B S hS))
    (𝒯₁' : CatFiberedInGroupoids.{u, a₂, u + 1, b₂} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, a₃, u + 1, b₃} (BigFppfOver B S hS))
    (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val)
    (t : 𝒯₁'.val ⥤ᵇ 𝒯₁.val) (hte : Functor.IsEquivalence t.toFunctor) :
    IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y) ↔
      IsRepresentableByAlgebraicSpace B S hS
        (twoFibreProduct B S hS 𝒳 𝒯₁' 𝒯₂ (BasedFunctor.comp t x) y) := by
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (TwoFibreProductOver.isFiberedInGroupoids 𝒯₁'.val.p 𝒯₂.val.p 𝒳.val.p
      (t.toFunctor ⋙ x.toFunctor) y.toFunctor
      𝒯₁'.isFiberedInGroupoids 𝒯₂.isFiberedInGroupoids 𝒳.isFiberedInGroupoids
      (BasedFunctor.comp t x).w y.w)
    (TwoFibreProductOver.isFiberedInGroupoids 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.toFunctor y.toFunctor
      𝒯₁.isFiberedInGroupoids 𝒯₂.isFiberedInGroupoids 𝒳.isFiberedInGroupoids x.w y.w)
    (TwoFibreProductOver.precomposeFst 𝒯₁'.val.p 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p
      x.toFunctor y.toFunctor t.toFunctor t.w)
    (TwoFibreProductOver.precomposeFst_comp_structureFunctor _ _ _ _ _ _ _ _)
    (TwoFibreProductOver.isEquivalence_precomposeFst 𝒯₁'.val.p 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p
      x.toFunctor y.toFunctor t.toFunctor t.w
      𝒯₂.isFiberedInGroupoids 𝒯₁'.isFiberedInGroupoids 𝒯₁.isFiberedInGroupoids hte x.w)
  exact isRepresentableByAlgebraicSpace_iff_of_equivalenceOver k

/-- **Stacks 045G, the equivalence of conditions (7) and (8).** Every 1-morphism to `𝒳` out of a
category fibred in groupoids representable by an algebraic space over `S` is representable by
algebraic spaces if and only if the 2-fibre product over `𝒳` of any two such 1-morphisms is
representable by an algebraic space. -/
@[stacks 045G "parts (7) and (8)"]
theorem isRepresentableFromAlgebraicSpaces_iff_hasAlgebraicSpaceProducts :
    IsRepresentableFromAlgebraicSpaces.{u, v, w, v₁, w₁} B S hS 𝒳 ↔
      HasAlgebraicSpaceProducts.{u, v, w, v₁, w₁, v₂, w₂} B S hS 𝒳 := by
  constructor
  · intro h₇ 𝒯₁ 𝒯₂ hT₁ hT₂ x y
    exact (isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff B S hS 𝒳 𝒯₂ 𝒯₁ y x).1
      (isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳 𝒯₂ 𝒯₁ y x (h₇ 𝒯₁ hT₁ x) hT₂)
  · intro h₈ 𝒯 h𝒯 x
    refine isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct B S hS 𝒳 𝒯 x fun V y => ?_
    let t : (CatFiberedInGroupoids.ulift.{u, u + 1, u, u + 1, v₂, w₂}
        (schemeFibredCategory B S hS V)).val ⥤ᵇ (schemeFibredCategory B S hS V).val :=
      ⟨BasedCategory.uliftDown (schemeFibredCategory B S hS V).val,
        BasedCategory.uliftDown_comp (schemeFibredCategory B S hS V).val⟩
    refine (isRepresentableByAlgebraicSpace_twoFibreProduct_precomposeFst_iff B S hS 𝒳
      (schemeFibredCategory B S hS V) _ 𝒯 y x t
      ((BasedCategory.uliftEquivalenceOver
        (schemeFibredCategory B S hS V).val).isEquivalence_hom_functor)).2 ?_
    exact (isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff B S hS 𝒳 𝒯 _ x
      (BasedFunctor.comp t y)).1
      (h₈ 𝒯 _ h𝒯 (isRepresentableByAlgebraicSpace_of_equivalenceOver
        (BasedCategory.uliftEquivalenceOver (schemeFibredCategory B S hS V).val)
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)) x _)

end AlgebraicGeometry.Stack

end
