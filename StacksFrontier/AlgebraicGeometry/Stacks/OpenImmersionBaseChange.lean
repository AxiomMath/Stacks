module

public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange

/-!
# Base change of the open-immersion property of Stacks 04XB (Stacks 045C)

In a 2-fibre product square over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over the big fppf site of `S`, the projection to `𝒵` is an open immersion in the sense
of Stacks 04XB as soon as `f` is. This is Stacks 045C at the open-immersion property of morphisms
of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.isOpenImmersion_baseChange`: in a 2-fibre product square over
  `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴`, the projection to `𝒵` is an open immersion if `f` is.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Base change of open immersions.** In a 2-fibre product square over a cospan `g : 𝒵 ⟶ 𝒴`,
`f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S`, the projection to `𝒵`
is an open immersion in the sense of Stacks 04XB as soon as `f` is. -/
theorem isOpenImmersion_baseChange
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : Stack.IsOpenImmersion B S hS f) :
    Stack.IsOpenImmersion B S hS R.fst := by
  intro U z hz F hF he
  refine hf U (z ⋙ g.hom.toFunctor) (by rw [Functor.assoc, g.hom.w, hz]) F hF ?_
  obtain ⟨e⟩ := he
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR U z hz
  exact ⟨E.symm.trans e⟩

end AlgebraicGeometry.Stack

end
