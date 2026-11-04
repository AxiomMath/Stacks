module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingMorphismObjects

/-!
# The base change of a limit preserving 1-morphism (Stacks 0CMT)

Let `p : 𝒳 ⟶ 𝒴` and `q : 𝒵 ⟶ 𝒴` be 1-morphisms of categories fibred in groupoids over the big
fppf category of a scheme `S`. Stacks 0CMT asserts that the base change `p' : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a
limit preserving `p` is again limit preserving. This file proves that `p'` is limit preserving
*on objects* in the sense of Stacks 06CU.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_twoFibreProductSnd`: the base change of a
  limit preserving 1-morphism is limit preserving on objects.

## Implementation notes

The conclusion is the objectwise shadow of Stacks 0CMT, and the tag records that restriction. It
is the composite of Stacks 0CMS, which turns limit preservation into limit preservation on
objects, with Stacks 06CV, the stability of the latter under base change along the 2-fibre
product. The full conclusion of Stacks 0CMT — that the square of Stacks 0CMR for `p'` is
2-cartesian — needs the statement, omitted in the source, that filtered colimits of categories
commute with 2-fibre products, since the left vertical functor of that square has
`colim (𝒳 ×_𝒴 𝒵)_{Uᵢ}` as its source and the square compares it with
`colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒵_{Uᵢ}`.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CV](https://stacks.math.columbia.edu/tag/06CV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w

/-- The base change along `q` of a limit preserving 1-morphism `p` of categories fibred in
groupoids over the big fppf category of `S` is limit preserving on objects: every object of
`𝒳 ×_𝒴 𝒵` over an affine inverse limit, with a cartesian comparison to an object of `𝒵` at a
finite stage, descends to a later stage. -/
@[stacks 0CMT "limit preservation on objects of the base change"]
theorem isLimitPreservingOnObjects_twoFibreProductSnd
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (BigFppfOver B S hS))
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    (hp : IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS p) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w} B S hS
      (BigFppfOver.twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q) 𝒵
      (BigFppfOver.twoFibreProductSnd B S hS 𝒳 𝒴 𝒵 p q) :=
  BigFppfOver.isLimitPreservingOnObjects_baseChange.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q
    (isLimitPreservingOnObjects_of_isLimitPreserving.{u, v, w} B S hS p hp)

end AlgebraicGeometry.Stack

end
