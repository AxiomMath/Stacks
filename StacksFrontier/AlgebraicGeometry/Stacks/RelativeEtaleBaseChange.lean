module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange

/-!
# Base change of relative étaleness (Stacks 045C at étaleness)

**Stacks 045C** says that the relative property of **Stacks 03YK** carried by a 1-morphism
representable by algebraic spaces is inherited by its base changes. The library's statement,
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`, is about
`AlgebraicGeometry.Stack.HasRelativeProperty`, whose two instance arguments include
`P.IsLocalAtTarget (AlgebraicGeometry.Space.Topology.fppf.precoverage B S hS)` — and for
étaleness of morphisms of algebraic spaces that instance is **not** available, which is why
`AlgebraicGeometry.Stack.IsRelativelyEtale` is written longhand in the first place. This module
proves the base change for the longhand notion.

## Main results

* `AlgebraicGeometry.Stack.isRelativelyEtale_baseChange`: in a 2-fibre product square over a
  cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴`, the projection to `𝒵` is relatively étale as soon as `f` is.

## Implementation notes

No hypothesis on the property is used, and none is needed: the proof of
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` **uses neither of its two instances**.
They are there only because they are part of the statement of
`AlgebraicGeometry.Stack.HasRelativeProperty`. The argument is the same one here, read on the
longhand notion: a scheme-valued point of `𝒵` becomes one of `𝒴` by composing with `g`, and
`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver` identifies the fibre of the
projection over the first with the fibre of `f` over the second, so an algebraic space
representing one represents the other.

This is the étale counterpart of
`AlgebraicGeometry.Stack.isRelativelySmooth_baseChange`, which *can* go through the short
spelling because both instances are discharged for smoothness.

The universes are pinned, not maximally general: `AlgebraicGeometry.Stack.IsRelativelyEtale` is
stated for `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, so the three categories
have to live there, and the two inputs are instantiated at `.{u, u, u + 1}`.

## References

* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 045C at étaleness.** In a 2-fibre product square over a cospan `g : 𝒵 ⟶ 𝒴`,
`f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S`, the projection to
`𝒵` is étale in the sense of Stacks 04XB as soon as `f` is.

This is the longhand `AlgebraicGeometry.Stack.IsRelativelyEtale`, so the statement carries no
instance on the property — see the implementation notes of this module for why none is
needed. -/
theorem isRelativelyEtale_baseChange
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsRelativelyEtale B S hS f) :
    IsRelativelyEtale B S hS R.fst := by
  obtain ⟨hfr, hfet⟩ := hf
  refine ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 f g R hR hfr,
    fun U z hz F hF he => ?_⟩
  refine hfet U (z ⋙ g.hom.toFunctor) (by rw [Functor.assoc, g.hom.w, hz]) F hF ?_
  obtain ⟨e⟩ := he
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 f g R hR U z hz
  exact ⟨E.symm.trans e⟩

end AlgebraicGeometry.Stack

end
