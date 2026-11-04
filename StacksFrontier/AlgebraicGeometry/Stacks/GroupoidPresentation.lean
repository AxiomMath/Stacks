module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion

/-!
# Presentations of a stack by a smooth groupoid in algebraic spaces

Let `S` be a scheme of a big fppf site. A *presentation* of a category `𝒳` over
`(Sch/S)_fppf` is a smooth groupoid `(U, R, s, t, c)` in algebraic spaces over `S` together with
an equivalence `[U/R] ⟶ 𝒳` of categories over the site, where `[U/R]` is the quotient stack.

## Main definitions

* `AlgebraicGeometry.Stack.baseSpace`: the algebraic space represented by the terminal object of
  `(Sch/S)_fppf`, that is, `S` read as an algebraic space over itself.
* `AlgebraicGeometry.Stack.GroupoidPresentation`: a presentation of a category over
  `(Sch/S)_fppf` by a smooth groupoid in algebraic spaces over
  `AlgebraicGeometry.Stack.baseSpace`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.basedFunctor`: the presenting 1-morphism
  `[U/R] ⥤ᵇ 𝒳` of a presentation.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.isEquivalence_basedFunctor`: the underlying
  functor of the presenting 1-morphism is an equivalence.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base scheme `S`, read as an algebraic space over itself: the presheaf represented by
the terminal object of `(Sch/S)_fppf`. -/
noncomputable abbrev baseSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (⊤_ (BigFppfOver B S hS)), isAlgebraicSpace_yoneda B S hS _⟩

/-- A *presentation* of a category `𝒳` over `(Sch/S)_fppf` is a smooth groupoid
`(U, R, s, t, c)` in algebraic spaces over `S` together with an equivalence of categories over
the site from its quotient stack `[U/R]` to `𝒳`. -/
@[stacks 04TI]
structure GroupoidPresentation (𝒳 : BasedCategory.{v, w} (BigFppfOver B S hS)) where
  /-- The presenting groupoid in algebraic spaces over `S`. -/
  groupoid : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS)
  /-- The presenting groupoid is smooth, i.e. its source and target maps are smooth. -/
  smooth : GroupoidInAlgebraicSpaces.IsSmooth B S hS groupoid
  /-- The equivalence of categories over the site from the quotient stack to `𝒳`. -/
  equivalence : StacksRepresentableCFG.EquivalenceOver (quotientStack groupoid).p 𝒳.p

namespace GroupoidPresentation

variable {B S hS} {𝒳 : BasedCategory.{v, w} (BigFppfOver B S hS)}

/-- The presenting 1-morphism `[U/R] ⥤ᵇ 𝒳` of a presentation: the forward functor of its
equivalence, with the strict commuting equation that makes it a functor over the site. -/
def basedFunctor (P : GroupoidPresentation B S hS 𝒳) : quotientStack P.groupoid ⥤ᵇ 𝒳 :=
  ⟨P.equivalence.hom.functor, P.equivalence.hom.w⟩

/-- The underlying functor of the presenting 1-morphism of a presentation is an equivalence of
categories. -/
noncomputable instance isEquivalence_basedFunctor (P : GroupoidPresentation B S hS 𝒳) :
    P.basedFunctor.toFunctor.IsEquivalence :=
  P.equivalence.toEquivalence.isEquivalence_functor

end GroupoidPresentation

end AlgebraicGeometry.Stack

end
