module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# Affine 1-morphisms of algebraic stacks (Stacks 0CHQ)

Following Stacks 0CHQ, a 1-morphism of algebraic stacks over `S` *is affine* when it is
representable and affine in the sense of Stacks 04XB: every algebraic space representing its
base change along a scheme-valued point of the target has affine structural morphism, read as a
morphism of algebraic spaces over `S`.

As with the immersions of Stacks 04YL, the source reads "representable, and affine in the sense
of Section 04XB", and the §04XB notions are stated for 1-morphisms representable by *algebraic
spaces*; that is the form taken here, and it is the form in which
`AlgebraicGeometry.Stack.AlgebraicStacks.IsOpenImmersion` and its companions are already formalized.

## Main definitions

* `AlgebraicGeometry.Stack.IsAffineHom`: the Stacks 04XB notion at
  `AlgebraicGeometry.Space.IsAffineHom`, for a 1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom`: **Stacks 0CHQ**.

## Implementation notes

The predicate is written out rather than expressed through
`AlgebraicGeometry.Stack.HasRelativeProperty`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism`: that definition carries two instance
hypotheses on the tested property — stability under base change and locality at the target for
the fppf precoverage — which for affineness of morphisms of algebraic spaces are Stacks 03WG and
Stacks 03WJ, neither of which this library has, while its body uses neither. Writing the
quantifier out therefore gives *the same* proposition carrying no hypothesis on the property, and
keeps affineness of a 1-morphism available now. The same choice is made for the three immersion
predicates of Stacks 04YL and for `AlgebraicGeometry.Stack.IsRelativelyEtale`; compare
`AlgebraicGeometry.Stack.IsRelativelySmooth`, which can use the short spelling because both
instances are discharged for smoothness.

As in `AlgebraicGeometry.Stack.HasRelativeProperty`, a scheme-valued point of the target is a
functor from the big fppf site of a scheme `U` over `S` to the total category of the target lying
over `CategoryTheory.Over.map U.hom`, and quantifying over *all* algebraic spaces representing
the base change makes the condition independent of the choice made in Stacks 0402. The passage
from an algebraic space over `U` to one over `S` is
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG, whose structural morphism is read
off by `AlgebraicGeometry.algebraicSpaceMap`.

The tag sits on the predicate in the `AlgebraicGeometry.Stack.AlgebraicStacks` namespace, which
is the notion of Stacks 0CHQ for a 1-morphism of *algebraic stacks*; the predicate in
`AlgebraicGeometry.Stack` is the Stacks 04XB notion it is built from, and Stacks 04XB's general
definition is already tagged as `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**),
so it is untagged.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

section FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is affine* when every algebraic space representing its base
change along a scheme-valued point of the target has affine structural morphism, read as a
morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsAffineHom`; together with representability by algebraic spaces it is
Stacks 0CHQ. -/
abbrev IsAffineHom (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsAffineHom B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end FiberedInGroupoids

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CHQ.** A 1-morphism of algebraic stacks over `S` is *affine* when it is
representable by algebraic spaces and is affine in the sense of Stacks 04XB. -/
@[stacks 0CHQ]
abbrev IsAffineHom (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧ Stack.IsAffineHom B S hS f.hom

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
