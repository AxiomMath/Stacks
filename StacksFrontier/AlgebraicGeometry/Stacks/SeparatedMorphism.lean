module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# Separated, proper and universally closed representable 1-morphisms of stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces. Following Stacks 04XB, `f` *is separated*,
*is proper*, respectively *is universally closed* when every algebraic space representing
the base change of `f` along a scheme-valued point of `𝒴` has separated, proper,
respectively universally closed structural morphism, read as a morphism of algebraic spaces
over `S`.

## Main definitions

* `AlgebraicGeometry.Stack.IsSeparated`
* `AlgebraicGeometry.Stack.IsProper`
* `AlgebraicGeometry.Stack.UniversallyClosed`

## Main results

There are no propositional results here. In particular Stacks 04YS — that a representable
1-morphism of algebraic stacks is separated exactly when its relative diagonal is a closed
immersion, proper, or universally closed — is *not* proved here; see the implementation
notes.

## Implementation notes

The three predicates are the relative property of Stacks 03YK
(`AlgebraicGeometry.Stack.HasRelativeProperty`) for the three properties of morphisms of
algebraic spaces `AlgebraicGeometry.Space.IsSeparated`,
`AlgebraicGeometry.Space.IsProper` and `AlgebraicGeometry.Space.UniversallyClosed`, written
out rather than expressed through `HasRelativeProperty` itself: the latter is stated for a
`CategoryTheory.MorphismProperty` on the category of algebraic spaces over `S` carrying two
instance hypotheses — stability under base change and locality at the target for the fppf
precoverage — and those instances for these three properties are results of Chapter 67 that
this library does not have. Writing the quantifier out gives the same proposition with no
hypothesis on the property, which is what a consumer of Stacks 04YS or 0512 needs in order
to *state* its result. When the two instances become available each predicate should be
replaced by, or related to, the corresponding `HasRelativeProperty`.

No declaration here carries a `@[stacks]` attribute. The notions belong to Stacks 04XB,
which is a section of Properties of Stacks introducing a notion for *every* property of
morphisms of algebraic spaces stable under base change and local at the target, and that
general notion is already tagged, as `AlgebraicGeometry.Stack.HasRelativeProperty`
(**Stacks 03YK**); the three predicates below are its instances at three specific
properties, so tagging them would claim a tag that the general definition already covers.
Stacks 04YS's own tag belongs to its "the following are equivalent" theorem, which is not
proved here.

As in `AlgebraicGeometry.Stack.HasRelativeProperty`, a scheme-valued point of `𝒴` is a
functor from the big fppf site of a scheme `U` over `S` to the total category of `𝒴` lying
over `CategoryTheory.Over.map U.hom`; quantifying over *all* algebraic spaces representing
the base change makes the condition independent of the choice made in Stacks 0402. The
passage from an algebraic space over `U` to one over `S` is the forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG, whose structural morphism
is read off by `AlgebraicGeometry.algebraicSpaceMap`.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is separated* when every algebraic space representing its
base change along a scheme-valued point of the target has separated structural morphism,
read as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsSeparated`. -/
abbrev IsSeparated (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsSeparated B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is proper* when every algebraic space representing its
base change along a scheme-valued point of the target has proper structural morphism, read
as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsProper`. -/
abbrev IsProper (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsProper B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is universally closed* when every algebraic space
representing its base change along a scheme-valued point of the target has universally
closed structural morphism, read as a morphism of algebraic spaces over `S`. This is the
notion of Stacks 04XB for `AlgebraicGeometry.Space.UniversallyClosed`. -/
abbrev UniversallyClosed (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.UniversallyClosed B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end AlgebraicGeometry.Stack

end
