module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# Quasi-compact, quasi-separated and locally quasi-finite representable 1-morphisms of stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which is representable by algebraic spaces. Following Stacks 04XB, `f` *is quasi-compact*, *is
quasi-separated*, respectively *is locally quasi-finite* when every algebraic space representing
the base change of `f` along a scheme-valued point of `𝒴` has quasi-compact, quasi-separated,
respectively locally quasi-finite structural morphism, read as a morphism of algebraic spaces
over `S`.

These three complete the family begun in `AlgebraicGeometry.Stack.SeparatedMorphism`, which
treats separatedness, properness and universal closedness in the same shape. Together the six
are the properties of Stacks 04XB that the separation lemmas of Stacks 050F, 050H and 050K
quantify over.

## Main definitions

* `AlgebraicGeometry.Stack.IsQuasiCompact`
* `AlgebraicGeometry.Stack.IsQuasiSeparated`
* `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`

## Implementation notes

The three predicates are the relative property of Stacks 03YK
(`AlgebraicGeometry.Stack.HasRelativeProperty`) for the three properties of morphisms of
algebraic spaces `AlgebraicGeometry.Space.IsQuasiCompact` (**Stacks 03HE**),
`AlgebraicGeometry.Space.IsQuasiSeparated` (**Stacks 03HL**, part (3)) and
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` (**Stacks 03XJ**, part (1)), written out rather
than expressed through `HasRelativeProperty` itself. That abbreviation is stated for a
`CategoryTheory.MorphismProperty` on the category of algebraic spaces over `S` carrying two
instance hypotheses — stability under base change and locality at the target for the fppf
precoverage — and for local quasi-finiteness this library now has both: base
change is `AlgebraicGeometry.Space.locallyQuasiFiniteProperty_isStableUnderBaseChange`
(**Stacks 03XL**, the locally quasi-finite case) and the fppf locality is
`AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fppf` (**Stacks 0427**, read off its
fpqc form). Writing the quantifier out gives the same proposition with no hypothesis on the
property, which is the reason `AlgebraicGeometry.Stack.SeparatedMorphism` gives for its own three
and the reason `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated` is written out in the
same shape.

All three cases now have both instances.
For quasi-compactness base change is Stacks 03HF and fppf locality is Stacks 041L, packaged by
`AlgebraicGeometry.Space.quasiCompactProperty`; for quasi-separatedness base change is Stacks
03KL (`AlgebraicGeometry.Space.isQuasiSeparated_isStableUnderBaseChange`) and fppf locality is
Stacks 041N (`AlgebraicGeometry.Space.isQuasiSeparated_isLocalAtTarget_fppf`), packaged by
`AlgebraicGeometry.Space.quasiSeparatedProperty`. So each of
`AlgebraicGeometry.Stack.IsQuasiCompact B S hS f` and
`AlgebraicGeometry.Stack.IsQuasiSeparated B S hS f` is related to
`AlgebraicGeometry.Stack.HasRelativeProperty B S hS _ f hf` at the corresponding packaged
property by `Iff.rfl`, and a consumer who prefers the `CategoryTheory.MorphismProperty` API may
use the latter. The same now holds of local quasi-finiteness at
`AlgebraicGeometry.Space.locallyQuasiFiniteProperty`. All three are written out here for
uniformity, and because the written-out form assumes nothing about the property.

No declaration here carries a `@[stacks]` attribute, for the reason
`AlgebraicGeometry.Stack.SeparatedMorphism` records: Stacks 04XB introduces one notion for
*every* property of morphisms of algebraic spaces stable under base change and local at the
target, and that general notion is already tagged, as
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**). The three predicates below are
its instances at three specific properties, so tagging them would claim a tag the general
definition already covers.

As in `AlgebraicGeometry.Stack.HasRelativeProperty`, a scheme-valued point of `𝒴` is a functor
from the big fppf site of a scheme `U` over `S` to the total category of `𝒴` lying over
`CategoryTheory.Over.map U.hom`; quantifying over *all* algebraic spaces representing the base
change makes the condition independent of the choice made in Stacks 0402. The passage from an
algebraic space over `U` to one over `S` is the forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG, whose structural morphism is
read off by `AlgebraicGeometry.algebraicSpaceMap`.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is quasi-compact* when every algebraic space representing its
base change along a scheme-valued point of the target has quasi-compact structural morphism,
read as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsQuasiCompact` (**Stacks 03HE**). -/
abbrev IsQuasiCompact (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsQuasiCompact B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is quasi-separated* when every algebraic space representing
its base change along a scheme-valued point of the target has quasi-separated structural
morphism, read as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsQuasiSeparated` (**Stacks 03HL**, part (3)). -/
abbrev IsQuasiSeparated (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsQuasiSeparated B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is locally quasi-finite* when every algebraic space
representing its base change along a scheme-valued point of the target has locally quasi-finite
structural morphism, read as a morphism of algebraic spaces over `S`. This is the notion of
Stacks 04XB for `AlgebraicGeometry.Space.IsLocallyQuasiFinite` (**Stacks 03XJ**, part (1)). -/
abbrev IsLocallyQuasiFinite (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsLocallyQuasiFinite B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end AlgebraicGeometry.Stack

end
