module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Direct image preserves injective abelian sheaves (Stacks 06WX part (1))

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred over the big fppf category of schemes
over a base scheme `S`, and let `τ` be one of the five topologies Zariski, étale, smooth,
syntomic, fppf. Direct image along `F` carries injective abelian sheaves on the site
associated with `𝒳` to injective abelian sheaves on the site associated with `𝒴`.

## Main results

* `AlgebraicGeometry.Stack.abelianDirectImage_preservesInjectiveObjects`: **Stacks 06WX**,
  part (1), preservation of injective objects by the canonical direct image on abelian
  sheaves.

## Implementation notes

The source's proof is one sentence: this is formal from `F⁻¹` being an exact left adjoint of
`F_*`, which is Homology, Lemma 015Z. The three ingredients are already in the library for an
arbitrary fibred 1-morphism, all three from Stacks 06NW: the adjunction
`IsFibredOneMorphism.sheafAdjunctionInheritedTopology`, exactness of the inverse image
`IsFibredOneMorphism.preservesFiniteLimits_inverseImage`, and the continuity and cocontinuity
that make both functors exist. Mathlib's 015Z is
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`, which asks the
left adjoint only to preserve monomorphisms; left exactness gives that through
`preservesMonomorphisms_of_preservesLimitsOfShape`.

Two points of spelling. The base topology is written as the named abbreviation
`BigFppfOver.baseOverTopology`, not as the localization `(B.baseTopology τ).over (B.obj hS)`
it unfolds to, because `BigFppfOver.associatedTopology` is defined over the former: writing
the latter leaves the cocontinuity instance of the conclusion unsynthesizable even though the
two terms are definitionally equal. And the statement is for a fibred 1-morphism rather than
the source's fibred-in-groupoids one, which is a generalization: the proof uses only the
induced adjunction and the exactness of the inverse image, neither of which needs groupoid
fibres.

Part (2) of Stacks 06WX, the same statement for sheaves of modules, is not proved here, so
this tag's covering set is incomplete; see the implementation note below.

## References

* [Stacks Project, Tag 06WX](https://stacks.math.columbia.edu/tag/06WX)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v₁ v₂ w₁ w₂ t

namespace AlgebraicGeometry.Stack

/-- **Stacks 06WX, part (1).** Direct image under a fibred 1-morphism preserves injective
abelian sheaves, for any of the five associated topologies. -/
@[stacks 06WX "injective_pushforward_abelian"]
theorem abelianDirectImage_preservesInjectiveObjects
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v₁} [Category.{w₁} 𝒳]
    {𝒴 : Type v₂} [Category.{w₂} 𝒴]
    {p𝒳 : 𝒳 ⥤ BigFppfOver B S hS}
    {p𝒴 : 𝒴 ⥤ BigFppfOver B S hS}
    [p𝒳.IsFibered] [p𝒴.IsFibered]
    {F : 𝒳 ⥤ 𝒴} (hF : p𝒳.IsFibredOneMorphism p𝒴 F)
    (τ : SiteKind)
    [∀ (G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}), F.op.HasPointwiseRightKanExtension G] :
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      (BigFppfOver.baseOverTopology B S hS τ)).2
    (F.sheafPushforwardCocontinuous AddCommGrpCat.{t}
      (BigFppfOver.associatedTopology B S hS p𝒳 τ)
      (BigFppfOver.associatedTopology B S hS p𝒴 τ)).PreservesInjectiveObjects := by
  let J := BigFppfOver.baseOverTopology B S hS τ
  have := (hF.isContinuous_and_isCocontinuous_inheritedTopology J).1
  have := (hF.isContinuous_and_isCocontinuous_inheritedTopology J).2
  have := hF.preservesFiniteLimits_inverseImage (J := J) (A := AddCommGrpCat.{t})
  have := preservesMonomorphisms_of_preservesLimitsOfShape
    (F.sheafPushforwardContinuous AddCommGrpCat.{t} (p𝒳.inheritedTopology J)
      (p𝒴.inheritedTopology J))
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (hF.sheafAdjunctionInheritedTopology J AddCommGrpCat.{t})

end AlgebraicGeometry.Stack

end
