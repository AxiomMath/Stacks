module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal

/-!
# Deligne–Mumford morphisms of algebraic stacks (Stacks 04YW)

Following Stacks 04YW, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is
*Deligne–Mumford*, or *DM*, when its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is
representable by algebraic spaces and unramified.

## Main definitions

* `AlgebraicGeometry.Stack.IsDM`: **Stacks 04YW**, the DM condition.

## Implementation notes

The relative diagonal is `AlgebraicGeometry.Stack.relativeDiagonal`, into the
canonical 2-fibre product `AlgebraicGeometry.Stack.twoFibreProduct` of `f` with itself, so the
notion does not depend on a chosen fibre-product construction. Representability by algebraic
spaces of the diagonal is part of the predicate rather than a separate argument, as in the
source, which is why the condition is an existential over it: the unramifiedness clause needs a
representability witness to be stated at all, and the witness is unique as a proposition.

Unramifiedness is the relative property of **Stacks 03YK** at
`AlgebraicGeometry.Space.IsUnramified` (**Stacks 03ZH**, part (1)). It is written out **longhand**
rather than through `AlgebraicGeometry.Stack.HasRelativeProperty`: that abbreviation carries
`[P.IsStableUnderBaseChange]` and
`[P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]` as instance arguments which it
does not use in its body — its own docstring says so — so the longhand quantifier is *the same
proposition* with no hypothesis on the property at all, and that is what this definition should
be. (Both instances are available for unramifiedness: base-change stability is
**Stacks 03ZJ**, proved as
`AlgebraicGeometry.Space.isUnramified_isStableUnderBaseChange`, and the fppf locality follows
from the fpqc form `AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc` by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`. The longhand spelling is used because it
needs neither.) That
equality is machine-checked, quantified over the two instances; a consumer written against the
`HasRelativeProperty` form of Tag 04YW's `IsDM` therefore unifies with this on the nose.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04YW, the DM condition.** A 1-morphism of algebraic stacks over `S` is
*Deligne–Mumford* when its relative diagonal is representable by algebraic spaces and
unramified, the latter in the relative sense of Stacks 03YK: every algebraic space representing
a base change of the diagonal along a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has unramified
structural morphism. -/
@[stacks 04YW "dm"]
abbrev IsDM {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  let T := twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1} B S hS
    𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom
  let Δ := relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom
  ∃ _hΔ : IsRepresentableByAlgebraicSpaces B S hS Δ.hom,
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ T.val.obj)
      (_hy : y ⋙ T.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p T.val.p y
          (CatFiberedInGroupoids.homFunctor Δ))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsUnramified B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end AlgebraicGeometry.Stack

end
