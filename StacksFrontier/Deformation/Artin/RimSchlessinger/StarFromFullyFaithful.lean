module

public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonFullyFaithfulStack
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts

/-!
# What condition (RS*) still needs: essential surjectivity, and nothing else

**This file does not prove condition (RS*).** It records what is left of it once the
fully-faithful half of the comparison is available, in the same hypothesis-carrying shape as
`StacksFrontier/Deformation/Artin/RimSchlessinger/FromThickeningPushouts.lean`: the hypothesis is the
content, and here the hypothesis is *essential surjectivity* of
`Deformation.Artin.fiberSquareComparison` at the squares condition (RS*) quantifies over.

Full faithfulness at those squares is
`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal_of_isAffine`,
which needs only that the category fibred in groupoids have a representable diagonal. So the one
remaining gap between a representable diagonal and condition (RS*) of
[Stacks Project, Tag 07Y8] is essential surjectivity, which is what this file makes visible: it
is the *only* hypothesis below.

## Main results

* `Deformation.Artin.satisfiesRSStar_of_hasRepresentableDiagonal_of_essSurj` — condition (RS*)
  from a representable diagonal together with essential surjectivity at the squares (RS*)
  quantifies over.

## Implementation notes

No tag is claimed, and none would be honest: [Stacks Project, Tag 0CXP] and
[Stacks Project, Tag 07WN] assert that the comparison is an equivalence, and the essential
surjectivity half is assumed here, not proved. It is genuinely open in this repository: it needs
the infinitesimal lifting property of a smooth morphism into an algebraic space over an affine
base, which is interderivable with the unproved `hGlue` of
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmoothChartBiconditional.lean`.

The hypothesis asks for essential surjectivity at a *narrower* class of squares than the
fully-faithful half is proved for: affine source and target for the affine leg, and a thickening
of first order. That is exactly the class
`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair`
supplies, so nothing is asked for that condition (RS*) does not provide. Affineness of the two
remaining corners, and the first-order thickening opposite to the one in the square, are
available there but are not used by either half.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0CXP](https://stacks.math.columbia.edu/tag/0CXP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u w

namespace Deformation.Artin

/-- **Condition (RS*) holds for a category fibred in groupoids with representable diagonal as soon
as the comparison is essentially surjective at the squares condition (RS*) quantifies over.**

The hypothesis is the content: full faithfulness at those squares is
`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal_of_isAffine`,
proved from the representable diagonal alone, and essential surjectivity — assumed here — is the
only remaining gap. No tag is claimed; in particular this is **not** [Stacks Project, Tag 0CXP],
which asserts the comparison is an equivalence outright. -/
public theorem satisfiesRSStar_of_hasRepresentableDiagonal_of_essSurj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS))
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hES :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y')
        (b : Y ⟶ Y') (w : i ≫ a = f ≫ b),
        IsAffine ((BigFppfOver.toScheme B S hS).obj X) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj Y) →
        Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          (fiberSquareComparison 𝒳.val.p (chosenPullbacks 𝒳.val.p) f i b a w.symm).EssSurj) :
    SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  refine satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair
    B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids ?_
  intro X X' Y Y' i f a b w hX _hX' hY _hY' hfirst _hfirstb hpush
  have := hES i f a b w hX hY hfirst hpush
  have := (fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal_of_isAffine
    B S hS 𝒳 hdiag i f a b w hX hY hfirst hpush).full
  have := (fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal_of_isAffine
    B S hS 𝒳 hdiag i f a b w hX hY hfirst hpush).faithful
  exact Functor.IsEquivalence.mk

end Deformation.Artin

end
