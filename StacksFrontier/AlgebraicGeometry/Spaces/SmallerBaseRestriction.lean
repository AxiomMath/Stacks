module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# The structural morphism of Stacks 04SG is the relocalization's own (Stacks 04SG)

Let `g : S ⟶ S'` be a morphism of a big fppf site. The forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG carries an algebraic space `F`
over `S` to an algebraic space over `S'` *together with* a morphism to the representable
algebraic space of `S`. Forgetting that morphism identifies the image with the lower-shriek
extension `Λ_g F` of Stacks 03I5 part (2)
(`AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso`). This file records that under that
identification the structural morphism *is* the relocalization's own structural morphism
`CategoryTheory.OverShriek.relocalizeToYoneda`, which reads off the factorization through `S`
that a section of `Λ_g F` carries.

That is what connects `AlgebraicGeometry.algebraicSpaceMap` — the morphism of algebraic spaces
over `S'` that the relative-property statements of Stacks 03YK and Stacks 026O are about — to
`CategoryTheory.OverShriek.isPullback_relocalizeRestrictMap`, which exhibits the relocalization
of a restriction as a base change of `Λ_g F` along a representable morphism, and so is the
locality step of any argument of the shape "the property holds after restriction to each member
of a covering of `S` by schemes, hence it holds over `S`".

## Main results

* `AlgebraicGeometry.Space.relocalizeToYoneda_eq`: **Stacks 04SG**, the structural morphism of
  the image of `F` is `CategoryTheory.OverShriek.relocalizeToYoneda`.

## Implementation notes

This is a restatement of the pointwise computation
`AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app` as an equality of
morphisms of presheaves, which is the form a consumer needs in order to transport a pullback
square along `AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso`.

The *restriction* of an algebraic space over `S` to a smaller base is an algebraic space again —
Stacks 03I5 part (1), `AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict` in
`StacksFrontier/AlgebraicGeometry/Spaces/RestrictSmallerBase.lean` — but this file does not use
it: only the forward direction of Stacks 04SG is used here, so the base-change
statement is read with `CategoryTheory.OverShriek.relocalizeToYoneda` rather than
`AlgebraicGeometry.algebraicSpaceMap` on the restricted leg.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 04SG.** Under the identification of the image of `F` with the lower-shriek
extension `Λ_g F`, the structural morphism to the representable algebraic space of `S` is the
relocalization's own structural morphism: it sends the section of `Λ_g F` indexed by a
factorization `ψ : T ⟶ S` to `ψ`. -/
theorem relocalizeToYoneda_eq (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (F : AlgebraicSpaces B S hS) :
    (spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g).inv.app F ≫
        ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.hom =
      OverShriek.relocalizeToYoneda g F.1 := by
  ext W s
  exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B S S' hS hS' g F W s

end AlgebraicGeometry.Space

end
