module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationConstructionA

/-!
# Change of base and a 2-fibre product along two independent legs

Construction A of **Stacks 04X5** views a category fibred in groupoids over the big fppf category
of `S` as one over the big fppf category of `S'`, along a morphism `g : S ⟶ S'` of the site; on
structure functors it is post-composition with `CategoryTheory.Over.map g`. This file records that
it does not change a 2-fibre product, for two *independent* 1-morphisms into the common target.

`AlgebraicGeometry.Stack.changeBaseSelfProductHom` is the special case of the self-product of one
1-morphism `(f, f)`. The comparison functors are
`CategoryTheory.TwoFibreProductOver.relocalizeBase` and
`CategoryTheory.TwoFibreProductOver.unrelocalizeBase`, with equivalence
`CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence`.

## Main definitions

* `AlgebraicGeometry.Stack.changeBaseTwoFibreProductHom`: the comparison from Construction A of a
  2-fibre product to the 2-fibre product of Construction A of its data, a 1-morphism over the big
  fppf category of `S'`.
* `AlgebraicGeometry.Stack.changeBaseTwoFibreProductInv`: the comparison in the other direction.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_changeBaseTwoFibreProductHom` and
  `AlgebraicGeometry.Stack.isEquivalence_changeBaseTwoFibreProductInv`: both comparisons are
  equivalences of categories.

## Implementation notes

The two directions are stated separately, rather than one as the inverse of the other, for the
reason `AlgebraicGeometry.Stack.changeBaseSelfProductHom` and
`AlgebraicGeometry.Stack.changeBaseSelfProductInv` are: the underlying comparison is an
isomorphism of categories, so reading it backwards exchanges the two functors and the two inverse
identities and nothing has to be inverted.

Both hypotheses that
`CategoryTheory.TwoFibreProductOver.unrelocalizeBase` needs — that each leg is strictly over the
base — are the `w` fields of the two based functors, so they are available on the nose and are not
hypotheses of anything here.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (𝒯₁ : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS))
  (𝒯₂ : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))

/-- **Construction A of a 2-fibre product is the 2-fibre product of Construction A of its data**,
forward direction, for two independent legs `x` and `y` into the common target `𝒳`. The functor is
`CategoryTheory.TwoFibreProductOver.relocalizeBase`, which is strictly over the big fppf category
of `S'`. -/
def changeBaseTwoFibreProductHom (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val) :
    (changeBaseFiberedInGroupoids B S S' hS hS' g
        (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y)).val ⥤ᵇ
      (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒯₁)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒯₂)
        (changeBaseFunctor B S S' hS hS' g x)
        (changeBaseFunctor B S S' hS hS' g y)).val where
  toFunctor := TwoFibreProductOver.relocalizeBase g
  w := TwoFibreProductOver.relocalizeBase_comp_structureFunctor g

/-- The comparison of `AlgebraicGeometry.Stack.changeBaseTwoFibreProductHom` in the other
direction, `CategoryTheory.TwoFibreProductOver.unrelocalizeBase`. The two hypotheses it needs are
the commutations of the two legs with the structure functors. -/
def changeBaseTwoFibreProductInv (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val) :
    (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒯₁)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒯₂)
        (changeBaseFunctor B S S' hS hS' g x)
        (changeBaseFunctor B S S' hS hS' g y)).val ⥤ᵇ
      (changeBaseFiberedInGroupoids B S S' hS hS' g
        (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y)).val where
  toFunctor := TwoFibreProductOver.unrelocalizeBase g x.w y.w
  w := TwoFibreProductOver.unrelocalizeBase_comp_structureFunctor g x.w y.w

/-- The comparison `AlgebraicGeometry.Stack.changeBaseTwoFibreProductHom` is an equivalence of
categories. -/
instance isEquivalence_changeBaseTwoFibreProductHom (x : 𝒯₁.val ⥤ᵇ 𝒳.val)
    (y : 𝒯₂.val ⥤ᵇ 𝒳.val) :
    Functor.IsEquivalence
      (changeBaseTwoFibreProductHom B S S' hS hS' g 𝒳 𝒯₁ 𝒯₂ x y).toFunctor :=
  (TwoFibreProductOver.relocalizeBaseEquivalence g x.w y.w).isEquivalence_functor

/-- The comparison `AlgebraicGeometry.Stack.changeBaseTwoFibreProductInv` is an equivalence of
categories. -/
instance isEquivalence_changeBaseTwoFibreProductInv (x : 𝒯₁.val ⥤ᵇ 𝒳.val)
    (y : 𝒯₂.val ⥤ᵇ 𝒳.val) :
    Functor.IsEquivalence
      (changeBaseTwoFibreProductInv B S S' hS hS' g 𝒳 𝒯₁ 𝒯₂ x y).toFunctor :=
  (TwoFibreProductOver.relocalizeBaseEquivalence g x.w y.w).isEquivalence_inverse

end AlgebraicGeometry.Stack

end
