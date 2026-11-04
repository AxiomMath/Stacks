module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Fibre products of algebraic spaces, and étaleness of isomorphisms

The algebraic spaces over `S` form a full subcategory of the presheaves on the big fppf site
of `S` which is closed under isomorphism and under fibre products, so its inclusion creates —
hence preserves — fibre products. This is what transports a cartesian square of algebraic
spaces to the cartesian square of the presheaves underlying it, which is how the permanence
properties of étaleness are read off the big site.

An isomorphism of presheaves on the big fppf site is étale, with no algebraicity hypothesis on
either side.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_isClosedUnderIsomorphisms` and
  `AlgebraicGeometry.isAlgebraicSpace_isClosedUnderLimitsOfShape_walkingCospan`: being an
  algebraic space over `S` is invariant under isomorphism of presheaves and is inherited by a
  fibre product of presheaves.
* `AlgebraicGeometry.AlgebraicSpaces.instCreatesPullbacksι`: the inclusion of the algebraic
  spaces over `S` into all presheaves on the big fppf site of `S` creates fibre products.
* `AlgebraicGeometry.Space.isEtale_of_isIso`: an isomorphism of presheaves on the big fppf site
  of `S` is étale.

## Implementation notes

The two closure instances are the hypotheses of
`CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion`: being an algebraic space
is invariant under isomorphism by `AlgebraicGeometry.IsAlgebraicSpace.of_iso` and is inherited
by a presheaf fibre product by `AlgebraicGeometry.isAlgebraicSpace_pullback`.

`AlgebraicGeometry.Space.isEtale_of_isIso` needs neither side to be an algebraic space:
étaleness of a morphism of presheaves asks that its composite with every representable étale
chart be étale, and precomposing such a chart with an isomorphism leaves it one, because the
relatively representable étale property respects isomorphisms.

Permanence of étaleness itself — stability under base change (Stacks 03FU) and étaleness of a
morphism between two algebraic spaces étale over a third (Stacks 03FV) — is
`AlgebraicGeometry.Space.isEtale_of_isPullback` and
`AlgebraicGeometry.Space.isEtale_of_isEtale_over` in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms`, where they are proved alongside the
chart criteria of Stacks 03FS that they rest on.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cartesian squares of algebraic spaces and of the presheaves underlying them -/

/-- Being an algebraic space over `S` is invariant under isomorphism of presheaves. -/
instance isAlgebraicSpace_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) where
  of_iso e h := h.of_iso e

/-- The algebraic spaces over `S` are closed under fibre products inside all presheaves on the
big fppf site of `S`. -/
instance isAlgebraicSpace_isClosedUnderLimitsOfShape_walkingCospan :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) WalkingCospan := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨D, hD⟩
  exact (isAlgebraicSpace_pullback B S hS (D.map WalkingCospan.Hom.inl)
    (D.map WalkingCospan.Hom.inr) (hD WalkingCospan.left) (hD WalkingCospan.right)
    (hD WalkingCospan.one)).of_iso (HasLimit.isoOfNatIso (diagramIsoCospan D)).symm

namespace AlgebraicSpaces

/-- The inclusion of the algebraic spaces over `S` into all presheaves on the big fppf site of
`S` creates fibre products. -/
noncomputable instance instCreatesPullbacksι :
    CreatesLimitsOfShape WalkingCospan (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) :=
  inferInstance

end AlgebraicSpaces

namespace Space

/-- An isomorphism of presheaves on the big fppf site of `S` is étale: precomposing an étale
chart with an isomorphism leaves it an étale chart. -/
theorem isEtale_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [IsIso f] :
    IsEtale B S hS f :=
  fun _ φ hφ ↦ MorphismProperty.RespectsIso.postcomp _ f φ hφ

end Space

end AlgebraicGeometry

end
