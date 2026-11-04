module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf

/-!
# Fibre products of affine étale charts of an algebraic space

The affine étale site of a presheaf `F` on the big fppf site of `S` has fibre products, and they
are computed on the underlying schemes. Every morphism of affine étale charts is étale, hence
flat, on the underlying schemes.

## Main results

* `AlgebraicGeometry.Space.isAffineChart_isClosedUnderLimitsOfShape_walkingCospan`: the affine
  charts are closed under fibre products of étale charts.
* `AlgebraicGeometry.Space.AffineEtale.instHasPullbacks`: **the affine étale site has fibre
  products.**
* `AlgebraicGeometry.Space.AffineEtale.instPreservesPullbacksToScheme`: they are computed on the
  underlying schemes.
* `AlgebraicGeometry.Space.AffineEtale.etale_toScheme_map` and
  `AlgebraicGeometry.Space.AffineEtale.flat_toScheme_map`: a morphism of affine étale charts is
  étale, hence flat, on the underlying schemes.

## Implementation notes

The affine charts form a full subcategory of the étale charts cut out by an object property, and
the fibre products are *created* by that inclusion: a cone in the subcategory is a limit cone
exactly when it is one in the étale charts, and the limit formed there satisfies the affineness
condition by `AlgebraicGeometry.IsAffine.of_isPullback`.  No hypothesis that `F` is an algebraic
space is needed, because the fibre products of the small étale site are already available
unconditionally.

## References

* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The scheme underlying an étale chart of `F` is a fibre product of the underlying schemes of
a cospan of étale charts whenever the chart is their fibre product. -/
instance preservesPullbacks_smallEtaleToScheme :
    PreservesLimitsOfShape WalkingCospan
      (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS) := by
  apply comp_preservesLimitsOfShape

/-- Being an affine chart of `F` is invariant under isomorphism of étale charts, because an
isomorphism of étale charts is an isomorphism of the underlying schemes. -/
instance isAffineChart_isClosedUnderIsomorphisms :
    (IsAffineChart B S hS F).IsClosedUnderIsomorphisms :=
  ⟨fun {X Y} e hX => by
    let H := SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS
    let _ : IsAffine (H.obj X) := hX
    exact IsAffine.of_isIso (H.map e.inv)⟩

/-- A fibre product of two affine étale charts of `F`, formed in the étale charts, is again an
affine chart: it is computed on the underlying schemes, and a fibre product of affine schemes is
affine. -/
instance isAffineChart_isClosedUnderLimitsOfShape_walkingCospan :
    (IsAffineChart B S hS F).IsClosedUnderLimitsOfShape WalkingCospan := by
  let H := SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro X ⟨D, hD⟩
  let _ : IsAffine (H.obj (D.obj WalkingCospan.left)) := hD _
  let _ : IsAffine (H.obj (D.obj WalkingCospan.right)) := hD _
  let _ : IsAffine (H.obj (D.obj WalkingCospan.one)) := hD _
  have hpb : IsPullback (H.map (limit.π D WalkingCospan.left))
      (H.map (limit.π D WalkingCospan.right))
      (H.map (D.map WalkingCospan.Hom.inl))
      (H.map (D.map WalkingCospan.Hom.inr)) :=
    IsPullback.of_isLimit_cone (isLimitOfPreserves H (limit.isLimit D))
  exact IsAffine.of_isPullback hpb

namespace AffineEtale

/-- **The affine étale site of `F` has fibre products.** -/
instance instHasPullbacks : HasPullbacks (AffineEtale B S hS F) :=
  inferInstanceAs (HasPullbacks (IsAffineChart B S hS F).FullSubcategory)

/-- The fibre products of the affine étale site are the fibre products of the underlying
schemes. -/
instance instPreservesPullbacksToScheme :
    PreservesLimitsOfShape WalkingCospan (toScheme B S hS F) := by
  change PreservesLimitsOfShape WalkingCospan
    (inclusion B S hS F ⋙ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS))
  apply comp_preservesLimitsOfShape

/-- The underlying morphism of schemes of a morphism of affine étale charts is étale. -/
theorem etale_toScheme_map {U V : AffineEtale B S hS F} (f : U ⟶ V) :
    Etale ((toScheme B S hS F).map f) :=
  etale_toScheme_toOver_map B S hS F ((inclusion B S hS F).map f)

/-- The underlying morphism of schemes of a morphism of affine étale charts is flat, an étale
morphism of schemes being flat. -/
theorem flat_toScheme_map {U V : AffineEtale B S hS F} (f : U ⟶ V) :
    Flat ((toScheme B S hS F).map f) :=
  (Etale.iff_flat_and_formallyUnramified.mp (etale_toScheme_map B S hS F f)).1

end AffineEtale

end AlgebraicGeometry.Space

end
