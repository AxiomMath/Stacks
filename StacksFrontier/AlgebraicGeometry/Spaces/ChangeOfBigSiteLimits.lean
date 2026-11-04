module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteSections

/-!
# Limits of algebraic spaces descend along an enlargement of the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, and write
`f⁻¹` for the inverse image along the inclusion of localized big fppf sites
(`AlgebraicGeometry.changeBigSite`, Stacks 03FP and 04W1). This file proves that a cone of
algebraic spaces over `S` for `B` is a limit cone of presheaves as soon as its image under `f⁻¹`
is a limit cone of presheaves for `B'`.

The index category is arbitrary, in any universe. In particular it may be too large for limits
of presheaves of sets to exist objectwise, so the argument cannot evaluate at a test object.
It runs through sheaves instead.

## Main results

* `AlgebraicGeometry.isLimitOfIsLimitChangeBigSite`: if the image under `f⁻¹` of a cone of
  algebraic spaces is a limit cone of presheaves on the larger site, the cone is a limit cone of
  presheaves on the smaller site.

## Implementation notes

The image cone consists of sheaves, so it is a limit cone of sheaves, the inclusion of sheaves
into presheaves being fully faithful. The direct image `f_*` is a right adjoint
(`AlgebraicGeometry.inclusionOver_sheafPushforwardContinuous_isRightAdjoint`), so it carries that
limit cone to a limit cone; since `f⁻¹` is fully faithful the unit `𝟭 ⟶ f⁻¹ ⋙ f_*` is an
isomorphism (`AlgebraicGeometry.changeBigSiteSheafUnitIso`), so the given cone is a limit cone of
sheaves on the smaller site. Finally the inclusion of sheaves into presheaves is right adjoint to
sheafification, so it preserves this limit. Each step uses adjoint functors or reflection by a
fully faithful functor, both of which work for limits of every size.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **Limits of algebraic spaces descend along an enlargement of the big fppf site.** If the image
under the inverse image `AlgebraicGeometry.changeBigSite` of a cone of algebraic spaces over `S`
is a limit cone of presheaves on the larger site, then the cone is a limit cone of presheaves on
the smaller site. The index category is arbitrary. -/
def isLimitOfIsLimitChangeBigSite {J : Type w} [Category.{w'} J]
    {D : J ⥤ AlgebraicSpaces B S hS} (c : Cone D)
    (hc : IsLimit ((ObjectProperty.ι _).mapCone ((changeBigSite B B' h S hS).mapCone c))) :
    IsLimit ((ObjectProperty.ι _).mapCone c) := by
  let JT := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  letI : i.IsContinuous JT K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  letI : (i.sheafPushforwardContinuous (Type u) JT K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  letI : HasSheafify JT (Type u) := hasSheafify_overTopology B S hS
  let toSheaf : AlgebraicSpaces B S hS ⥤ Sheaf JT (Type u) :=
    ObjectProperty.lift _ (ObjectProperty.ι _) fun X => X.property.isSheaf
  let L := i.sheafPullback (Type u) JT K
  let R := i.sheafPushforwardContinuous (Type u) JT K
  have h1 : IsLimit ((toSheaf ⋙ L).mapCone c) :=
    isLimitOfReflects (sheafToPresheaf K (Type u)) hc
  have h2 : IsLimit ((toSheaf ⋙ L ⋙ R).mapCone c) := isLimitOfPreserves R h1
  have h3 : IsLimit (toSheaf.mapCone c) :=
    IsLimit.mapConeEquiv
      (Functor.isoWhiskerLeft toSheaf (changeBigSiteSheafUnitIso B B' h S hS).symm ≪≫
        toSheaf.rightUnitor) h2
  exact isLimitOfPreserves (sheafToPresheaf JT (Type u)) h3

end AlgebraicGeometry

end
