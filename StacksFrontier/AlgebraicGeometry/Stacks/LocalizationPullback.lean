module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# Pullback of a presheaf to the site of an object (Stacks 06W1)

Let `p : 𝒳 ⥤ BigFppfOver B S hS` be a category fibred in groupoids and let `x` be an object of
`𝒳`, lying over a scheme `U`. The canonical localization functor `CategoryTheory.Over.post` of
Stacks 06W0 is an equivalence from the slice `Over x` to the schemes over `U`, so a presheaf on
`𝒳` pulls back to a presheaf on the big fppf site of `U`: restrict along `Over.forget x`, then
transport along a chosen quasi-inverse of that equivalence.

Restricting further to the small étale site of `U` is literal precomposition with the small
étale inclusion, provided the étale and fppf sites share a size cutoff — the cutoffs then
define the same bounded category of schemes, and the change of bounded category is
`CategoryTheory.ObjectProperty.ιOfLE`. The two sites may still select different covering
families; only their underlying categories are identified here.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleInclusion`: the small étale site of a scheme, included into
  the slice of a big fppf site with the same cutoff.
* `AlgebraicGeometry.Stack.presheafPullback`: the pullback of a presheaf on `𝒳` to the big fppf
  site of the scheme underlying an object `x`.
* `AlgebraicGeometry.Stack.restrictToSmallEtale`: its restriction to the small étale site of that
  scheme.

## References

* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w t s

namespace AlgebraicGeometry.Stack

/-- The small étale site of a scheme `U`, regarded as landing in the slice at `U` of a big fppf
site with the same size cutoff. The two cutoffs agree, so the bounded categories of schemes
coincide and the change of category is `CategoryTheory.ObjectProperty.ιOfLE`. -/
@[implicit_reducible] def smallEtaleInclusion
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (U : Scheme.{u}) (hU : E.Contains U) :
    SmallEtale E U hU ⥤ Over (B.obj (show B.Contains U from by simpa [h] using hU)) :=
  SmallEtale.inclusion E U hU ⋙ Over.post (ObjectProperty.ιOfLE
    (P := schemeSizeBelow E.cutoff) (P' := schemeSizeBelow B.cutoff)
    (by intro X hX; simpa [h] using hX))

/-- The small étale inclusion is faithful, since both of its factors are. -/
instance smallEtaleInclusion_faithful
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (U : Scheme.{u}) (hU : E.Contains U) :
    (smallEtaleInclusion B E h U hU).Faithful := by
  let F : E.Scheme ⥤ B.Schemes := ObjectProperty.ιOfLE
    (P := schemeSizeBelow E.cutoff) (P' := schemeSizeBelow B.cutoff)
    (by intro X hX; simpa [h] using hX)
  let : F.Faithful := ObjectProperty.faithful_ιOfLE _
  unfold smallEtaleInclusion
  change (SmallEtale.inclusion E U hU ⋙ Over.post F).Faithful
  infer_instance

/-- Every object of the small étale site of `U` is étale over `U` after inclusion into the big
fppf slice, because the inclusion does not change the structure morphism. -/
instance smallEtaleInclusion_etale
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (U : Scheme.{u}) (hU : E.Contains U) (X : SmallEtale E U hU) :
    Etale (B.inclusion.map ((smallEtaleInclusion B E h U hU).obj X).hom) := by
  change Etale (E.inclusion.map X.obj.hom)
  infer_instance

/-- The pullback of a presheaf on a category fibred in groupoids to
the big fppf site of the scheme underlying an object `x`: restrict to the slice at `x`, then
transport across the localization equivalence of Stacks 06W0. -/
@[stacks 06W1 "part (1)"]
noncomputable abbrev presheafPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A) :
    (Over (p.obj x).left)ᵒᵖ ⥤ A :=
  letI := isEquivalence_overPost B S hS p hp x
  (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.op ⋙ (Over.forget x).op ⋙ F

/-- The restriction of the pulled-back presheaf to the small étale
site of the same scheme, for an étale site with the same size cutoff. -/
@[stacks 06W1 "part (2)"]
noncomputable abbrev restrictToSmallEtale
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A) :
    (SmallEtale E (p.obj x).left.1
      (show E.Contains (p.obj x).left.1 from by simpa [h] using (p.obj x).left.2))ᵒᵖ ⥤ A :=
  (smallEtaleInclusion B E h (p.obj x).left.1
    (show E.Contains (p.obj x).left.1 from by simpa [h] using (p.obj x).left.2)).op ⋙
      presheafPullback B S hS p hp x F

end AlgebraicGeometry.Stack

end
