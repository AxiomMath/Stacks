module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EquivalenceOfSites

/-!
# The affine étale site is invariant under isomorphism of the base presheaf

Let `B` be a big fppf site containing a scheme `S`, and let `e : F ≅ G` be an isomorphism of
presheaves on the big fppf site of `S`. Composition with `e` carries an étale chart of `F` to an
étale chart of `G` with the same source (`AlgebraicGeometry.Space.SmallEtale.congr`), hence an
affine chart to an affine chart, and this equivalence of small étale sites restricts to an
equivalence of affine étale sites, which is an isomorphism of sites.

## Main definitions

* `AlgebraicGeometry.Space.AffineEtale.congr`: the equivalence
  `AffineEtale B S hS F ≌ AffineEtale B S hS G` induced by `e : F ≅ G`.

## Main results

* `AlgebraicGeometry.Space.isAffineChart_inverseImage_congr`: a chart of `F` is affine exactly when
  its image under `AlgebraicGeometry.Space.SmallEtale.congr` is affine.
* `AlgebraicGeometry.Space.AffineEtale.congr_functor_comp_inclusion` and
  `AlgebraicGeometry.Space.AffineEtale.congr_inverse_comp_inclusion`: the equivalence of affine
  étale sites is the restriction of the equivalence of small étale sites.
* `AlgebraicGeometry.Space.AffineEtale.congr_functor_comp_toScheme` and
  `AlgebraicGeometry.Space.AffineEtale.congr_inverse_comp_toScheme`: the equivalence does not
  change the scheme underlying an affine chart.
* `AlgebraicGeometry.Space.AffineEtale.congr_isIsoOfSites`: the equivalence is an isomorphism of
  sites, carrying affine étale coverings to affine étale coverings in both directions.

## References

* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)

/-- The affine charts of `F` are exactly the charts whose image under the equivalence of small
étale sites is an affine chart of `G`. -/
theorem isAffineChart_inverseImage_congr :
    (IsAffineChart B S hS G).inverseImage (SmallEtale.congr B S hS e).functor =
      IsAffineChart B S hS F := rfl

namespace AffineEtale

/-- An isomorphism `e : F ≅ G` of presheaves on the big fppf site of `S` induces an equivalence of
affine étale sites, by composing the structure morphism of an affine chart with `e`. -/
def congr : AffineEtale B S hS F ≌ AffineEtale B S hS G :=
  Equivalence.congrFullSubcategory (SmallEtale.congr B S hS e)
    (isAffineChart_inverseImage_congr B S hS e)

/-- The equivalence of affine étale sites is the restriction of the equivalence of small étale
sites: it does not change the étale chart underlying an affine chart. -/
theorem congr_functor_comp_inclusion :
    (congr B S hS e).functor ⋙ inclusion B S hS G =
      inclusion B S hS F ⋙ (SmallEtale.congr B S hS e).functor :=
  Equivalence.congrFullSubcategory_functor_comp_ι _ _

/-- The inverse equivalence of affine étale sites is the restriction of the inverse equivalence of
small étale sites. -/
theorem congr_inverse_comp_inclusion :
    (congr B S hS e).inverse ⋙ inclusion B S hS F =
      inclusion B S hS G ⋙ (SmallEtale.congr B S hS e).inverse :=
  Equivalence.congrFullSubcategory_inverse_comp_ι _ _

/-- The equivalence of affine étale sites does not change the scheme underlying a chart. -/
theorem congr_functor_comp_toScheme :
    (congr B S hS e).functor ⋙ toScheme B S hS G = toScheme B S hS F :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The inverse equivalence does not change the scheme underlying a chart. -/
theorem congr_inverse_comp_toScheme :
    (congr B S hS e).inverse ⋙ toScheme B S hS F = toScheme B S hS G :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The equivalence of affine étale sites induced by `e : F ≅ G` is an isomorphism of sites: each
of its halves carries a covering family of affine charts to a covering family of affine charts. -/
theorem congr_isIsoOfSites :
    (congr B S hS e).IsIsoOfSites (topology B S hS F) (topology B S hS G) :=
  Equivalence.isIsoOfSites_of_isCovering _ (precoverage B S hS F) (precoverage B S hS G)
    (IsCovering B S hS F) (IsCovering B S hS G) (fun _ _ => mem_precoverage_iff B S hS F)
    (fun _ _ => mem_precoverage_iff B S hS G) (fun _ _ h => h) (fun _ _ h => h)

end AffineEtale

end AlgebraicGeometry.Space

end
