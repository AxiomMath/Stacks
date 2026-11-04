module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.Subcanonical

/-!
# Cartesian squares of quotient sheaves on the five big sites

Let `j : R ⟶ U ×_S U` and `j' : R' ⟶ U' ×_S U'` be equivalence relations over `S` and let
`(r, f)` be a morphism from `j` to `j'` whose square on source maps is cartesian. Then `U` is
the fibre product of `U'` and `U/R` over `U'/R'` as sheaves for each of the Zariski, étale,
smooth, syntomic and fppf topologies.

`Stacks.Groupoids.isPullback_toQuotientSheaf` proves this for an arbitrary topology on an
arbitrary presenting site, but only under the hypothesis that the restricted functors of
points of `U` and of `U'` are sheaves. On a subcanonical site that hypothesis is a theorem as
soon as `U` and `U'` come from objects of the site, because the restricted functor of points
of the scheme presented by an object is then the presheaf represented by that object. Each of
the five big sites of `AlgebraicGeometry.BigSite` is subcanonical, so the hypothesis is
discharged there and the five instances of the source statement are unconditional.

## Main results

* `Stacks.Groupoids.isPullback_toQuotientSheaf_of_subcanonical` discharges the two sheaf
  hypotheses of `Stacks.Groupoids.isPullback_toQuotientSheaf` over any subcanonical topology
  on a site presented by a fully faithful functor.
* `AlgebraicGeometry.isPullback_toQuotientSheaf_overTopology` is the resulting statement on
  the localization at `S` of a big site of any of the five topologies.

## Implementation notes

The five topologies are handled in one declaration rather than five, by quantifying over
`AlgebraicGeometry.CoveringTopology`: `AlgebraicGeometry.BigSite` dispatches on it to the five
big-site structures and `AlgebraicGeometry.overTopology` to the five localized topologies, so
the quantified statement is exactly the "for each `τ`" of the source.

The scheme of relations `R` is an arbitrary scheme over `S`, not required to be an object of
the site: only the functors of points of `U` and of `U'` enter the square, so only those two
need the sheaf condition.

## References

* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{u} C]

/-- A cartesian square on the source maps of two equivalence relations induces a cartesian
square on their quotient sheaves, for a subcanonical topology on a site of `S`-schemes
presented by a fully faithful functor and for relations on the schemes presented by two
objects of the site.

This is `Stacks.Groupoids.isPullback_toQuotientSheaf` with its two sheaf hypotheses
discharged: on a subcanonical site the restricted functor of points of the scheme presented
by an object of the site is the presheaf represented by that object, which is a sheaf. -/
theorem isPullback_toQuotientSheaf_of_subcanonical (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [J.Subcanonical] (F : C ⥤ Over S) [F.Full] [F.Faithful]
    {R R' : Over S} {X X' : C} (j : PreRelation R (F.obj X)) (j' : PreRelation R' (F.obj X'))
    [IsEquivalenceRelation j.target j.source] [IsEquivalenceRelation j'.target j'.source]
    (r : R ⟶ R') (f : F.obj X ⟶ F.obj X')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    (hcart : IsPullback r j.source j'.source f) :
    IsPullback (toQuotientSheaf J F j) (F.op.whiskerLeft (yoneda.map f))
      (quotientSheafMap J F j j' r f hs ht).hom (toQuotientSheaf J F j') :=
  isPullback_toQuotientSheaf J F j j' r f hs ht hcart
    (isSheaf_points_obj J F X) (isSheaf_points_obj J F X')

end Stacks.Groupoids

namespace AlgebraicGeometry

open Stacks.Groupoids

/-- The functor presenting a localized big site as a site of `S`-schemes is faithful: it is
`Over.post` of the inclusion of a full subcategory of schemes. -/
instance faithful_overToSlice (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
    (hS : S.size < cutoff τ B) : (overToSlice τ B S hS).Faithful :=
  inferInstanceAs (CategoryTheory.Over.post
    (X := base B S hS) (schemeBelowInclusion (cutoff τ B))).Faithful

/-- The functor presenting a localized big site as a site of `S`-schemes is full: it is
`Over.post` of the inclusion of a full subcategory of schemes. -/
instance full_overToSlice (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
    (hS : S.size < cutoff τ B) : (overToSlice τ B S hS).Full :=
  inferInstanceAs (CategoryTheory.Over.post
    (X := base B S hS) (schemeBelowInclusion (cutoff τ B))).Full

/-- Set-valued presheaves on the localization at `S` of a big site can be sheafified: the
underlying category of a big site is essentially small, and so is its slice. -/
instance hasSheafify_overTopology_type (τ : CoveringTopology) (B : BigSite.{u} τ)
    (S : Scheme.{u}) (hS : S.size < cutoff τ B) :
    HasSheafify (overTopology τ B S hS) (Type u) :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- **Stacks 07S3.** Let `S` be a scheme and let `(r, f)` be a morphism of equivalence
relations `j : R ⟶ U ×_S U` and `j' : R' ⟶ U' ×_S U'` over `S` whose square on source maps is
cartesian. Then for each of the Zariski, étale, smooth, syntomic and fppf topologies the
square formed by the two quotient maps and by `f` is a fibre product square of `τ`-sheaves:
`U` is the fibre product of `U'` and `U/R` over `U'/R'`.

The topology is quantified over `AlgebraicGeometry.CoveringTopology`, so the single statement
is the five of the source. The two schemes of objects `U` and `U'` are the schemes presented
by objects of the site; the two schemes of relations are arbitrary schemes over `S`. -/
@[stacks 07S3]
theorem isPullback_toQuotientSheaf_overTopology (τ : CoveringTopology) (B : BigSite.{u} τ)
    (S : Scheme.{u}) (hS : S.size < cutoff τ B)
    {R R' : CategoryTheory.Over S} {U U' : CategoryTheory.Over (base B S hS)}
    (j : PreRelation R ((overToSlice τ B S hS).obj U))
    (j' : PreRelation R' ((overToSlice τ B S hS).obj U'))
    [IsEquivalenceRelation j.target j.source] [IsEquivalenceRelation j'.target j'.source]
    (r : R ⟶ R')
    (f : (overToSlice τ B S hS).obj U ⟶ (overToSlice τ B S hS).obj U')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    (hcart : IsPullback r j.source j'.source f) :
    IsPullback (toQuotientSheaf (overTopology τ B S hS) (overToSlice τ B S hS) j)
      ((overToSlice τ B S hS).op.whiskerLeft (yoneda.map f))
      (quotientSheafMap (overTopology τ B S hS) (overToSlice τ B S hS) j j' r f hs ht).hom
      (toQuotientSheaf (overTopology τ B S hS) (overToSlice τ B S hS) j') :=
  isPullback_toQuotientSheaf_of_subcanonical (overTopology τ B S hS) (overToSlice τ B S hS)
    j j' r f hs ht hcart

end AlgebraicGeometry

end
