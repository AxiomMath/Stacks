module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CohenMacaulayReachMap
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.RestrictionComposition
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.PointsLocallySurjective

/-!
# Refining an equivalence relation to one with locally quasi-finite structure maps, on the big
fppf site

Stacks 0489 says that an equivalence relation `j : R ⟶ U ×_S U` on schemes over `S` whose source
and target are flat and locally of finite presentation can be *refined*: there is an equivalence
relation `j' : R' ⟶ U' ×_S U'` whose source and target are in addition locally quasi-finite,
together with a morphism `U' ⟶ U` carrying `R'` into `R` which induces an isomorphism
`U'/R' ⟶ U/R` of quotient sheaves.

This file proves that statement with no assumed input, for the quotient sheaves on the big fppf
site over `S`.

The refinement is the two-stage one of the source proof, which is
`AlgebraicGeometry.GroupoidScheme.exists_cohenMacaulay_and_quasiFinite_refinement`: Step 1 is the
inclusion `g₁ : U₁ ⟶ U` of the open over which the source map is Cohen-Macaulay (Stacks 0460),
whose reach map — the morphism `U₁ ×_{g₁, U, t} R ⟶ U` sending an arrow whose target lifts along
`g₁` to its source — is flat, locally of finite presentation and surjective; Steps 2 and 3 give,
for the restricted groupoid on `U₁`, a morphism `g' : U' ⟶ U₁` whose reach map is in addition
locally quasi-finite and surjective, namely the disjoint union of the affine slices of
Stacks 04N0 over the finite type points of `U₁`.  The refined equivalence relation `R'` is the
restriction along `g'` of the restriction along `g₁`, and the morphism `U' ⟶ U` of the tag is the
composite.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_locallyQuasiFinite_refinement_isIso_quotientMap`:
  **Stacks 0489**, unconditionally.

## Implementation notes

Two things make the statement unconditional here which the site-indexed statement
`Stacks.Groupoids.GroupoidScheme.exists_restriction_locallyQuasiFinite_isIso_quotientMap` has to
assume, and both are bought by the two choices made here: the concrete site, and the two-stage
shape.

The first is the covering datum.  On an arbitrary site presented by a functor `F : C ⥤ Over S`
there is no reason for a flat, locally finitely presented and surjective morphism of `Over S` to
be a covering of the site, or even for its source to be an object of the site, so the
site-indexed statement carries the singleton covering as data, in the convention of Stacks 04SK
and Stacks 02WQ.  On the big fppf site over `S` the datum is not needed at all:
`AlgebraicGeometry.isLocallySurjective_points_map_of_fppf` turns any flat, locally finitely
presented, surjective morphism of `Over S` into a locally surjective map of the restricted
functors of points, with no hypothesis on the sizes of its source and target — the fibre product
with a test object of the site, which need not lie in the site because of the site's cardinality
cutoff, is refined there to one of the site's chosen covering families.  In particular no
cardinality estimate for the disjoint union of Step 3 is required, and the footnote of the source
is not needed.

The second is that the conclusion of the tag asks for *some* equivalence relation `R'` on *some*
`U'` with a morphism to `R`, not for the restriction of `R` along a single morphism `U' ⟶ U`.  The
two stages do not collapse into one such morphism: the reach map of the composite factors through
the base change of the immersion `U' ⟶ U₁`, so it is not flat, hence not an fppf covering, and
Stacks 02VH does not apply to it once.  The source proof passes to the quotient twice for the
same reason, and so does this file: `R'` is taken to be the second stage's restriction, whose
source and target are base changes of the second stage's reach map (Stacks 04MV, here
`AlgebraicGeometry.restriction_source_mem` and `AlgebraicGeometry.restriction_target_mem`) and
therefore flat, locally of finite presentation, locally of finite type and locally quasi-finite;
and `U'/R' ⟶ U/R` is the composite of the two stages' maps of quotient sheaves, each an
isomorphism by Stacks 02VH.

Beyond the tag, the conclusion also records that the map of quotient sheaves induced by the
restriction of `R` along the single composite `U' ⟶ U` is an isomorphism, for *every* groupoid
scheme realizing that restriction; this is
`AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_comp_reach`.  That `R'` and
those restrictions are the same equivalence relation on `U'` is Stacks 04MW, which this library
has only as the comparison diagram `AlgebraicGeometry.doubleRestrictionDiagram` and not as an
identification of realizations; nothing below uses such an identification.

## References

* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
* [Stacks Project, Tag 04MW](https://stacks.math.columbia.edu/tag/04MW)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- **Stacks Project, Tag 0489.**

Let `(U, R, s, t, c, e, i)` be a groupoid scheme over `S` whose target and source maps form an
equivalence relation and are flat and locally of finite presentation.  Then there are a scheme
`U'` over `S`, a morphism `U' ⟶ U`, and an equivalence relation `R'` on `U'` mapping into `R`
over it, whose source and target maps are flat, locally of finite presentation, locally of finite
type and locally quasi-finite, and for which the induced map `U'/R' ⟶ U/R` of quotient sheaves on
the big fppf site over `S` is an isomorphism.

The refinement is produced in the two stages of the source proof: `g₁ : U₁ ⟶ U` is the inclusion
of the Cohen-Macaulay open of Stacks 0460, `H₁` is the restriction of `R` along it,
`g' : U' ⟶ U₁` is the disjoint union of the affine slices of Stacks 04N0 over the finite type
points of `U₁`, and `R'` is the restriction `H'` of `H₁` along `g'`.  The morphism `U' ⟶ U` is the
composite `g`, and the morphism of `R'` into `R` is the composite of the two restrictions'
canonical morphisms, which lies over `g` by the second conclusion below.

The last conclusion is more than the tag asks: the map of quotient sheaves induced by the
restriction of `R` along the single morphism `g` is an isomorphism for *every* groupoid scheme
realizing that restriction.  Together with the isomorphism for `R'` it says that the two
descriptions of the refined relation — the restriction of the restriction, and the restriction
along the composite — have the same quotient; that they are the same relation is Stacks 04MW,
which is not used here.

The last two conclusions are the size estimates of the two stages, also more than the tag asks:
the first stage is an open of `U`, and the second is a disjoint union of affine immersions
locally of finite presentation indexed by the points of the first, so
`size U₁ ≤ size U` and `size U' ≤ 2 ^ size U`.  They are not used for the isomorphism of
quotient sheaves — that needs no cardinality hypothesis at all, see the implementation notes —
but they are what a later consumer needs in order to exhibit `U'` and the arrow scheme of `R'`
as *objects of the site*, which the engine of Stacks 02WW requires and which the existential
form of this statement would otherwise destroy. -/
@[stacks 0489 "unconditionally, with no assumed input: the hypotheses are exactly the tag's, that
the source and target of the groupoid scheme are an equivalence relation and are flat and locally
of finite presentation. The refined equivalence relation R' is the restriction H' along the second
stage g' of the restriction H₁ along the first stage g₁ of the two-stage refinement that
`exists_cohenMacaulay_and_quasiFinite_refinement` produces -- the Cohen-Macaulay open of
Stacks 0460, then the disjoint union of the affine slices of Stacks 04N0 over the finite type
points -- and the morphism U' ⟶ U of the tag is the composite g, over which the composite of the
two restrictions' canonical morphisms carries R' into R. Its source and target are flat, locally
of finite presentation, locally of finite type and locally quasi-finite, being base changes of the
second stage's reach map by Stacks 04MV; it is an equivalence relation by
`restriction_isEquivalenceRelation`; and U'/R' ⟶ U/R, the composite of the two stages' maps of
quotient sheaves, is an isomorphism because each stage's reach map is flat, locally of finite
presentation and surjective and therefore locally surjective on the functors of points of the big
fppf site by `isLocallySurjective_points_map_of_fppf`, which Stacks 02VH turns into an
isomorphism of quotient sheaves. No covering datum is assumed: on this site a flat, locally
finitely presented, surjective morphism of Over S is locally surjective on points whatever the
sizes of its source and target, so neither the disjoint union of Step 3 nor the source of either
reach map has to be exhibited as an object of the site. The two stages are not collapsed into one
morphism whose reach map is a covering, because the reach map of the composite factors through the
base change of an immersion and so is not flat; the final conclusion instead gives the
isomorphism of quotient sheaves for the restriction along the composite as well, by
`isIso_restrictionQuotientMap_of_comp_reach`"]
theorem exists_locallyQuasiFinite_refinement_isIso_quotientMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : GroupoidScheme S) [IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left] :
    letI := BigFppfOver.hasSheafify_type B S hS
    ∃ (U₁ : Over S) (g₁ : U₁ ⟶ G.objects) (H₁ : Restriction G g₁) (U' : Over S)
      (g' : U' ⟶ H₁.groupoid.objects) (H' : Restriction H₁.groupoid g')
      (g : U' ⟶ G.objects),
      g = g' ≫ H₁.hom.mapObjects ∧
      H'.hom.mapObjects ≫ H₁.hom.mapObjects = eqToHom H'.objects_eq ≫ g ∧
      IsEquivalenceRelation H'.groupoid.target H'.groupoid.source ∧
      Flat H'.groupoid.source.left ∧
      LocallyOfFinitePresentation H'.groupoid.source.left ∧
      LocallyOfFiniteType H'.groupoid.source.left ∧
      LocallyQuasiFinite H'.groupoid.source.left ∧
      Flat H'.groupoid.target.left ∧
      LocallyOfFinitePresentation H'.groupoid.target.left ∧
      LocallyOfFiniteType H'.groupoid.target.left ∧
      LocallyQuasiFinite H'.groupoid.target.left ∧
      IsIso (restrictionQuotientMap (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          H₁.groupoid g' H' ≫
        restrictionQuotientMap (BigFppfOver.topology B S hS) (Over.post B.inclusion) G g₁ H₁) ∧
      (∀ H : Restriction G g,
        IsIso (restrictionQuotientMap (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) G g H)) ∧
      U₁.left.size ≤ G.objects.left.size ∧
      U'.left.size ≤ 2 ^ G.objects.left.size := by
  have : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  have : (BigFppfOver.topology B S hS).WEqualsLocallyBijective (Type u) :=
    BigFppfOver.wEqualsLocallyBijective_type B S hS
  obtain ⟨U₁, g₁, h₁flat, h₁lfp, h₁surj, h₁size, U', g', hflat, hlfp, hlqf, hsurj, hsize⟩ :=
    exists_cohenMacaulay_and_quasiFinite_refinement G
  -- each stage's reach map is an fppf covering, hence locally surjective on functors of points
  have hreach : ∀ {U M : Over S} (f : U ⟶ M) [Flat f.left] [LocallyOfFinitePresentation f.left]
      [Surjective f.left], Sheaf.IsLocallySurjective ((presheafToSheaf
        (BigFppfOver.topology B S hS) (Type u)).map ((Over.post B.inclusion).op.whiskerLeft
          (yoneda.map f))) := fun f _ _ _ =>
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2
      (AlgebraicGeometry.isLocallySurjective_points_map_of_fppf B S hS f)
  have hreach₁ := hreach (restrictionReachMap G g₁)
  have hreach' := hreach (restrictionReachMap (GroupoidScheme.restrict G g₁).groupoid g')
  refine ⟨U₁, g₁, GroupoidScheme.restrict G g₁, U', g',
    GroupoidScheme.restrict (GroupoidScheme.restrict G g₁).groupoid g',
    g' ≫ (GroupoidScheme.restrict G g₁).hom.mapObjects, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, h₁size, hsize⟩
  · -- the composite of the two restrictions' morphisms lies over the composite of the two stages
    rw [(GroupoidScheme.restrict (GroupoidScheme.restrict G g₁).groupoid g').mapObjects_eq,
      Category.assoc]
  · -- the restriction of an equivalence relation is an equivalence relation, twice
    have _ : IsEquivalenceRelation (GroupoidScheme.restrict G g₁).groupoid.target
        (GroupoidScheme.restrict G g₁).groupoid.source :=
      AlgebraicGeometry.restriction_isEquivalenceRelation G g₁ (GroupoidScheme.restrict G g₁)
    exact AlgebraicGeometry.restriction_isEquivalenceRelation
      (GroupoidScheme.restrict G g₁).groupoid g' _
  -- the source and target of the second stage's restriction are base changes of its reach map,
  -- by Stacks 04MV
  · exact AlgebraicGeometry.restriction_source_mem _ g' _ @Flat hflat
  · exact AlgebraicGeometry.restriction_source_mem _ g' _ @LocallyOfFinitePresentation hlfp
  · have := hlfp
    exact AlgebraicGeometry.restriction_source_mem _ g' _ @LocallyOfFiniteType inferInstance
  · exact AlgebraicGeometry.restriction_source_mem _ g' _ @LocallyQuasiFinite hlqf
  · exact AlgebraicGeometry.restriction_target_mem _ g' _ @Flat hflat
  · exact AlgebraicGeometry.restriction_target_mem _ g' _ @LocallyOfFinitePresentation hlfp
  · have := hlfp
    exact AlgebraicGeometry.restriction_target_mem _ g' _ @LocallyOfFiniteType inferInstance
  · exact AlgebraicGeometry.restriction_target_mem _ g' _ @LocallyQuasiFinite hlqf
  · -- Stacks 02VH at each stage, composed
    have _ := isIso_restrictionQuotientMap_of_reach (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (GroupoidScheme.restrict G g₁).groupoid g'
      (GroupoidScheme.restrict (GroupoidScheme.restrict G g₁).groupoid g') hreach'
    have _ := isIso_restrictionQuotientMap_of_reach (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) G g₁ (GroupoidScheme.restrict G g₁) hreach₁
    infer_instance
  · -- the same two applications of Stacks 02VH, transported to the restriction along the
    -- composite
    intro H
    exact isIso_restrictionQuotientMap_of_comp_reach _ _ G g₁ (GroupoidScheme.restrict G g₁) g'
      (GroupoidScheme.restrict (GroupoidScheme.restrict G g₁).groupoid g') _ rfl H hreach₁ hreach'

end AlgebraicGeometry.GroupoidScheme

end
