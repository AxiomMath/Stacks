module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.DividedQuotientAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingAffineLocalization

/-!
# The quotient over an affine étale neighbourhood of a point

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` affine and in the big fppf site,
whose target and source form an internal equivalence relation and are flat, locally of finite
presentation, locally of finite type and locally quasi-finite, and let `u` be a point of `U`.
[Stacks, Tag 04S0] produces an affine étale neighbourhood `U'' ⟶ U` of `u` over which the
restricted groupoid is quasi-split; the division step
`AlgebraicGeometry.isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_openFiniteSubgroupoid` then makes
the quotient of the restricted relation an algebraic space with an atlas no larger than `U`.

This is step (B) of the proof of [Stacks, Tag 04S6] at one point; the affine case of condition
(2) is obtained from it by covering the quasi-compact `U` by finitely many such neighbourhoods.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.property_restrictionReach_of_source`: the reach map of a restriction has
  every property which is stable under base change and composition and holds for the source map
  of the groupoid and for the restricting map.  This is the hypothesis in which
  `AlgebraicGeometry.restriction_source_mem` states the properties of a restricted source.
* `AlgebraicGeometry.exists_affineEtale_isAlgebraicSpaceAtlasSizeLE_restrictedQuotient`: the
  affine étale neighbourhood of the point over which the quotient of the restricted relation is
  an algebraic space with an atlas no larger than the object scheme.

## Implementation notes

The quasi-splitting situation of [Stacks, Tag 04RV] is assembled from the hypotheses: the
separatedness of the two legs is `AlgebraicGeometry.PreRelation.isSeparated_left_of_isAffine`
read for the legs rather than for the relation, local finite type of the target comes from the
source through the inverse, and quasi-finiteness of the source at the identity arrow is local
finite presentation together with local quasi-finiteness.  The three site-membership hypotheses
of [Stacks, Tag 04S0] are the arrow scheme (monic relation into `U ×_S U`), the scheme of
composable pairs (a fibre product of two copies of the arrow scheme) and the spectrum of the
residue field at `u` (a quasi-compact monomorphism into `U`).

The bound on the atlas is `size U` throughout: the neighbourhood is affine and étale over `U`, so
it is no larger than `U` by [Stacks, Tag 04T7], and the division step bounds its atlas by the
size of the neighbourhood.

## References

* [Stacks Project, Tag 04S0](https://stacks.math.columbia.edu/tag/04S0)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open Stacks.Groupoids.GroupoidScheme

universe u

namespace AlgebraicGeometry

/-- The reach map `U' ×_{g, U, t} R ⟶ U` of a restriction has every property which is stable
under base change and under composition and which holds for the source map of the groupoid and
for the restricting map.  This is the shape in which
`AlgebraicGeometry.restriction_source_mem` asks for the properties of a restricted source. -/
theorem property_restrictionReach_of_source {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (hs : P G.source.left) (hg : P g.left) :
    P ((pullback.snd g G.target ≫ G.source).left) := by
  rw [Over.comp_left]
  exact P.comp_mem _ _
    (P.of_isPullback ((IsPullback.of_hasPullback g G.target).map (Over.forget S)) hg) hs

/-- The source map of a restriction has every property which is stable under base change and
under composition and which holds for the source map of the groupoid and for the restricting
map. -/
private theorem property_restriction_source {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (R : GroupoidScheme.Restriction G g)
    (hs : P G.source.left := by infer_instance)
    (hg : P g.left := by infer_instance) : P R.groupoid.source.left :=
  restriction_source_mem G g R P (property_restrictionReach_of_source P G g hs hg)

/-- The target map of a groupoid scheme has every property which is stable under base change and
holds for its source map. -/
private theorem property_target_of_property_source_of_isStableUnderBaseChange {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (G : GroupoidScheme S)
    (hP : P G.source.left := by infer_instance) : P G.target.left := by
  have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact GroupoidScheme.property_target_of_property_source P G hP

/-- **Step (B) of [Stacks, Tag 04S6] at one point.**

A point of the affine object scheme of a flat, locally finitely presented, locally quasi-finite
equivalence-relation groupoid in the big fppf site has an affine étale neighbourhood, no larger
than the object scheme, over which the quotient sheaf of the restricted relation is an algebraic
space with a surjective étale atlas again no larger than the object scheme.

[Stacks, Tag 04S0] supplies the neighbourhood together with a quasi-splitting of the restricted
groupoid, and
`AlgebraicGeometry.isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_openFiniteSubgroupoid` divides by
it. -/
theorem exists_affineEtale_isAlgebraicSpaceAtlasSizeLE_restrictedQuotient
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    [IsAffine G.objects.left]
    [CategoryTheory.IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [LocallyQuasiFinite G.source.left] [LocallyOfFiniteType G.source.left]
    (u : G.objects.left) :
    ∃ (U' : Over S) (g : U' ⟶ G.objects),
      IsAffine U'.left ∧ Etale g.left ∧ (∃ y, g.left.base y = u) ∧
        U'.left.size ≤ G.objects.left.size ∧
        Space.IsAlgebraicSpaceAtlasSizeLE B S hS
          (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
            (Over.post B.inclusion)
            (PreRelation.restrict (groupoidPreRelation G) g)).obj G.objects.left.size := by
  classical
  -- the relation is a monomorphism, so the arrow scheme is a separated scheme in the site
  have _ : JointlyMono₂ G.target G.source := jointlyMono₂_of_isEquivalenceRelation G
  have _ : Mono (groupoidPreRelation G) := mono_groupoidPreRelation_of_jointlyMono₂ G
  have _ : G.arrows.left.IsSeparated :=
    PreRelation.isSeparated_left_of_isAffine (groupoidPreRelation G)
  have hR : B.Contains G.arrows.left := B.contains_arrows_of_isEquivalenceRelation G hU
  -- the target map inherits what the source map has
  have _ : Flat G.target.left :=
    property_target_of_property_source_of_isStableUnderBaseChange @Flat G
  have _ : LocallyOfFinitePresentation G.target.left :=
    property_target_of_property_source_of_isStableUnderBaseChange @LocallyOfFinitePresentation G
  have _ : LocallyOfFiniteType G.target.left :=
    property_target_of_property_source_of_isStableUnderBaseChange @LocallyOfFiniteType G
  -- the quasi-splitting situation of Tag 04RV
  let D : Space.QuasiSplittingSituation.{u} :=
    { S := S, groupoid := G, u := u
      sourceQuasiFiniteAtIdentity :=
        (forall_quasiFiniteAt_iff G.source.left).mpr ⟨inferInstance, inferInstance⟩ _ }
  -- the three site-membership hypotheses of Tag 04S0
  have hP : B.Contains (pullback G.source G.target).left :=
    (Scheme.size_congr ((IsPullback.of_hasPullback G.source G.target).map
      (Over.forget S)).isoPullback).trans_lt (Scheme.size_pullback_lt _ _ hR hR)
  obtain ⟨U₁, gp, R₁, U₂, jj, u₂, -, -, haff, -, het, hpt, -, -, hqsplit⟩ :=
    GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation D B hS hU hR hP
      (Scheme.size_lt_of_mono_quasiCompact (G.objects.left.fromSpecResidueField u) hU)
  set g : U₂ ⟶ G.objects := jj ≫ R₁.hom.mapObjects
  obtain ⟨_, -, _⟩ := Etale.iff_flat_and_formallyUnramified.mp het
  have hgsize : U₂.left.size ≤ G.objects.left.size := Scheme.size_le_of_locallyOfFiniteType g.left
  -- the restriction of the groupoid along the neighbourhood
  set Gr := GroupoidScheme.restrict G g
  have hGrobj : Gr.groupoid.objects.left = U₂.left := congrArg Over.left Gr.objects_eq
  have _ : IsAffine Gr.groupoid.objects.left := by rwa [hGrobj]
  have hGrsize : Gr.groupoid.objects.left.size ≤ G.objects.left.size := by rwa [hGrobj]
  have _ := restriction_isEquivalenceRelation G g Gr
  have _ : Flat Gr.groupoid.source.left :=
    property_restriction_source @Flat G g Gr
  have _ : LocallyOfFinitePresentation Gr.groupoid.source.left :=
    property_restriction_source @LocallyOfFinitePresentation G g Gr
  have _ : LocallyOfFiniteType Gr.groupoid.source.left :=
    property_restriction_source @LocallyOfFiniteType G g Gr
  have _ : LocallyQuasiFinite Gr.groupoid.source.left :=
    property_restriction_source @LocallyQuasiFinite G g Gr
  -- the quasi-splitting, and the division by it
  obtain ⟨Psplit⟩ := hqsplit Gr
  exact ⟨U₂, g, haff, het, ⟨u₂, hpt⟩, hgsize, (Space.IsAlgebraicSpaceAtlasSizeLE.of_iso
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      (GroupoidScheme.restrictionQuotientIso (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) G g Gr).symm)
    (isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_openFiniteSubgroupoid B S hS
      Gr.groupoid (hGrsize.trans_lt hU) Psplit.toOpenFiniteSubgroupoid)).mono hGrsize⟩

end AlgebraicGeometry

end
