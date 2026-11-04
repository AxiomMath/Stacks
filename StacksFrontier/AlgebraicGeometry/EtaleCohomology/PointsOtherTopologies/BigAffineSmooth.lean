module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the big affine smooth site

The big affine smooth site over a scheme has enough points: its covering families may be taken
finite, so the criterion for the existence of points applies directly.

## Main results

* `AlgebraicGeometry.bigAffineSmooth_hasConservativeFamily` states that the big affine smooth
  site has enough points.

## Implementation notes

The site is the full subcategory of affine objects of the size-bounded slice site over `S`.
Enough points is expressed by the existence of a conservative family of points, with no
prescribed smallness condition. The instances recorded first supply fibre products in the
bounded category, in its slice over `S`, and in the affine full subcategory of that slice,
which is what the finiteness criterion needs.

## References

* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The cone over a diagram of shape `WalkingCospan` built from `pullback.cone` is a limit. -/
private noncomputable def isLimitOfPullbackConePullbackCone
    {C : Type*} [Category C] [HasPullbacks C] (D : WalkingCospan ⥤ C) :
    IsLimit (Cone.ofPullbackCone (F := D)
      (pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr))) :=
  (IsLimit.postcomposeInvEquiv (diagramIsoCospan D) _).symm (limit.isLimit _)

private noncomputable instance createsPullbacks_schemeCutoff
    (B : AlgebraicGeometry.BigSmoothSite.{u}) :
    CreatesLimitsOfShape WalkingCospan
      (ObjectProperty.ι (fun X : Scheme.{u} => X.size < B.cutoff)) where
  CreatesLimit := fun {F} => by
    exact createsLimitFullSubcategoryInclusion' F
      (isLimitOfPullbackConePullbackCone
        (F ⋙ ObjectProperty.ι (fun X : Scheme.{u} => X.size < B.cutoff)))
      (Scheme.size_pullback_lt _ _ (F.obj .left).property (F.obj .right).property)

private noncomputable instance hasPullbacks_schemeCutoff
    (B : AlgebraicGeometry.BigSmoothSite.{u}) :
    HasPullbacks (AlgebraicGeometry.SchemeBelow B.cutoff) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (ObjectProperty.ι _)

private noncomputable instance hasPullbacks_bigSmoothOver
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    HasPullbacks (AlgebraicGeometry.BigSmoothOver B S hS) := inferInstance

private noncomputable instance preservesPullbacks_bigSmoothOverToScheme
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    PreservesLimitsOfShape WalkingCospan (AlgebraicGeometry.BigSmoothOver.toScheme B S hS) := by
  apply comp_preservesLimitsOfShape

private noncomputable instance createsPullbacks_bigAffineSmooth
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    CreatesLimitsOfShape WalkingCospan (AlgebraicGeometry.BigAffineSmooth.inclusion B S hS) where
  CreatesLimit := fun {F} => by
    let G := AlgebraicGeometry.BigSmoothOver.toScheme B S hS
    let D := F ⋙ AlgebraicGeometry.BigAffineSmooth.inclusion B S hS
    letI : IsAffine (G.obj (D.obj .left)) := (F.obj .left).property
    letI : IsAffine (G.obj (D.obj .right)) := (F.obj .right).property
    letI : IsAffine (G.obj (D.obj .one)) := (F.obj .one).property
    exact createsLimitFullSubcategoryInclusion' F
      (isLimitOfPullbackConePullbackCone D) (by
      let e := PreservesPullback.iso G (D.map WalkingCospan.Hom.inl)
        (D.map WalkingCospan.Hom.inr)
      exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance)

private noncomputable instance hasPullbacks_bigAffineSmooth
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    HasPullbacks (AlgebraicGeometry.BigAffineSmooth B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (AlgebraicGeometry.BigAffineSmooth.inclusion B S hS)

/-- **Stacks 06VX, big affine smooth case.** The big affine smooth site over
`S` has enough points. -/
@[stacks 06VX "big_affine_smooth"]
public theorem bigAffineSmooth_hasConservativeFamily
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    (AlgebraicGeometry.BigAffineSmooth.topology B S hS).HasConservativeFamily.{u + 1} :=
  Precoverage.hasConservativeFamily_toGrothendieck_of_finite.{u + 1, u, u + 1} _
    fun _ _ ⟨E, hEq, hE⟩ ↦ ⟨E, hE.2.1, hEq⟩

end AlgebraicGeometry
