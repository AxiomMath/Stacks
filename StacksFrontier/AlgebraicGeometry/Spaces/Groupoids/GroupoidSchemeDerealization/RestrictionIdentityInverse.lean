module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization.SpaceRestriction

/-!
# The arrows, identity and inverse of a restriction of a groupoid scheme

The identification `Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso` of the space
represented by the arrow scheme of the restriction of a groupoid scheme with the arrow space of
the restriction of its realization, and the identity
(`Stacks.Groupoids.GroupoidScheme.restrictionIdentity`) and inverse
(`Stacks.Groupoids.GroupoidScheme.restrictionInverse`) of a restriction at the scheme level,
each determined by its source, target and underlying arrow.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_RestrictionIdentityInverse (C : BigFppfSite.{u})
    (hS : C.Contains S) :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RestrictionIdentityInverse
    (C : BigFppfSite.{u}) (hS : C.Contains S) {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The morphism to the object space of the realization of a groupoid scheme represented by a
morphism of schemes over `S` to its object scheme. -/
noncomputable abbrev realizationMap (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) : siteSchemeSpace C hS hX ⟶ (G.realization C hS hU hR hP).objects :=
  siteSchemeSpaceMap C hS hX hU p

/-- The first projection of the arrow scheme of a restriction: an arrow together with the lift
of its target. -/
noncomputable abbrev restrictionArrowsFst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : AlgebraicGeometry.restrictionArrows G p ⟶ pullback p G.target :=
  pullback.fst (pullback.snd p G.target) (pullback.fst G.source p)

/-- The second projection of the arrow scheme of a restriction: an arrow together with the lift
of its source. -/
noncomputable abbrev restrictionArrowsSnd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : AlgebraicGeometry.restrictionArrows G p ⟶ pullback G.source p :=
  pullback.snd (pullback.snd p G.target) (pullback.fst G.source p)

/-- Yoneda carries the square exhibiting the arrow scheme of a restriction as an iterated fibre
product to a cartesian square of presheaves. -/
theorem isPullback_restrictionArrowsSite (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hR : C.Contains G.arrows.left) {X : Over S} (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left) (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    IsPullback
      (yoneda.map (schemeSiteMap C hS hRA hA (restrictionArrowsFst G p)))
      (yoneda.map (schemeSiteMap C hS hRA hB (restrictionArrowsSnd G p)))
      (yoneda.map (schemeSiteMap C hS hA hR (pullback.snd p G.target)))
      (yoneda.map (schemeSiteMap C hS hB hR (pullback.fst G.source p))) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (yonedaSchemePullbackIso C hS hA hB hR (pullback.snd p G.target)
      (pullback.fst G.source p) hRA).symm ?_ ?_
  · rw [← yoneda.map_comp, ← yoneda.map_comp, ← schemeSiteMap_comp, ← schemeSiteMap_comp]
    exact congrArg (fun k => yoneda.map (schemeSiteMap C hS hRA hR k)) pullback.condition
  · exact (Iso.inv_comp_eq _).2 (yonedaSchemePullbackIso_hom_fst C hS hA hB hR
      (pullback.snd p G.target) (pullback.fst G.source p) hRA).symm
  · exact (Iso.inv_comp_eq _).2 (yonedaSchemePullbackIso_hom_snd C hS hA hB hR
      (pullback.snd p G.target) (pullback.fst G.source p) hRA).symm

/-- The cartesian square of `Stacks.Groupoids.GroupoidScheme.isPullback_restrictionArrowsSite`,
read on the cospan which defines the arrow space of the restriction of the realization. -/
theorem isPullback_restrictionArrowsRealization (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left) (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    IsPullback
      (yoneda.map (schemeSiteMap C hS hRA hA (restrictionArrowsFst G p)) ≫
        (yonedaSchemePullbackIso C hS hX hR hU p G.target hA).inv)
      (yoneda.map (schemeSiteMap C hS hRA hB (restrictionArrowsSnd G p)) ≫
        (yonedaSchemePullbackIso C hS hR hX hU G.source p hB).inv)
      (pullback.snd (yoneda.map (schemeSiteMap C hS hX hU p))
        (yoneda.map (schemeSiteMap C hS hR hU G.target)))
      (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source))
        (yoneda.map (schemeSiteMap C hS hX hU p))) := by
  have h := isPullback_comp_iso (isPullback_restrictionArrowsSite G C hS hR p hA hB hRA)
    (yonedaSchemePullbackIso C hS hX hR hU p G.target hA)
    (yonedaSchemePullbackIso C hS hR hX hU G.source p hB)
  rwa [yonedaSchemePullbackIso_hom_snd, yonedaSchemePullbackIso_hom_fst] at h

/-- **De-realization of the arrows of a restriction.**  The arrow space of the restriction of
the realization of a groupoid scheme along a represented morphism is the space represented by
the arrow scheme of the restriction of the groupoid scheme. -/
noncomputable def restrictionArrowsRealizationIso (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    yoneda.obj (schemeSiteObject C hS hRA) ≅
      pullback
        (pullback.snd (yoneda.map (schemeSiteMap C hS hX hU p))
          (yoneda.map (schemeSiteMap C hS hR hU G.target)))
        (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source))
          (yoneda.map (schemeSiteMap C hS hX hU p))) :=
  (isPullback_restrictionArrowsRealization G C hS hU hR hX p hA hB hRA).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- The arrow space of the restriction of a realization along a represented morphism is the
iterated fibre product of the Yoneda images of the structure morphisms. -/
theorem restrictionArrows_realizationMap_obj (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) :
    (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).obj =
      pullback
        (pullback.snd (yoneda.map (schemeSiteMap C hS hX hU p))
          (yoneda.map (schemeSiteMap C hS hR hU G.target)))
        (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source))
          (yoneda.map (schemeSiteMap C hS hX hU p))) :=
  rfl

/-- The identification of the arrows of a restriction carries the first projection of the
space-level iterated fibre product to the Yoneda image of the first projection of the arrow
scheme. -/
theorem restrictionArrowsRealizationIso_hom_comp_fst (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫
        pullback.fst
          (pullback.snd (yoneda.map (schemeSiteMap C hS hX hU p))
            (yoneda.map (schemeSiteMap C hS hR hU G.target)))
          (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source))
            (yoneda.map (schemeSiteMap C hS hX hU p))) =
      yoneda.map (schemeSiteMap C hS hRA hA (restrictionArrowsFst G p)) ≫
        (yonedaSchemePullbackIso C hS hX hR hU p G.target hA).inv :=
  IsPullback.isoIsPullback_hom_fst _ _
    (isPullback_restrictionArrowsRealization G C hS hU hR hX p hA hB hRA)
    (IsPullback.of_hasPullback _ _)

/-- The identification of the arrows of a restriction carries the second projection of the
space-level iterated fibre product to the Yoneda image of the second projection of the arrow
scheme. -/
theorem restrictionArrowsRealizationIso_hom_comp_snd (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫
        pullback.snd
          (pullback.snd (yoneda.map (schemeSiteMap C hS hX hU p))
            (yoneda.map (schemeSiteMap C hS hR hU G.target)))
          (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source))
            (yoneda.map (schemeSiteMap C hS hX hU p))) =
      yoneda.map (schemeSiteMap C hS hRA hB (restrictionArrowsSnd G p)) ≫
        (yonedaSchemePullbackIso C hS hR hX hU G.source p hB).inv :=
  IsPullback.isoIsPullback_hom_snd _ _
    (isPullback_restrictionArrowsRealization G C hS hU hR hX p hA hB hRA)
    (IsPullback.of_hasPullback _ _)

/-- If a projection `a` is carried by `h` to the Yoneda image of `f` followed by `i`, and `i`
followed by `k` is the Yoneda image of `g`, then `a ≫ k` is carried to the Yoneda image of
`f ≫ g`. -/
private theorem comp_comp_eq_yoneda_map_schemeSiteMap_comp (C : BigFppfSite.{u})
    (hS : C.Contains S) {X Y Z : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (hZ : C.Contains Z.left) {f : X ⟶ Y} {g : Y ⟶ Z} {B B'}
    {h : yoneda.obj (schemeSiteObject C hS hX) ⟶ B} {a : B ⟶ B'}
    {i : yoneda.obj (schemeSiteObject C hS hY) ⟶ B'}
    {k : B' ⟶ yoneda.obj (schemeSiteObject C hS hZ)}
    (hf : h ≫ a = yoneda.map (schemeSiteMap C hS hX hY f) ≫ i)
    (hg : i ≫ k = yoneda.map (schemeSiteMap C hS hY hZ g)) :
    h ≫ a ≫ k = yoneda.map (schemeSiteMap C hS hX hZ (f ≫ g)) := by
  rw [← Category.assoc, hf, Category.assoc, hg, ← yoneda.map_comp, ← schemeSiteMap_comp]

/-- **De-realization of the projection to the ambient arrows.**  The identification carries the
projection of the restricted arrow space to the arrow space of the realization to the Yoneda
image of the corresponding projection of arrow schemes. -/
theorem restrictionArrowsRealizationIso_hom_comp_arrowsToArrows (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)
    {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p)) :=
  comp_comp_eq_yoneda_map_schemeSiteMap_comp C hS hRA hA hR
    (restrictionArrowsRealizationIso_hom_comp_fst G C hS hU hR hX p hA hB hRA)
    ((Iso.inv_comp_eq _).2 (yonedaSchemePullbackIso_hom_snd C hS hX hR hU p G.target hA).symm)

/-- **De-realization of the source of a restriction.**  The identification carries the source of
the restricted realization to the Yoneda image of the source of the restricted groupoid
scheme. -/
theorem restrictionArrowsRealizationIso_hom_comp_source (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)
    {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) :=
  comp_comp_eq_yoneda_map_schemeSiteMap_comp C hS hRA hB hX
    (restrictionArrowsRealizationIso_hom_comp_snd G C hS hU hR hX p hA hB hRA)
    ((Iso.inv_comp_eq _).2 (yonedaSchemePullbackIso_hom_snd C hS hR hX hU G.source p hB).symm)

/-- **De-realization of the target of a restriction.**  The identification carries the target of
the restricted realization to the Yoneda image of the target of the restricted groupoid
scheme. -/
theorem restrictionArrowsRealizationIso_hom_comp_target (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)
    {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left) :
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p)) :=
  comp_comp_eq_yoneda_map_schemeSiteMap_comp C hS hRA hA hX
    (restrictionArrowsRealizationIso_hom_comp_fst G C hS hU hR hX p hA hB hRA)
    ((Iso.inv_comp_eq _).2 (yonedaSchemePullbackIso_hom_fst C hS hX hR hU p G.target hA).symm)

/-! ### The identity of a restriction at the scheme level -/

/-- The target-lift component of the identity arrow of a restriction: the point itself, together
with the identity arrow of `G` at its image. -/
noncomputable def restrictionIdentityTargetLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : X ⟶ pullback p G.target :=
  pullback.lift (𝟙 X) (p ≫ G.identity)
    (by rw [Category.id_comp, Category.assoc, G.target_identity, Category.comp_id])

/-- The source-lift component of the identity arrow of a restriction. -/
noncomputable def restrictionIdentitySourceLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : X ⟶ pullback G.source p :=
  pullback.lift (p ≫ G.identity) (𝟙 X)
    (by rw [Category.id_comp, Category.assoc, G.source_identity, Category.comp_id])

/-- The arrow of `G` carried by the target-lift component of the identity. -/
theorem restrictionIdentityTargetLift_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentityTargetLift G p ≫ pullback.snd p G.target = p ≫ G.identity :=
  pullback.lift_snd _ _ _

/-- The point carried by the target-lift component of the identity. -/
theorem restrictionIdentityTargetLift_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentityTargetLift G p ≫ pullback.fst p G.target = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The arrow of `G` carried by the source-lift component of the identity. -/
theorem restrictionIdentitySourceLift_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentitySourceLift G p ≫ pullback.fst G.source p = p ≫ G.identity :=
  pullback.lift_fst _ _ _

/-- The point carried by the source-lift component of the identity. -/
theorem restrictionIdentitySourceLift_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentitySourceLift G p ≫ pullback.snd G.source p = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- **The identity of a restriction, at the scheme level.**  The identity arrow of the
restriction of `G` along `p` at a point of `X`: the identity arrow of `G` at its image, with both
endpoint lifts the point itself. -/
noncomputable def restrictionIdentity (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : X ⟶ AlgebraicGeometry.restrictionArrows G p :=
  pullback.lift (restrictionIdentityTargetLift G p) (restrictionIdentitySourceLift G p)
    ((restrictionIdentityTargetLift_comp_snd G p).trans
      (restrictionIdentitySourceLift_comp_fst G p).symm)

/-- The identity arrow projects to its target-lift component. -/
theorem restrictionIdentity_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentity G p ≫
        pullback.fst (pullback.snd p G.target) (pullback.fst G.source p) =
      restrictionIdentityTargetLift G p :=
  pullback.lift_fst _ _ _

/-- The identity arrow projects to its source-lift component. -/
theorem restrictionIdentity_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentity G p ≫
        pullback.snd (pullback.snd p G.target) (pullback.fst G.source p) =
      restrictionIdentitySourceLift G p :=
  pullback.lift_snd _ _ _

/-- The arrow of `G` underlying the identity arrow of a restriction is the identity arrow of `G`
at the image of the point. -/
theorem restrictionIdentity_comp_arrowsToArrows (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentity G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      p ≫ G.identity :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd p G.target)
      (restrictionIdentity_comp_fst G p)).trans
      (restrictionIdentityTargetLift_comp_snd G p))

/-- The source of the identity arrow of a restriction is the point itself. -/
theorem restrictionIdentity_comp_source (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentity G p ≫ AlgebraicGeometry.restrictionSource G p = 𝟙 X :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd G.source p)
      (restrictionIdentity_comp_snd G p)).trans
      (restrictionIdentitySourceLift_comp_snd G p))

/-- The target of the identity arrow of a restriction is the point itself. -/
theorem restrictionIdentity_comp_target (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentity G p ≫ AlgebraicGeometry.restrictionTarget G p = 𝟙 X :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst p G.target)
      (restrictionIdentity_comp_fst G p)).trans
      (restrictionIdentityTargetLift_comp_fst G p))

/-- **The identity of a restriction is pinned down by three identities.**  A morphism into the
arrow scheme of a restriction whose source and target are both the point itself and whose
underlying arrow of `G` is the identity arrow of `G` there is the identity arrow of the
restriction.

This is `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext`, and it is what identifies the
opaque `identity` field of the groupoid scheme produced by
`AlgebraicGeometry.GroupoidScheme.restrict`. -/
theorem eq_restrictionIdentity_of_spec (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) (c : X ⟶ AlgebraicGeometry.restrictionArrows G p)
    (hsrc : c ≫ AlgebraicGeometry.restrictionSource G p = 𝟙 X)
    (htgt : c ≫ AlgebraicGeometry.restrictionTarget G p = 𝟙 X)
    (harr : c ≫ AlgebraicGeometry.restrictionArrowsToArrows G p = p ≫ G.identity) :
    c = restrictionIdentity G p :=
  AlgebraicGeometry.GroupoidScheme.restriction_hom_ext G p c (restrictionIdentity G p)
    (hsrc.trans (restrictionIdentity_comp_source G p).symm)
    (htgt.trans (restrictionIdentity_comp_target G p).symm)
    (harr.trans (restrictionIdentity_comp_arrowsToArrows G p).symm)

/-! ### The inverse of a restriction at the scheme level -/

/-- The target-lift component of the inverse of an arrow of a restriction: the OLD source lift,
together with the inverse in `G` of the underlying arrow. -/
noncomputable def restrictionInverseTargetLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    AlgebraicGeometry.restrictionArrows G p ⟶ pullback p G.target :=
  pullback.lift (AlgebraicGeometry.restrictionSource G p)
    (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse)
    (by
      rw [Category.assoc, G.target_inverse]
      exact AlgebraicGeometry.GroupoidScheme.restriction_condition G p)

/-- The source-lift component of the inverse of an arrow of a restriction: the inverse in `G` of
the underlying arrow, together with the OLD target lift. -/
noncomputable def restrictionInverseSourceLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    AlgebraicGeometry.restrictionArrows G p ⟶ pullback G.source p :=
  pullback.lift (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse)
    (AlgebraicGeometry.restrictionTarget G p)
    (by
      rw [Category.assoc, G.source_inverse]
      exact AlgebraicGeometry.GroupoidScheme.restriction_condition' G p)

/-- The arrow of `G` carried by the target-lift component of the inverse. -/
theorem restrictionInverseTargetLift_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverseTargetLift G p ≫ pullback.snd p G.target =
      AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse :=
  pullback.lift_snd _ _ _

/-- The point carried by the target-lift component of the inverse is the old source lift. -/
theorem restrictionInverseTargetLift_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverseTargetLift G p ≫ pullback.fst p G.target =
      AlgebraicGeometry.restrictionSource G p :=
  pullback.lift_fst _ _ _

/-- The arrow of `G` carried by the source-lift component of the inverse. -/
theorem restrictionInverseSourceLift_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverseSourceLift G p ≫ pullback.fst G.source p =
      AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse :=
  pullback.lift_fst _ _ _

/-- The point carried by the source-lift component of the inverse is the old target lift. -/
theorem restrictionInverseSourceLift_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverseSourceLift G p ≫ pullback.snd G.source p =
      AlgebraicGeometry.restrictionTarget G p :=
  pullback.lift_snd _ _ _

/-- **The inverse of a restriction, at the scheme level.**  The inverse of an arrow of the
restriction of `G` along `p`: the inverse in `G` of the underlying arrow, with the two endpoint
lifts exchanged. -/
noncomputable def restrictionInverse (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    AlgebraicGeometry.restrictionArrows G p ⟶ AlgebraicGeometry.restrictionArrows G p :=
  pullback.lift (restrictionInverseTargetLift G p) (restrictionInverseSourceLift G p)
    ((restrictionInverseTargetLift_comp_snd G p).trans
      (restrictionInverseSourceLift_comp_fst G p).symm)

/-- The inverse projects to its target-lift component. -/
theorem restrictionInverse_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverse G p ≫
        pullback.fst (pullback.snd p G.target) (pullback.fst G.source p) =
      restrictionInverseTargetLift G p :=
  pullback.lift_fst _ _ _

/-- The inverse projects to its source-lift component. -/
theorem restrictionInverse_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverse G p ≫
        pullback.snd (pullback.snd p G.target) (pullback.fst G.source p) =
      restrictionInverseSourceLift G p :=
  pullback.lift_snd _ _ _

/-- The arrow of `G` underlying the inverse of an arrow of a restriction is the inverse in `G` of
the underlying arrow. -/
theorem restrictionInverse_comp_arrowsToArrows (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverse G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd p G.target)
      (restrictionInverse_comp_fst G p)).trans
      (restrictionInverseTargetLift_comp_snd G p))

/-- The source of the inverse of an arrow of a restriction is the target of the arrow. -/
theorem restrictionInverse_comp_source (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverse G p ≫ AlgebraicGeometry.restrictionSource G p =
      AlgebraicGeometry.restrictionTarget G p :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd G.source p)
      (restrictionInverse_comp_snd G p)).trans
      (restrictionInverseSourceLift_comp_snd G p))

/-- The target of the inverse of an arrow of a restriction is the source of the arrow. -/
theorem restrictionInverse_comp_target (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInverse G p ≫ AlgebraicGeometry.restrictionTarget G p =
      AlgebraicGeometry.restrictionSource G p :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst p G.target)
      (restrictionInverse_comp_fst G p)).trans
      (restrictionInverseTargetLift_comp_fst G p))

/-- **The inverse of a restriction is pinned down by three identities.**  An endomorphism of the
arrow scheme of a restriction which exchanges the source and the target and inverts the
underlying arrow of `G` is the inverse of the restriction.

This is `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext`, and it is what identifies the
opaque `inverse` field of the groupoid scheme produced by
`AlgebraicGeometry.GroupoidScheme.restrict`. -/
theorem eq_restrictionInverse_of_spec (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects)
    (c : AlgebraicGeometry.restrictionArrows G p ⟶ AlgebraicGeometry.restrictionArrows G p)
    (hsrc : c ≫ AlgebraicGeometry.restrictionSource G p =
      AlgebraicGeometry.restrictionTarget G p)
    (htgt : c ≫ AlgebraicGeometry.restrictionTarget G p =
      AlgebraicGeometry.restrictionSource G p)
    (harr : c ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse) :
    c = restrictionInverse G p :=
  AlgebraicGeometry.GroupoidScheme.restriction_hom_ext G p c (restrictionInverse G p)
    (hsrc.trans (restrictionInverse_comp_source G p).symm)
    (htgt.trans (restrictionInverse_comp_target G p).symm)
    (harr.trans (restrictionInverse_comp_arrowsToArrows G p).symm)

end Stacks.Groupoids.GroupoidScheme

end
