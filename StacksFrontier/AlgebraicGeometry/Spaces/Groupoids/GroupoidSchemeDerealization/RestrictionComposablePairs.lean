module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization.RestrictionIdentityInverse

/-!
# Composable pairs and composition of a restriction of a groupoid scheme

The scheme of composable pairs of a restriction of a groupoid scheme and the identification
`Stacks.Groupoids.GroupoidScheme.composablePairsRealizationIso` of the space it represents with
the composable pairs of the restricted realization; the scheme-level composition
`Stacks.Groupoids.GroupoidScheme.restrictionComposition`; and the facts that the identity of a
restriction is idempotent and that the inverse of an arrow composes with it to the identity.
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
local instance hasPullbacks_presheaf_RestrictionComposablePairs (C : BigFppfSite.{u})
    (hS : C.Contains S) :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RestrictionComposablePairs
    (C : BigFppfSite.{u})
    (hS : C.Contains S) {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### De-realization of the composable pairs of a restriction -/

/-- The scheme of composable pairs of arrows of a restriction of a groupoid scheme: the fibre
product of its source and its target, which is the domain of its composition. -/
noncomputable abbrev restrictionComposablePairs (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : Over S :=
  pullback (AlgebraicGeometry.restrictionSource G p) (AlgebraicGeometry.restrictionTarget G p)

/-- The first projection of the composable pairs of a restriction: the arrow composed last. -/
noncomputable abbrev composablePairsFst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p :=
  pullback.fst (AlgebraicGeometry.restrictionSource G p)
    (AlgebraicGeometry.restrictionTarget G p)

/-- The second projection of the composable pairs of a restriction: the arrow composed first. -/
noncomputable abbrev composablePairsSnd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p :=
  pullback.snd (AlgebraicGeometry.restrictionSource G p)
    (AlgebraicGeometry.restrictionTarget G p)

/-- The arrow of `G` underlying the composite of a composable pair of arrows of a restriction:
the composite in `G` of the two underlying arrows, the first projection being the arrow applied
last. -/
noncomputable def restrictionAmbientLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : restrictionComposablePairs G p ⟶ pullback G.source G.target :=
  pullback.lift
    (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
    (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
    (by
      rw [Category.assoc, Category.assoc,
        ← AlgebraicGeometry.GroupoidScheme.restriction_condition,
        AlgebraicGeometry.GroupoidScheme.restriction_condition',
        ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The arrow composed last, read off the lifted pair. -/
theorem restrictionAmbientLift_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionAmbientLift G p ≫ pullback.fst G.source G.target =
      composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p :=
  pullback.lift_fst _ _ _

/-- The arrow composed first, read off the lifted pair. -/
theorem restrictionAmbientLift_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionAmbientLift G p ≫ pullback.snd G.source G.target =
      composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p :=
  pullback.lift_snd _ _ _

/-- The composite in `G` of the two underlying arrows of a composable pair of a restriction. -/
noncomputable def restrictionAmbientComp (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : restrictionComposablePairs G p ⟶ G.arrows :=
  restrictionAmbientLift G p ≫ G.comp

/-- The source of the ambient composite of a composable pair is the source of the arrow composed
first.  This is the field `source_comp` of the groupoid scheme, read on the lifted pair. -/
theorem restrictionAmbientComp_comp_source (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionAmbientComp G p ≫ G.source =
      composablePairsSnd G p ≫ AlgebraicGeometry.restrictionSource G p ≫ p := by
  rw [restrictionAmbientComp, Category.assoc, G.source_comp, ← Category.assoc,
    restrictionAmbientLift_comp_snd, Category.assoc,
    ← AlgebraicGeometry.GroupoidScheme.restriction_condition]

/-- The target of the ambient composite of a composable pair is the target of the arrow composed
last.  This is the field `target_comp` of the groupoid scheme, read on the lifted pair. -/
theorem restrictionAmbientComp_comp_target (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionAmbientComp G p ≫ G.target =
      composablePairsFst G p ≫ AlgebraicGeometry.restrictionTarget G p ≫ p := by
  rw [restrictionAmbientComp, Category.assoc, G.target_comp, ← Category.assoc,
    restrictionAmbientLift_comp_fst, Category.assoc,
    AlgebraicGeometry.GroupoidScheme.restriction_condition']

/-- The target-lift component of the composite of a composable pair of arrows of a restriction:
the target-lift of the arrow composed last, together with the ambient composite. -/
noncomputable def restrictionCompTargetLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : restrictionComposablePairs G p ⟶ pullback p G.target :=
  pullback.lift (composablePairsFst G p ≫ AlgebraicGeometry.restrictionTarget G p)
    (restrictionAmbientComp G p)
    (by rw [Category.assoc, restrictionAmbientComp_comp_target])

/-- The source-lift component of the composite of a composable pair of arrows of a restriction:
the ambient composite, together with the source-lift of the arrow composed first. -/
noncomputable def restrictionCompSourceLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : restrictionComposablePairs G p ⟶ pullback G.source p :=
  pullback.lift (restrictionAmbientComp G p)
    (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionSource G p)
    (by rw [restrictionAmbientComp_comp_source, Category.assoc])

/-- The arrow of `G` carried by the target-lift component is the ambient composite. -/
theorem restrictionCompTargetLift_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionCompTargetLift G p ≫ pullback.snd p G.target = restrictionAmbientComp G p :=
  pullback.lift_snd _ _ _

/-- The point of `X` carried by the target-lift component is the target of the arrow composed
last. -/
theorem restrictionCompTargetLift_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionCompTargetLift G p ≫ pullback.fst p G.target =
      composablePairsFst G p ≫ AlgebraicGeometry.restrictionTarget G p :=
  pullback.lift_fst _ _ _

/-- The arrow of `G` carried by the source-lift component is the ambient composite. -/
theorem restrictionCompSourceLift_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionCompSourceLift G p ≫ pullback.fst G.source p = restrictionAmbientComp G p :=
  pullback.lift_fst _ _ _

/-- The point of `X` carried by the source-lift component is the source of the arrow composed
first. -/
theorem restrictionCompSourceLift_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionCompSourceLift G p ≫ pullback.snd G.source p =
      composablePairsSnd G p ≫ AlgebraicGeometry.restrictionSource G p :=
  pullback.lift_snd _ _ _

/-- **The composition of a restriction, at the scheme level.**  The composite of a composable
pair of arrows of the restriction of `G` along `p`: its underlying arrow of `G` is the composite
of the two underlying arrows, its target-lift is that of the arrow composed last, and its
source-lift is that of the arrow composed first. -/
noncomputable def restrictionComposition (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p :=
  pullback.lift (restrictionCompTargetLift G p) (restrictionCompSourceLift G p)
    ((restrictionCompTargetLift_comp_snd G p).trans
      (restrictionCompSourceLift_comp_fst G p).symm)

/-- The composite of a composable pair projects to its target-lift component. -/
theorem restrictionComposition_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposition G p ≫
        pullback.fst (pullback.snd p G.target) (pullback.fst G.source p) =
      restrictionCompTargetLift G p :=
  pullback.lift_fst _ _ _

/-- The composite of a composable pair projects to its source-lift component. -/
theorem restrictionComposition_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposition G p ≫
        pullback.snd (pullback.snd p G.target) (pullback.fst G.source p) =
      restrictionCompSourceLift G p :=
  pullback.lift_snd _ _ _

/-- The arrow of `G` underlying the composite of a composable pair is the ambient composite. -/
theorem restrictionComposition_comp_arrowsToArrows (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposition G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      restrictionAmbientComp G p :=
  calc restrictionComposition G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p
      = (restrictionComposition G p ≫
          pullback.fst (pullback.snd p G.target) (pullback.fst G.source p)) ≫
        pullback.snd p G.target := (Category.assoc _ _ _).symm
    _ = restrictionCompTargetLift G p ≫ pullback.snd p G.target :=
        congrArg (· ≫ pullback.snd p G.target) (restrictionComposition_comp_fst G p)
    _ = restrictionAmbientComp G p := restrictionCompTargetLift_comp_snd G p

/-- The source of the composite of a composable pair is the source of the arrow composed
first. -/
theorem restrictionComposition_comp_source (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposition G p ≫ AlgebraicGeometry.restrictionSource G p =
      composablePairsSnd G p ≫ AlgebraicGeometry.restrictionSource G p :=
  calc restrictionComposition G p ≫ AlgebraicGeometry.restrictionSource G p
      = (restrictionComposition G p ≫
          pullback.snd (pullback.snd p G.target) (pullback.fst G.source p)) ≫
        pullback.snd G.source p := (Category.assoc _ _ _).symm
    _ = restrictionCompSourceLift G p ≫ pullback.snd G.source p :=
        congrArg (· ≫ pullback.snd G.source p) (restrictionComposition_comp_snd G p)
    _ = _ := restrictionCompSourceLift_comp_snd G p

/-- The target of the composite of a composable pair is the target of the arrow composed
last. -/
theorem restrictionComposition_comp_target (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionComposition G p ≫ AlgebraicGeometry.restrictionTarget G p =
      composablePairsFst G p ≫ AlgebraicGeometry.restrictionTarget G p :=
  calc restrictionComposition G p ≫ AlgebraicGeometry.restrictionTarget G p
      = (restrictionComposition G p ≫
          pullback.fst (pullback.snd p G.target) (pullback.fst G.source p)) ≫
        pullback.fst p G.target := (Category.assoc _ _ _).symm
    _ = restrictionCompTargetLift G p ≫ pullback.fst p G.target :=
        congrArg (· ≫ pullback.fst p G.target) (restrictionComposition_comp_fst G p)
    _ = _ := restrictionCompTargetLift_comp_fst G p

/-- **The composition of a restriction is pinned down by three identities.**  A morphism out of
the composable pairs of a restriction whose source is that of the arrow composed first, whose
target is that of the arrow composed last and whose underlying arrow of `G` is the composite of
the two underlying arrows is the composition of the restriction.

This is `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext`: a generalized point of the arrow
scheme of a restriction is determined by its source, its target and its underlying arrow. -/
theorem eq_restrictionComposition_of_spec (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects)
    (c : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p)
    (hsrc : c ≫ AlgebraicGeometry.restrictionSource G p =
      composablePairsSnd G p ≫ AlgebraicGeometry.restrictionSource G p)
    (htgt : c ≫ AlgebraicGeometry.restrictionTarget G p =
      composablePairsFst G p ≫ AlgebraicGeometry.restrictionTarget G p)
    (harr : c ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      restrictionAmbientComp G p) :
    c = restrictionComposition G p :=
  AlgebraicGeometry.GroupoidScheme.restriction_hom_ext G p c (restrictionComposition G p)
    (hsrc.trans (restrictionComposition_comp_source G p).symm)
    (htgt.trans (restrictionComposition_comp_target G p).symm)
    (harr.trans (restrictionComposition_comp_arrowsToArrows G p).symm)

/-- Yoneda carries the square exhibiting the composable pairs of a restriction as a fibre
product of the source and the target to a cartesian square of presheaves. -/
theorem isPullback_composablePairsSite (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    IsPullback
      (yoneda.map (schemeSiteMap C hS hCP hRA
        (pullback.fst (AlgebraicGeometry.restrictionSource G p)
          (AlgebraicGeometry.restrictionTarget G p))))
      (yoneda.map (schemeSiteMap C hS hCP hRA
        (pullback.snd (AlgebraicGeometry.restrictionSource G p)
          (AlgebraicGeometry.restrictionTarget G p))))
      (yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)))
      (yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p))) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (yonedaSchemePullbackIso C hS hRA hRA hX (AlgebraicGeometry.restrictionSource G p)
      (AlgebraicGeometry.restrictionTarget G p) hCP).symm ?_ ?_
  · rw [← yoneda.map_comp, ← yoneda.map_comp, ← schemeSiteMap_comp, ← schemeSiteMap_comp]
    exact congrArg (fun k => yoneda.map (schemeSiteMap C hS hCP hX k)) pullback.condition
  · exact (Iso.inv_comp_eq _).2 (yonedaSchemePullbackIso_hom_fst C hS hRA hRA hX
      (AlgebraicGeometry.restrictionSource G p)
      (AlgebraicGeometry.restrictionTarget G p) hCP).symm
  · exact (Iso.inv_comp_eq _).2 (yonedaSchemePullbackIso_hom_snd C hS hRA hRA hX
      (AlgebraicGeometry.restrictionSource G p)
      (AlgebraicGeometry.restrictionTarget G p) hCP).symm

/-- The cartesian square of
`Stacks.Groupoids.GroupoidScheme.isPullback_composablePairsSite`, read on the cospan of the
source and the target of the restriction of the realization. -/
theorem isPullback_composablePairsRealization (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    IsPullback
      (yoneda.map (schemeSiteMap C hS hCP hRA
        (pullback.fst (AlgebraicGeometry.restrictionSource G p)
          (AlgebraicGeometry.restrictionTarget G p))) ≫
        (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom)
      (yoneda.map (schemeSiteMap C hS hCP hRA
        (pullback.snd (AlgebraicGeometry.restrictionSource G p)
          (AlgebraicGeometry.restrictionTarget G p))) ≫
        (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom)
      (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom
      (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom := by
  have e₁ : (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).inv ≫
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) =
      (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom :=
    (Iso.inv_comp_eq _).2 (restrictionArrowsRealizationIso_hom_comp_source
      G C hS hU hR hP hX p hA hB hRA).symm
  have e₂ : (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).inv ≫
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p)) =
      (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom :=
    (Iso.inv_comp_eq _).2 (restrictionArrowsRealizationIso_hom_comp_target
      G C hS hU hR hP hX p hA hB hRA).symm
  have h := isPullback_comp_iso (isPullback_composablePairsSite G C hS hX p hRA hCP)
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).symm
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).symm
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  rw [e₁, e₂] at h
  exact h

/-- **De-realization of the composable pairs of a restriction.**  The space of composable pairs
of arrows of the restriction of the realization of a groupoid scheme along a represented
morphism is the space represented by the scheme of composable pairs of the restriction of the
groupoid scheme. -/
noncomputable def composablePairsRealizationIso (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    yoneda.obj (schemeSiteObject C hS hCP) ≅
      (AlgebraicSpaces.fiberProduct C S hS
        (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p))
        (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p))).obj :=
  (isPullback_composablePairsRealization G C hS hU hR hP hX p hA hB hRA hCP).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- The identification of the composable pairs carries the first projection of the space-level
fibre product to the Yoneda image of the first projection of the scheme of composable pairs. -/
theorem composablePairsRealizationIso_hom_comp_fst (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.fiberProductFst
          (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
            (realizationMap G C hS hU hR hP hX p))
          (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
            (realizationMap G C hS hU hR hP hX p))).hom =
      yoneda.map (schemeSiteMap C hS hCP hRA
        (pullback.fst (AlgebraicGeometry.restrictionSource G p)
          (AlgebraicGeometry.restrictionTarget G p))) ≫
        (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom :=
  IsPullback.isoIsPullback_hom_fst _ _
    (isPullback_composablePairsRealization G C hS hU hR hP hX p hA hB hRA hCP)
    (IsPullback.of_hasPullback _ _)

/-- The identification of the composable pairs carries the second projection of the space-level
fibre product to the Yoneda image of the second projection of the scheme of composable
pairs. -/
theorem composablePairsRealizationIso_hom_comp_snd (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.fiberProductSnd
          (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
            (realizationMap G C hS hU hR hP hX p))
          (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
            (realizationMap G C hS hU hR hP hX p))).hom =
      yoneda.map (schemeSiteMap C hS hCP hRA
        (pullback.snd (AlgebraicGeometry.restrictionSource G p)
          (AlgebraicGeometry.restrictionTarget G p))) ≫
        (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom :=
  IsPullback.isoIsPullback_hom_snd _ _
    (isPullback_composablePairsRealization G C hS hU hR hP hX p hA hB hRA hCP)
    (IsPullback.of_hasPullback _ _)

/-! ### The identity of a restriction is idempotent -/

/-- The identity arrow of a restriction, paired with itself as a composable pair: its source and
its target are both the point, so the pair is composable. -/
noncomputable def restrictionIdentityPair (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) : X ⟶ restrictionComposablePairs G p :=
  pullback.lift (restrictionIdentity G p) (restrictionIdentity G p)
    ((restrictionIdentity_comp_source G p).trans (restrictionIdentity_comp_target G p).symm)

/-- Both components of that pair are the identity arrow. -/
theorem restrictionIdentityPair_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentityPair G p ≫ composablePairsFst G p = restrictionIdentity G p :=
  pullback.lift_fst _ _ _

/-- Both components of that pair are the identity arrow. -/
theorem restrictionIdentityPair_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentityPair G p ≫ composablePairsSnd G p = restrictionIdentity G p :=
  pullback.lift_snd _ _ _

/-- The two underlying arrows of that pair are both the identity arrow of `G` at the image of
the point. -/
theorem restrictionIdentityPair_comp_ambientLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentityPair G p ≫ restrictionAmbientLift G p =
      pullback.lift (p ≫ G.identity) (p ≫ G.identity)
        (by rw [Category.assoc, Category.assoc, G.source_identity, G.target_identity]) := by
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionIdentityPair G p ≫ k)
      (restrictionAmbientLift_comp_fst G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
      (restrictionIdentityPair_comp_fst G p)).trans ?_
    exact (restrictionIdentity_comp_arrowsToArrows G p).trans (pullback.lift_fst _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionIdentityPair G p ≫ k)
      (restrictionAmbientLift_comp_snd G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
      (restrictionIdentityPair_comp_snd G p)).trans ?_
    exact (restrictionIdentity_comp_arrowsToArrows G p).trans (pullback.lift_snd _ _ _).symm

/-- The composite in `G` of the identity arrow at a point with itself is that identity arrow.
This is the field `left_identity` of the groupoid scheme, read at the identity arrow. -/
theorem restrictionIdentityPair_comp_ambientComp (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentityPair G p ≫ restrictionAmbientComp G p = p ≫ G.identity := by
  have hfix : (p ≫ G.identity) ≫ G.target ≫ G.identity = p ≫ G.identity := by
    rw [← Category.assoc, Category.assoc p G.identity G.target, G.target_identity,
      Category.comp_id]
  have hts : (G.target ≫ G.identity) ≫ G.source = G.target :=
    (Category.assoc G.target G.identity G.source).trans
      ((congrArg (fun k => G.target ≫ k) G.source_identity).trans (Category.comp_id G.target))
  have hli := G.left_identity X (p ≫ G.identity)
    ((Category.assoc (p ≫ G.identity) (G.target ≫ G.identity) G.source).trans
      (congrArg (fun k => (p ≫ G.identity) ≫ k) hts))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ G.comp)
    (restrictionIdentityPair_comp_ambientLift G p)).trans ?_
  refine Eq.trans ?_ hli
  refine congrArg (fun k => k ≫ G.comp) ?_
  refine pullback.hom_ext ?_ ?_
  · exact (pullback.lift_fst _ _ _).trans ((pullback.lift_fst _ _ _).trans hfix).symm
  · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- **The identity arrow of a restriction is idempotent.**  Composing it with itself returns it.

This is what lets the identity arrow of a restriction be recognised across the de-realization:
the pointwise identity of a groupoid in functors is characterised among arrows with equal source
and target by being idempotent, so this identity together with the source and target
computations is all the identification needs. -/
theorem restrictionIdentityPair_comp_restrictionComposition (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionIdentityPair G p ≫ restrictionComposition G p = restrictionIdentity G p := by
  refine eq_restrictionIdentity_of_spec G p _ ?_ ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionIdentityPair G p ≫ k)
      (restrictionComposition_comp_source G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionSource G p)
      (restrictionIdentityPair_comp_snd G p)).trans ?_
    exact restrictionIdentity_comp_source G p
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionIdentityPair G p ≫ k)
      (restrictionComposition_comp_target G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionTarget G p)
      (restrictionIdentityPair_comp_fst G p)).trans ?_
    exact restrictionIdentity_comp_target G p
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionIdentityPair G p ≫ k)
      (restrictionComposition_comp_arrowsToArrows G p)).trans ?_
    exact restrictionIdentityPair_comp_ambientComp G p

/-! ### The inverse of a restriction composes with its arrow to the identity -/

/-- The inverse of an arrow of a restriction, paired with that arrow: the source of the inverse
is the target of the arrow, so the pair is composable. -/
noncomputable def restrictionInversePair (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    AlgebraicGeometry.restrictionArrows G p ⟶ restrictionComposablePairs G p :=
  pullback.lift (restrictionInverse G p) (𝟙 (AlgebraicGeometry.restrictionArrows G p))
    ((restrictionInverse_comp_source G p).trans (Category.id_comp _).symm)

/-- The first component of that pair is the inverse. -/
theorem restrictionInversePair_comp_fst (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInversePair G p ≫ composablePairsFst G p = restrictionInverse G p :=
  pullback.lift_fst _ _ _

/-- The second component of that pair is the arrow itself. -/
theorem restrictionInversePair_comp_snd (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInversePair G p ≫ composablePairsSnd G p =
      𝟙 (AlgebraicGeometry.restrictionArrows G p) :=
  pullback.lift_snd _ _ _

/-- The two underlying arrows of that pair are the inverse in `G` of the underlying arrow and
the underlying arrow itself. -/
theorem restrictionInversePair_comp_ambientLift (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInversePair G p ≫ restrictionAmbientLift G p =
      pullback.lift (AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.inverse)
        (AlgebraicGeometry.restrictionArrowsToArrows G p)
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => AlgebraicGeometry.restrictionArrowsToArrows G p ≫ k)
            G.source_inverse)) := by
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionInversePair G p ≫ k)
      (restrictionAmbientLift_comp_fst G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
      (restrictionInversePair_comp_fst G p)).trans ?_
    exact (restrictionInverse_comp_arrowsToArrows G p).trans (pullback.lift_fst _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionInversePair G p ≫ k)
      (restrictionAmbientLift_comp_snd G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
      (restrictionInversePair_comp_snd G p)).trans ?_
    exact (Category.id_comp _).trans (pullback.lift_snd _ _ _).symm

/-- The composite in `G` of the inverse of an arrow with that arrow is the identity arrow of `G`
at its source.  This is the field `left_inverse` of the groupoid scheme, read at the underlying
arrow. -/
theorem restrictionInversePair_comp_ambientComp (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInversePair G p ≫ restrictionAmbientComp G p =
      AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.source ≫ G.identity := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ G.comp)
    (restrictionInversePair_comp_ambientLift G p)).trans ?_
  exact G.left_inverse (AlgebraicGeometry.restrictionArrows G p)
    (AlgebraicGeometry.restrictionArrowsToArrows G p) _

/-- **The inverse of a restriction composes with its arrow to the identity at the source.**

Together with the exchange of source and target this is everything needed to recognise the
inverse across the de-realization, by the same route as the identity: an arrow of a groupoid
which composes with a given arrow to the identity at its source is its inverse. -/
theorem restrictionInversePair_comp_restrictionComposition (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) :
    restrictionInversePair G p ≫ restrictionComposition G p =
      AlgebraicGeometry.restrictionSource G p ≫ restrictionIdentity G p := by
  have hidsrc : (AlgebraicGeometry.restrictionSource G p ≫ restrictionIdentity G p) ≫
      AlgebraicGeometry.restrictionSource G p = AlgebraicGeometry.restrictionSource G p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => AlgebraicGeometry.restrictionSource G p ≫ k)
        (restrictionIdentity_comp_source G p)).trans (Category.comp_id _))
  have hidtgt : (AlgebraicGeometry.restrictionSource G p ≫ restrictionIdentity G p) ≫
      AlgebraicGeometry.restrictionTarget G p = AlgebraicGeometry.restrictionSource G p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => AlgebraicGeometry.restrictionSource G p ≫ k)
        (restrictionIdentity_comp_target G p)).trans (Category.comp_id _))
  have hidarr : (AlgebraicGeometry.restrictionSource G p ≫ restrictionIdentity G p) ≫
      AlgebraicGeometry.restrictionArrowsToArrows G p =
      AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.source ≫ G.identity :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => AlgebraicGeometry.restrictionSource G p ≫ k)
        (restrictionIdentity_comp_arrowsToArrows G p)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ G.identity)
            (AlgebraicGeometry.GroupoidScheme.restriction_condition G p)).trans
            (Category.assoc _ _ _))))
  refine AlgebraicGeometry.GroupoidScheme.restriction_hom_ext G p _ _ ?_ ?_ ?_
  · refine Eq.trans ?_ hidsrc.symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionInversePair G p ≫ k)
      (restrictionComposition_comp_source G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionSource G p)
      (restrictionInversePair_comp_snd G p)).trans ?_
    exact Category.id_comp _
  · refine Eq.trans ?_ hidtgt.symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionInversePair G p ≫ k)
      (restrictionComposition_comp_target G p)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ AlgebraicGeometry.restrictionTarget G p)
      (restrictionInversePair_comp_fst G p)).trans ?_
    exact restrictionInverse_comp_target G p
  · refine Eq.trans ?_ hidarr.symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictionInversePair G p ≫ k)
      (restrictionComposition_comp_arrowsToArrows G p)).trans ?_
    exact restrictionInversePair_comp_ambientComp G p

end Stacks.Groupoids.GroupoidScheme

end
