module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization.RestrictionComposablePairs

/-!
# Comparison of the two compositions of a restriction of a groupoid scheme

`Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_eq`: the space-level composition of
the restriction of a realization, read through the identifications of the composable pairs and
of the arrows, is the composition of the restricted groupoid scheme; and
`Stacks.Groupoids.GroupoidScheme.exists_etale_scheme_of_isRepresentable`, the de-realization of
an étale neighbourhood.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}}

/-- Pullbacks of presheaves on `BigFppfOver C S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_RestrictionCompRealization
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_RestrictionCompRealization
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {X' Y' Z' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ Z') (g : Y' ⟶ Z') :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_RestrictionCompRealization C S hS).has_limit _

/-! ### Comparison of the two compositions of a restriction -/

/-- Reading a composite through an identification: if `α ≫ s` is `ya ≫ ι` and `ι ≫ t` is `yb`,
then `α ≫ s ≫ t` is `ya ≫ yb`. -/
private theorem comp_comp_eq_of_comp_eq {D : Type*} [Category D] {A B E F A' : D} {α : A ⟶ B}
    {s : B ⟶ E} {ya : A ⟶ A'} {ι : A' ⟶ E} {t : E ⟶ F} {yb : A' ⟶ F} (h₁ : α ≫ s = ya ≫ ι)
    (h₂ : ι ≫ t = yb) : α ≫ s ≫ t = ya ≫ yb := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- The Yoneda images of composable morphisms of schemes of the site compose to the Yoneda image
of the composite. -/
private theorem yoneda_map_schemeSiteMap_comp_eq (C : BigFppfSite.{u}) (hS : C.Contains S)
    {X Y Z : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left) (hZ : C.Contains Z.left)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    yoneda.map (schemeSiteMap C hS hX hY f) ≫ yoneda.map (schemeSiteMap C hS hY hZ g) =
      yoneda.map (schemeSiteMap C hS hX hZ (f ≫ g)) := by
  rw [schemeSiteMap_comp C hS hX hY hZ, yoneda.map_comp]

/-- The source of the space-level composite of a composable pair of arrows of a restriction,
read through the identification of the composable pairs and that of the arrows, is the source of
the arrow composed first.

This is the field `hom_source` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.RestrictionCompositionData`, transported along
`Stacks.Groupoids.GroupoidScheme.composablePairsRealizationIso_hom_comp_snd` and
`Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso_hom_comp_source`. -/
theorem restrictionComp_realization_comp_source (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionComp (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hCP hRA (composablePairsSnd G p)) ≫
        yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) := by
  exact (congrArg (_ ≫ ·) (congrArg (·.hom) (GroupoidInAlgebraicSpaces.restrictionCompositionData
      (G.realization C hS hU hR hP) (realizationMap G C hS hU hR hP hX p)).hom_source)).trans
    (comp_comp_eq_of_comp_eq
      (composablePairsRealizationIso_hom_comp_snd G C hS hU hR hP hX p hA hB hRA hCP)
      (restrictionArrowsRealizationIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA))

/-- The target of the space-level composite of a composable pair of arrows of a restriction,
read through the identification of the composable pairs and that of the arrows, is the target of
the arrow composed last.

This is the field `hom_target` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.RestrictionCompositionData`, transported along
`Stacks.Groupoids.GroupoidScheme.composablePairsRealizationIso_hom_comp_fst` and
`Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso_hom_comp_target`. -/
theorem restrictionComp_realization_comp_target (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionComp (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hCP hRA (composablePairsFst G p)) ≫
        yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p)) := by
  exact (congrArg (_ ≫ ·) (congrArg (·.hom) (GroupoidInAlgebraicSpaces.restrictionCompositionData
      (G.realization C hS hU hR hP) (realizationMap G C hS hU hR hP hX p)).hom_target)).trans
    (comp_comp_eq_of_comp_eq
      (composablePairsRealizationIso_hom_comp_fst G C hS hU hR hP hX p hA hB hRA hCP)
      (restrictionArrowsRealizationIso_hom_comp_target G C hS hU hR hP hX p hA hB hRA))

/-- The arrow of `G` underlying the first component of a composable pair of the restricted
realization, read through the two identifications: it is the Yoneda image of the first projection
of the scheme of composable pairs followed by the projection to the ambient arrow scheme. -/
theorem composablePairsRealizationIso_comp_underlyingFst (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)
    {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.fiberProductFst
            (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
              (realizationMap G C hS hU hR hP hX p))
            (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
              (realizationMap G C hS hU hR hP hX p))).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hCP hR
        (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)) := by
  exact (comp_comp_eq_of_comp_eq
    (composablePairsRealizationIso_hom_comp_fst G C hS hU hR hP hX p hA hB hRA hCP)
    (restrictionArrowsRealizationIso_hom_comp_arrowsToArrows
      G C hS hU hR hP hX p hA hB hRA)).trans
    (yoneda_map_schemeSiteMap_comp_eq C hS hCP hRA hR _ _)

/-- The arrow of `G` underlying the second component of a composable pair of the restricted
realization, read through the two identifications: it is the Yoneda image of the second projection
of the scheme of composable pairs followed by the projection to the ambient arrow scheme. -/
theorem composablePairsRealizationIso_comp_underlyingSnd (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)
    {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.fiberProductSnd
            (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
              (realizationMap G C hS hU hR hP hX p))
            (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
              (realizationMap G C hS hU hR hP hX p))).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hCP hR
        (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)) := by
  exact (comp_comp_eq_of_comp_eq
    (composablePairsRealizationIso_hom_comp_snd G C hS hU hR hP hX p hA hB hRA hCP)
    (restrictionArrowsRealizationIso_hom_comp_arrowsToArrows
      G C hS hU hR hP hX p hA hB hRA)).trans
    (yoneda_map_schemeSiteMap_comp_eq C hS hCP hRA hR _ _)

/-- The arrow of `G` underlying the space-level composite of a composable pair of arrows of a
restriction, read through the identification of the composable pairs and that of the arrows, is
the ambient composite.

This is the third and last clause of the comparison.  The space-level composite's underlying
arrow is the field `hom_comp` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.RestrictionCompositionData`, which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionCompositionData_underlying_eq` presents
as the pair of the two underlying arrows followed by the ambient composition; the ambient
composition of a realization is `Stacks.Groupoids.GroupoidScheme.realization_comp`.  Both sides
are then morphisms into the space represented by the scheme of composable pairs of `G`, and
agree because their two components do. -/
theorem restrictionComp_realization_comp_arrowsToArrows (G : GroupoidScheme S)
    (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)
    {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionComp (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hCP hR (restrictionAmbientComp G p)) := by
  have hcomp : ((GroupoidInAlgebraicSpaces.restrictionCompositionData
        (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom).hom ≫
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom =
      (GroupoidInAlgebraicSpaces.restrictionUnderlyingLift (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom ≫
        (G.realization C hS hU hR hP).comp.hom :=
    (congrArg (fun f => f.hom)
      (GroupoidInAlgebraicSpaces.restrictionCompositionData (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom_comp).trans
      (congrArg (fun f => f.hom)
        (GroupoidInAlgebraicSpaces.restrictionCompositionData_underlying_eq
          (G.realization C hS hU hR hP) (realizationMap G C hS hU hR hP hX p)))
  have hinvfst := (Iso.inv_comp_eq _).2
    (yonedaSchemePullbackIso_hom_fst C hS hR hR hU G.source G.target hP).symm
  have hinvsnd := (Iso.inv_comp_eq _).2
    (yonedaSchemePullbackIso_hom_snd C hS hR hR hU G.source G.target hP).symm
  have key : (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
      (GroupoidInAlgebraicSpaces.restrictionUnderlyingLift (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hCP hP (restrictionAmbientLift G p)) ≫
        (yonedaSchemePullbackIso C hS hR hR hU G.source G.target hP).inv := by
    refine pullback.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (congrArg (·.hom)
        (GroupoidInAlgebraicSpaces.restrictionUnderlyingLift_comp_fst
          (G.realization C hS hU hR hP) (realizationMap G C hS hU hR hP hX p)))).trans ?_)
      refine (composablePairsRealizationIso_comp_underlyingFst
        G C hS hU hR hP hX p hA hB hRA hCP).trans ?_
      rw [← restrictionAmbientLift_comp_fst,
        ← yoneda_map_schemeSiteMap_comp_eq C hS hCP hP hR]
      exact (congrArg (_ ≫ ·) hinvfst).symm.trans (Category.assoc _ _ _).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (congrArg (·.hom)
        (GroupoidInAlgebraicSpaces.restrictionUnderlyingLift_comp_snd
          (G.realization C hS hU hR hP) (realizationMap G C hS hU hR hP hX p)))).trans ?_)
      refine (composablePairsRealizationIso_comp_underlyingSnd
        G C hS hU hR hP hX p hA hB hRA hCP).trans ?_
      rw [← restrictionAmbientLift_comp_snd,
        ← yoneda_map_schemeSiteMap_comp_eq C hS hCP hP hR]
      exact (congrArg (_ ≫ ·) hinvsnd).symm.trans (Category.assoc _ _ _).symm
  refine (congrArg (_ ≫ ·) ((congrArg (·.hom) (GroupoidInAlgebraicSpaces.restrictionCompositionData
      (G.realization C hS hU hR hP) (realizationMap G C hS hU hR hP hX p)).hom_comp).trans
    (congrArg (·.hom) (GroupoidInAlgebraicSpaces.restrictionCompositionData_underlying_eq
      (G.realization C hS hU hR hP) (realizationMap G C hS hU hR hP hX p))))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans ?_)
  rw [realization_comp]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)).trans ?_)
  exact yoneda_map_schemeSiteMap_comp_eq C hS hCP hP hR _ _

/-- **De-realization of the composition of a restriction.**  The composition of the restriction
of the realization of a groupoid scheme along a represented morphism is, read through the
identification of the composable pairs and that of the arrows, the Yoneda image of the
composition of the restriction of the groupoid scheme.

This is the piece the de-realization of this file left open.  The space-level composition is
de-realized by faithfulness of Yoneda; the morphism of schemes it comes from has the source, the
target and the underlying arrow of a composite, by
`Stacks.Groupoids.GroupoidScheme.restrictionComp_realization_comp_source`, `_comp_target` and
`_comp_arrowsToArrows`; and those three identities determine the composition, by
`Stacks.Groupoids.GroupoidScheme.eq_restrictionComposition_of_spec`. -/
theorem restrictionComp_realization_eq (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left)
    (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)
    {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
    (hA : C.Contains (pullback p G.target).left)
    (hB : C.Contains (pullback G.source p).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
    (hCP : C.Contains (restrictionComposablePairs G p).left) :
    (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionComp (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom =
      yoneda.map (schemeSiteMap C hS hCP hRA (restrictionComposition G p)) ≫
        (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom := by
  have hex : ∀ g : yoneda.obj (schemeSiteObject C hS hCP) ⟶ yoneda.obj (schemeSiteObject C hS hRA),
      ∃ c : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p,
        yoneda.map (schemeSiteMap C hS hCP hRA c) = g := fun g =>
    ⟨(siteToOver C hS).map (yoneda.preimage g), by
      change yoneda.map (yoneda.preimage g) = g
      exact yoneda.map_preimage g⟩
  obtain ⟨c, hc⟩ := hex (((composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
      (GroupoidInAlgebraicSpaces.restrictionComp (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom) ≫
    (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).inv)
  replace hc := (Iso.eq_comp_inv _).1 hc
  -- a morphism out of the restricted arrows is determined by its Yoneda image through `c`
  have step : ∀ {Z : Over S} (hZ : C.Contains Z.left)
      (f : AlgebraicGeometry.restrictionArrows G p ⟶ Z) (k : restrictionComposablePairs G p ⟶ Z)
      (R : _ ⟶ yoneda.obj (schemeSiteObject C hS hZ)),
      (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫ R =
        yoneda.map (schemeSiteMap C hS hRA hZ f) →
      (composablePairsRealizationIso G C hS hU hR hP hX p hA hB hRA hCP).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionComp (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom ≫ R =
        yoneda.map (schemeSiteMap C hS hCP hZ k) → c ≫ f = k := by
    intro Z hZ f k R hf hk
    refine schemeSiteMap_yoneda_injective C hS hCP hZ ?_
    rw [schemeSiteMap_comp C hS hCP hRA hZ, yoneda.map_comp, ← hf]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ R) hc).trans ((Category.assoc _ _ _).trans hk))
  have hceq : c = restrictionComposition G p :=
    eq_restrictionComposition_of_spec G p c
      (step hX _ _ _ (restrictionArrowsRealizationIso_hom_comp_source
        G C hS hU hR hP hX p hA hB hRA)
        ((restrictionComp_realization_comp_source G C hS hU hR hP hX p hA hB hRA hCP).trans
          (yoneda_map_schemeSiteMap_comp_eq C hS hCP hRA hX _ _)))
      (step hX _ _ _ (restrictionArrowsRealizationIso_hom_comp_target
        G C hS hU hR hP hX p hA hB hRA)
        ((restrictionComp_realization_comp_target G C hS hU hR hP hX p hA hB hRA hCP).trans
          (yoneda_map_schemeSiteMap_comp_eq C hS hCP hRA hX _ _)))
      (step hR _ _ _ (restrictionArrowsRealizationIso_hom_comp_arrowsToArrows
        G C hS hU hR hP hX p hA hB hRA)
        (restrictionComp_realization_comp_arrowsToArrows G C hS hU hR hP hX p hA hB hRA hCP))
  rw [hceq] at hc
  exact hc.symm

/-- **De-realization of an étale neighbourhood.**  An algebraic space with representable
underlying presheaf, étale over the object space of the realization of a groupoid scheme, is the
space represented by a scheme over `S` which is étale over the object scheme. -/
theorem exists_etale_scheme_of_isRepresentable (G : GroupoidScheme S) (C : BigFppfSite.{u})
    (hS : C.Contains S) (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left) (U' : AlgebraicSpaces C S hS)
    (hU' : U'.obj.IsRepresentable) (g : U' ⟶ (G.realization C hS hU hR hP).objects)
    (hg : IsEtale C S hS g.hom) :
    ∃ (Y : Over S) (hY : C.Contains Y.left) (q : Y ⟶ G.objects)
      (e : yoneda.obj (schemeSiteObject C hS hY) ≅ U'.obj),
      AlgebraicGeometry.Etale q.left ∧
        e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hY hU q) := by
  have hspec := derealize_spec C hS U'.obj hU g.hom
  have hpre : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf
      (yoneda.map (schemeSiteMap C hS (contains_representingScheme C hS U'.obj) hU
        (derealize C hS U'.obj hU g.hom))) := by
    rw [hspec]
    exact presheaf_etale_of_isEtale_iso C hS U'.obj (representingSchemeIso C hS U'.obj).symm
      g.hom hg
  have hetale := (presheaf_yoneda_map_iff C S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
    (schemeSiteMap C hS (contains_representingScheme C hS U'.obj) hU
      (derealize C hS U'.obj hU g.hom))).1 hpre
  rw [toScheme_map_schemeSiteMap_eq] at hetale
  exact ⟨representingScheme C hS U'.obj, contains_representingScheme C hS U'.obj,
    derealize C hS U'.obj hU g.hom, (representingSchemeIso C hS U'.obj).symm, hetale, hspec.symm⟩

end Stacks.Groupoids.GroupoidScheme

end
