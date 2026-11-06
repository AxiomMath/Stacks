module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment

/-!
# De-realizing the arrows of a restriction along a morphism out of a representable space

`Stacks.Groupoids.GroupoidScheme.restrictionArrowsRealizationIso` identifies the arrow space of
the restriction of the realization of a groupoid scheme along a *represented* morphism with the
space represented by the arrow scheme of the restriction of the groupoid scheme.  The étale
neighbourhoods produced by Stacks 04RW and Stacks 04RY are not represented morphisms on the
nose: they are morphisms `g : U' ⟶ U` out of an algebraic space `U'` which is merely *asserted*
to be representable, and the comparison with a scheme over `S` is an isomorphism
`e : yoneda.obj X' ≅ U'` together with the identification `e ≫ g = yoneda.map q` of
`Stacks.Groupoids.GroupoidScheme.exists_etale_scheme_of_isRepresentable`.

This file gives the same identification in that situation.  The three projections behave as
before except that the source and the target, which land in `U'` rather than in the represented
space, acquire the comparison isomorphism.

It also records that a big fppf site contains the schemes the comparison is stated with — the
two intermediate fibre products and the arrow scheme of the restriction — so that none of them
has to be carried as a hypothesis.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.restrictionArrowsIsoOfIso`: the identification of the arrow
  space of the restriction of a realization along such a `g` with the space represented by the
  arrow scheme of the restriction of the groupoid scheme along `q`.

## Main results

* `Stacks.Groupoids.GroupoidScheme.contains_pullback_target_left`,
  `contains_pullback_source_left` and `contains_restrictionArrows_left`: the site contains the
  three schemes the comparison names.
* `Stacks.Groupoids.GroupoidScheme.restrictionArrowsIsoOfIso_hom_comp_arrowsToArrows`: the
  identification carries the projection to the ambient arrow space to the Yoneda image of the
  corresponding projection of arrow schemes.
* `Stacks.Groupoids.GroupoidScheme.restrictionArrowsIsoOfIso_hom_comp_source` and
  `restrictionArrowsIsoOfIso_hom_comp_target`: it carries the source and the target to the
  Yoneda images of those of the restricted groupoid scheme, followed by the comparison
  isomorphism.

## Implementation notes

The construction is the one of `restrictionArrowsRealizationIso`, with one extra transport on
each of the two inner fibre products.  Each of those is an instance of
`AlgebraicGeometry.Space.isPullback_comp_iso`: a fibre product along `e ≫ g` is a fibre product
along `g`, because base change along an isomorphism is an isomorphism, and the comparison of the
two is recorded by `Stacks.Groupoids.GroupoidScheme.targetLegIso` and `sourceLegIso`.  The outer
square is then the one of `Stacks.Groupoids.GroupoidScheme.isPullback_restrictionArrowsSite`
read on the transported cospan, again by `isPullback_comp_iso`, and both it and the chosen fibre
product are cartesian on that cospan, so their vertices agree by
`CategoryTheory.IsPullback.isoIsPullback`.

The containment statements use that the cutoff of a big fppf site is a strong prelimit cardinal,
through `AlgebraicGeometry.BigFppfSite.contains_pullback_left`.  They are what makes the
de-realization usable from a statement which carries only the site containments of the object,
arrow and composable-pair schemes.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace Stacks.Groupoids

/-! ### Base change along an isomorphism -/

section Limits

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- A fibre product of `f` with `g` is a fibre product of `q` with `g` whenever `q` factors as
an isomorphism followed by `f`: base change along an isomorphism is an isomorphism. -/
theorem isPullback_isoLeft {V W Y Z : 𝒞} (i : V ≅ W) (q : V ⟶ Y) (f : W ⟶ Y) (g : Z ⟶ Y)
    (hq : i.hom ≫ f = q) [HasPullback f g] :
    IsPullback (pullback.fst f g ≫ i.inv) (pullback.snd f g) q g := by
  subst hq
  have h := AlgebraicGeometry.Space.isPullback_comp_iso
    (IsPullback.of_hasPullback f g) i (Iso.refl Z)
  simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp] using h

/-- The same with the isomorphism on the other leg of the cospan. -/
theorem isPullback_isoRight {V W Y Z : 𝒞} (i : V ≅ W) (f : Z ⟶ Y) (q : V ⟶ Y) (g : W ⟶ Y)
    (hq : i.hom ≫ g = q) [HasPullback f g] :
    IsPullback (pullback.fst f g) (pullback.snd f g ≫ i.inv) f q := by
  subst hq
  have h := AlgebraicGeometry.Space.isPullback_comp_iso
    (IsPullback.of_hasPullback f g) (Iso.refl Z) i
  simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp] using h

/-- **Base change along an isomorphism on the left.** -/
noncomputable def pullbackIsoOfIsoLeft {V W Y Z : 𝒞} (i : V ≅ W) (q : V ⟶ Y) (f : W ⟶ Y)
    (g : Z ⟶ Y) (hq : i.hom ≫ f = q) [HasPullback q g] [HasPullback f g] :
    pullback q g ≅ pullback f g :=
  (IsPullback.of_hasPullback q g).isoIsPullback _ _ (isPullback_isoLeft i q f g hq)

theorem pullbackIsoOfIsoLeft_hom_fst_comp_inv {V W Y Z : 𝒞} (i : V ≅ W) (q : V ⟶ Y)
    (f : W ⟶ Y) (g : Z ⟶ Y) (hq : i.hom ≫ f = q) [HasPullback q g] [HasPullback f g] :
    (pullbackIsoOfIsoLeft i q f g hq).hom ≫ pullback.fst f g ≫ i.inv = pullback.fst q g :=
  IsPullback.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback q g)
    (isPullback_isoLeft i q f g hq)

theorem pullbackIsoOfIsoLeft_hom_fst {V W Y Z : 𝒞} (i : V ≅ W) (q : V ⟶ Y) (f : W ⟶ Y)
    (g : Z ⟶ Y) (hq : i.hom ≫ f = q) [HasPullback q g] [HasPullback f g] :
    (pullbackIsoOfIsoLeft i q f g hq).hom ≫ pullback.fst f g = pullback.fst q g ≫ i.hom := by
  rw [← pullbackIsoOfIsoLeft_hom_fst_comp_inv i q f g hq, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem pullbackIsoOfIsoLeft_hom_snd {V W Y Z : 𝒞} (i : V ≅ W) (q : V ⟶ Y) (f : W ⟶ Y)
    (g : Z ⟶ Y) (hq : i.hom ≫ f = q) [HasPullback q g] [HasPullback f g] :
    (pullbackIsoOfIsoLeft i q f g hq).hom ≫ pullback.snd f g = pullback.snd q g :=
  IsPullback.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback q g)
    (isPullback_isoLeft i q f g hq)

/-- **Base change along an isomorphism on the right.** -/
noncomputable def pullbackIsoOfIsoRight {V W Y Z : 𝒞} (i : V ≅ W) (f : Z ⟶ Y) (q : V ⟶ Y)
    (g : W ⟶ Y) (hq : i.hom ≫ g = q) [HasPullback f q] [HasPullback f g] :
    pullback f q ≅ pullback f g :=
  (IsPullback.of_hasPullback f q).isoIsPullback _ _ (isPullback_isoRight i f q g hq)

theorem pullbackIsoOfIsoRight_hom_fst {V W Y Z : 𝒞} (i : V ≅ W) (f : Z ⟶ Y) (q : V ⟶ Y)
    (g : W ⟶ Y) (hq : i.hom ≫ g = q) [HasPullback f q] [HasPullback f g] :
    (pullbackIsoOfIsoRight i f q g hq).hom ≫ pullback.fst f g = pullback.fst f q :=
  IsPullback.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback f q)
    (isPullback_isoRight i f q g hq)

theorem pullbackIsoOfIsoRight_hom_snd_comp_inv {V W Y Z : 𝒞} (i : V ≅ W) (f : Z ⟶ Y)
    (q : V ⟶ Y) (g : W ⟶ Y) (hq : i.hom ≫ g = q) [HasPullback f q] [HasPullback f g] :
    (pullbackIsoOfIsoRight i f q g hq).hom ≫ pullback.snd f g ≫ i.inv = pullback.snd f q :=
  IsPullback.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f q)
    (isPullback_isoRight i f q g hq)

theorem pullbackIsoOfIsoRight_hom_snd {V W Y Z : 𝒞} (i : V ≅ W) (f : Z ⟶ Y) (q : V ⟶ Y)
    (g : W ⟶ Y) (hq : i.hom ≫ g = q) [HasPullback f q] [HasPullback f g] :
    (pullbackIsoOfIsoRight i f q g hq).hom ≫ pullback.snd f g =
      pullback.snd f q ≫ i.hom := by
  rw [← pullbackIsoOfIsoRight_hom_snd_comp_inv i f q g hq, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Limits

end Stacks.Groupoids

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
instance (priority := high) hasPullbacks_presheaf_restrictionArrows :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

instance (priority := high) hasPullback_presheaf_restrictionArrows
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_restrictionArrows C hS).has_limit _

/-! ### The site contains the schemes of the comparison -/

include hR in
/-- The site contains the fibre product of the restricting morphism with the target. -/
theorem contains_pullback_target_left {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) : C.Contains (pullback p G.target).left :=
  C.contains_pullback_left p G.target hX hR

include hR in
/-- The site contains the fibre product of the source with the restricting morphism. -/
theorem contains_pullback_source_left {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) : C.Contains (pullback G.source p).left :=
  C.contains_pullback_left G.source p hR hX

include hR in
/-- The site contains the arrow scheme of a restriction of a groupoid scheme it contains. -/
theorem contains_restrictionArrows_left {X : Over S} (hX : C.Contains X.left)
    (p : X ⟶ G.objects) : C.Contains (AlgebraicGeometry.restrictionArrows G p).left :=
  C.contains_pullback_left (pullback.snd p G.target) (pullback.fst G.source p)
    (contains_pullback_target_left G C hR hX p) (contains_pullback_source_left G C hR hX p)

/-! ### The two inner fibre products -/

variable (hP : C.Contains (pullback G.source G.target).left) {X : Over S}
  (hX : C.Contains X.left) (p : X ⟶ G.objects) (U' : AlgebraicSpaces C S hS)
  (g : U' ⟶ (G.realization C hS hU hR hP).objects)
  (e : yoneda.obj (schemeSiteObject C hS hX) ≅ U'.obj)
  (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hX hU p))

include he in
/-- The comparison of the two readings of the fibre product on the target side. -/
noncomputable def targetLegIso :
    pullback (yoneda.map (schemeSiteMap C hS hX hU p))
        (yoneda.map (schemeSiteMap C hS hR hU G.target)) ≅
      pullback g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) :=
  Stacks.Groupoids.pullbackIsoOfIsoLeft e (yoneda.map (schemeSiteMap C hS hX hU p)) g.hom
    (yoneda.map (schemeSiteMap C hS hR hU G.target)) he

theorem targetLegIso_hom_fst :
    (targetLegIso G C hS hU hR hP hX p U' g e he).hom ≫
        pullback.fst g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) =
      pullback.fst (yoneda.map (schemeSiteMap C hS hX hU p))
        (yoneda.map (schemeSiteMap C hS hR hU G.target)) ≫ e.hom :=
  Stacks.Groupoids.pullbackIsoOfIsoLeft_hom_fst e _ g.hom _ he

theorem targetLegIso_hom_snd :
    (targetLegIso G C hS hU hR hP hX p U' g e he).hom ≫
        pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) =
      pullback.snd (yoneda.map (schemeSiteMap C hS hX hU p))
        (yoneda.map (schemeSiteMap C hS hR hU G.target)) :=
  Stacks.Groupoids.pullbackIsoOfIsoLeft_hom_snd e _ g.hom _ he

include he in
/-- The comparison of the two readings of the fibre product on the source side. -/
noncomputable def sourceLegIso :
    pullback (yoneda.map (schemeSiteMap C hS hR hU G.source))
        (yoneda.map (schemeSiteMap C hS hX hU p)) ≅
      pullback (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom :=
  Stacks.Groupoids.pullbackIsoOfIsoRight e (yoneda.map (schemeSiteMap C hS hR hU G.source))
    (yoneda.map (schemeSiteMap C hS hX hU p)) g.hom he

theorem sourceLegIso_hom_fst :
    (sourceLegIso G C hS hU hR hP hX p U' g e he).hom ≫
        pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom =
      pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source))
        (yoneda.map (schemeSiteMap C hS hX hU p)) :=
  Stacks.Groupoids.pullbackIsoOfIsoRight_hom_fst e _ _ g.hom he

theorem sourceLegIso_hom_snd :
    (sourceLegIso G C hS hU hR hP hX p U' g e he).hom ≫
        pullback.snd (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom =
      pullback.snd (yoneda.map (schemeSiteMap C hS hR hU G.source))
        (yoneda.map (schemeSiteMap C hS hX hU p)) ≫ e.hom :=
  Stacks.Groupoids.pullbackIsoOfIsoRight_hom_snd e _ _ g.hom he

/-! ### The outer fibre product -/

variable (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)

/-- The comparison on the target side, read from the represented fibre product. -/
noncomputable def targetLegCompare :
    pullback g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) ≅
      yoneda.obj (schemeSiteObject C hS hA) :=
  (targetLegIso G C hS hU hR hP hX p U' g e he).symm ≪≫
    yonedaSchemePullbackIso C hS hX hR hU p G.target hA

/-- The comparison on the source side, read from the represented fibre product. -/
noncomputable def sourceLegCompare :
    pullback (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom ≅
      yoneda.obj (schemeSiteObject C hS hB) :=
  (sourceLegIso G C hS hU hR hP hX p U' g e he).symm ≪≫
    yonedaSchemePullbackIso C hS hR hX hU G.source p hB

/-- The inverse of the target comparison carries the second projection to the Yoneda image of the
second projection of the represented fibre product. -/
private theorem targetLegCompare_inv_comp_snd :
    (targetLegCompare G C hS hU hR hP hX p U' g e he hA).inv ≫
      pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) =
      yoneda.map (schemeSiteMap C hS hA hR (pullback.snd p G.target)) := by
  rw [targetLegCompare, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    targetLegIso_hom_snd G C hS hU hR hP hX p U' g e he, Iso.inv_comp_eq]
  exact (yonedaSchemePullbackIso_hom_snd C hS hX hR hU p G.target hA).symm

/-- The inverse of the source comparison carries the first projection to the Yoneda image of the
first projection of the represented fibre product. -/
private theorem sourceLegCompare_inv_comp_fst :
    (sourceLegCompare G C hS hU hR hP hX p U' g e he hB).inv ≫
      pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom =
      yoneda.map (schemeSiteMap C hS hB hR (pullback.fst G.source p)) := by
  rw [sourceLegCompare, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    sourceLegIso_hom_fst G C hS hU hR hP hX p U' g e he, Iso.inv_comp_eq]
  exact (yonedaSchemePullbackIso_hom_fst C hS hR hX hU G.source p hB).symm

include he in
/-- The cartesian square of `Stacks.Groupoids.GroupoidScheme.isPullback_restrictionArrowsSite`,
read on the cospan which defines the arrow space of the restriction along `g`. -/
theorem isPullback_restrictionArrowsOfIso :
    IsPullback
      (yoneda.map (schemeSiteMap C hS hRA hA (restrictionArrowsFst G p)) ≫
        (targetLegCompare G C hS hU hR hP hX p U' g e he hA).inv)
      (yoneda.map (schemeSiteMap C hS hRA hB (restrictionArrowsSnd G p)) ≫
        (sourceLegCompare G C hS hU hR hP hX p U' g e he hB).inv)
      (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
      (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) := by
  have h := isPullback_comp_iso (isPullback_restrictionArrowsSite G C hS hR p hA hB hRA)
    (targetLegCompare G C hS hU hR hP hX p U' g e he hA)
    (sourceLegCompare G C hS hU hR hP hX p U' g e he hB)
  rwa [← (Iso.inv_comp_eq _).1 (targetLegCompare_inv_comp_snd G C hS hU hR hP hX p U' g e he hA),
    ← (Iso.inv_comp_eq _).1 (sourceLegCompare_inv_comp_fst G C hS hU hR hP hX p U' g e he hB)]
    at h

/-- **De-realization of the arrows of a restriction along a morphism out of a representable
space.**  The arrow space of the restriction of the realization of a groupoid scheme along a
morphism out of an algebraic space identified with a represented one is the space represented by
the arrow scheme of the restriction of the groupoid scheme. -/
noncomputable def restrictionArrowsIsoOfIso :
    yoneda.obj (schemeSiteObject C hS hRA) ≅
      pullback (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
        (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) :=
  (isPullback_restrictionArrowsOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- The arrow space of the restriction of a realization along such a `g` is that iterated fibre
product. -/
theorem restrictionArrows_obj_ofIso :
    (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP) g).obj =
      pullback (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
        (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) :=
  rfl

theorem restrictionArrowsIsoOfIso_hom_comp_fst :
    (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
        pullback.fst (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
          (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) =
      yoneda.map (schemeSiteMap C hS hRA hA (restrictionArrowsFst G p)) ≫
        (targetLegCompare G C hS hU hR hP hX p U' g e he hA).inv :=
  IsPullback.isoIsPullback_hom_fst _ _
    (isPullback_restrictionArrowsOfIso G C hS hU hR hP hX p U' g e he hA hB hRA)
    (IsPullback.of_hasPullback _ _)

theorem restrictionArrowsIsoOfIso_hom_comp_snd :
    (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
        pullback.snd (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
          (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) =
      yoneda.map (schemeSiteMap C hS hRA hB (restrictionArrowsSnd G p)) ≫
        (sourceLegCompare G C hS hU hR hP hX p U' g e he hB).inv :=
  IsPullback.isoIsPullback_hom_snd _ _
    (isPullback_restrictionArrowsOfIso G C hS hU hR hP hX p U' g e he hA hB hRA)
    (IsPullback.of_hasPullback _ _)

/-! ### The three projections -/

include he in
/-- **De-realization of the projection to the ambient arrows.** -/
theorem restrictionArrowsIsoOfIso_hom_comp_arrowsToArrows :
    (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom =
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p)) := by
  have key : (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
      pullback.fst (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
          (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) ≫
      pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) =
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p)) := by
    rw [← Category.assoc, restrictionArrowsIsoOfIso_hom_comp_fst, Category.assoc,
      targetLegCompare_inv_comp_snd G C hS hU hR hP hX p U' g e he hA, ← yoneda.map_comp]
    exact congrArg (fun k => yoneda.map k) (schemeSiteMap_comp C hS hRA hA hR
      (restrictionArrowsFst G p) (pullback.snd p G.target)).symm
  exact key

include he in
/-- **De-realization of the source of a restriction**, up to the comparison isomorphism. -/
theorem restrictionArrowsIsoOfIso_hom_comp_source :
    (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP) g).hom =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) ≫
        e.hom := by
  have hleg : (sourceLegCompare G C hS hU hR hP hX p U' g e he hB).inv ≫
      pullback.snd (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom =
      yoneda.map (schemeSiteMap C hS hB hX (pullback.snd G.source p)) ≫ e.hom := by
    rw [sourceLegCompare, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      sourceLegIso_hom_snd G C hS hU hR hP hX p U' g e he, Iso.inv_comp_eq, ← Category.assoc,
      yonedaSchemePullbackIso_hom_snd C hS hR hX hU G.source p hB]
  have key : (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
      pullback.snd (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
          (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) ≫
      pullback.snd (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) ≫
        e.hom := by
    rw [← Category.assoc, restrictionArrowsIsoOfIso_hom_comp_snd, Category.assoc, hleg,
      ← Category.assoc, ← yoneda.map_comp]
    exact congrArg (fun k => yoneda.map k ≫ e.hom) (schemeSiteMap_comp C hS hRA hB hX
      (restrictionArrowsSnd G p) (pullback.snd G.source p)).symm
  exact key

include he in
/-- **De-realization of the target of a restriction**, up to the comparison isomorphism. -/
theorem restrictionArrowsIsoOfIso_hom_comp_target :
    (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
        (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP) g).hom =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p)) ≫
        e.hom := by
  have hleg : (targetLegCompare G C hS hU hR hP hX p U' g e he hA).inv ≫
      pullback.fst g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) =
      yoneda.map (schemeSiteMap C hS hA hX (pullback.fst p G.target)) ≫ e.hom := by
    rw [targetLegCompare, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      targetLegIso_hom_fst G C hS hU hR hP hX p U' g e he, Iso.inv_comp_eq, ← Category.assoc,
      yonedaSchemePullbackIso_hom_fst C hS hX hR hU p G.target hA]
  have key : (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫
      pullback.fst (pullback.snd g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)))
          (pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source)) g.hom) ≫
      pullback.fst g.hom (yoneda.map (schemeSiteMap C hS hR hU G.target)) =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p)) ≫
        e.hom := by
    rw [← Category.assoc, restrictionArrowsIsoOfIso_hom_comp_fst, Category.assoc, hleg,
      ← Category.assoc, ← yoneda.map_comp]
    exact congrArg (fun k => yoneda.map k ≫ e.hom) (schemeSiteMap_comp C hS hRA hA hX
      (restrictionArrowsFst G p) (pullback.fst p G.target)).symm
  exact key

end Stacks.Groupoids.GroupoidScheme

end
