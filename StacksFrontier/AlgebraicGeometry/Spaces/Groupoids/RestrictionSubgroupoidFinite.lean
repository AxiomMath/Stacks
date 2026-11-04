module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionArrowSections
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable

/-!
# Finiteness of the source and the target on the open subscheme cut out by an open subspace

`Stacks.Groupoids.GroupoidScheme.arrowOpens` transports an open subspace `A` of the arrow space
of the restriction of the realization of a groupoid scheme to an open subscheme of the arrow
scheme of the restriction of the groupoid scheme.  This file transports the two finiteness
conditions of an open finite subgroupoid across the same identification: if the source of the
restricted realization is finite on `A`, then the source of the restriction of the groupoid
scheme is finite on that open subscheme, and likewise for the target.

Together with
`Stacks.Groupoids.GroupoidScheme.mem_iff_forall_mem_arrowOpens` this turns the data of an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid` of the restricted
realization into the data of an open subscheme of the arrow scheme of the restriction with
finite source and target, which is the form the scheme-level splitting statements consume.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isFinite_arrowOpens_source`: the source of the restriction of
  the groupoid scheme is finite on the open subscheme cut out by an open subspace on which the
  source of the restricted realization is finite.
* `Stacks.Groupoids.GroupoidScheme.isFinite_arrowOpens_target`: the same for the target.

## Implementation notes

The open subscheme is by definition `AlgebraicGeometry.Space.opensOfOpenSubspace` of the
inverse image `A'` of `A` along the comparison isomorphism
`Stacks.Groupoids.GroupoidScheme.restrictionArrowsIsoOfIso`, so
`AlgebraicGeometry.Space.subspaceOfOpens_opensOfOpenSubspace` says that `A'` is the subspace cut
out by that open, and `AlgebraicGeometry.Space.range_yoneda_map_eq_subspaceOfOpens` says that
subspace is the image of the Yoneda image of the open immersion
`AlgebraicGeometry.BigFppfOver.openSubHom` of the open subscheme.  Hence `A'` is isomorphic to
the presheaf represented by `AlgebraicGeometry.BigFppfOver.openSubObj`, compatibly with the two
inclusions, by `AlgebraicGeometry.Space.rangeIsoOfMono`.

Finiteness is then moved along three isomorphisms — the identification of `A` with `A'`
(`AlgebraicGeometry.Space.subfunctorIsoPreimage`), the identification of `A'` with the
represented presheaf, and the comparison `e` of the target — using
`AlgebraicGeometry.Space.isFinite_of_sourceIso` and
`AlgebraicGeometry.Space.isFinite_postcomp_iso`, and the resulting finite represented morphism
is read on schemes by `AlgebraicGeometry.Space.finite_of_isFinite_yoneda_map`.

The equality of subfunctors is used to produce the isomorphism with the represented presheaf
through an auxiliary universally quantified statement, so that the substitution happens before
the isomorphism is named; rewriting inside the type of an already-named isomorphism is not
type-correct.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

/-! ### Finiteness through an open immersion of the site -/

section Site

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor to schemes takes the inclusion of an open of an object of the big fppf site to
the open immersion of the corresponding open subscheme. -/
theorem toScheme_map_openSubHom (T : BigFppfOver B S hS) (Q : T.left.obj.Opens) :
    (BigFppfOver.toScheme B S hS).map (BigFppfOver.openSubHom B S hS T Q) = Q.ι := rfl

/-- **Finiteness read through an open immersion of the site whose image is the inverse image of
an open subspace.**  Let `R` identify a chart `yoneda.obj V` with an algebraic space carrying an
open subspace `A`, let `sp` be a morphism out of that space which is finite on `A`, and let `i`
be an open immersion of the site whose Yoneda image has as its image exactly the inverse image
of `A` along `R`.  If `R.hom ≫ sp` is a morphism `q` of the chart followed by an isomorphism,
then `q` is finite on the source of `i`. -/
private theorem isFinite_yoneda_map_of_range_eq_preimage
    {F Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W : BigFppfOver B S hS}
    (R : yoneda.obj V ≅ F) (A : Subfunctor F) (sp : F ⟶ Y) (i : W ⟶ V)
    (q : yoneda.obj V ⟶ Z) (d : Z ≅ Y) (hq : R.hom ≫ sp = q ≫ d.hom)
    (hoi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hrange : Subfunctor.range (yoneda.map i) = A.preimage R.hom)
    (hfin : Space.IsFinite B S hS (A.ι ≫ sp)) :
    Space.IsFinite B S hS (yoneda.map i ≫ q) := by
  have hoim : IsOpenImmersion B S hS (yoneda.map i) :=
    (presheaf_yoneda_map_iff B S hS inferInstance i).2 hoi
  have _ : Mono (yoneda.map i) := mono_of_presheaf_isOpenImmersion hoim
  have gen : ∀ Zt : Subfunctor (yoneda.obj V), Subfunctor.range (yoneda.map i) = Zt →
      ∃ j : yoneda.obj W ≅ Zt.toFunctor, j.inv ≫ yoneda.map i = Zt.ι := by
    intro Zt hZt
    subst hZt
    exact ⟨rangeIsoOfMono B S hS (yoneda.map i), rangeIsoOfMono_inv_comp B S hS (yoneda.map i)⟩
  obtain ⟨j, hj⟩ := gen _ hrange
  have hpre : (subfunctorIsoPreimage R.symm A).hom ≫ (A.preimage R.hom).ι = A.ι ≫ R.inv :=
    subfunctorIsoPreimage_hom_ι R.symm A
  have hw : (subfunctorIsoPreimage R.symm A).hom ≫ ((A.preimage R.hom).ι ≫ R.hom ≫ sp) =
      A.ι ≫ sp := by
    rw [← Category.assoc, hpre, Category.assoc, Iso.inv_hom_id_assoc]
  have h1 : Space.IsFinite B S hS ((A.preimage R.hom).ι ≫ R.hom ≫ sp) :=
    isFinite_of_sourceIso B S hS (subfunctorIsoPreimage R.symm A) (A.ι ≫ sp) _ hw hfin
  have hw2 : j.symm.hom ≫ (yoneda.map i ≫ R.hom ≫ sp) =
      (A.preimage R.hom).ι ≫ R.hom ≫ sp := by
    rw [Iso.symm_hom, ← Category.assoc, hj]
  have h2 : Space.IsFinite B S hS (yoneda.map i ≫ R.hom ≫ sp) :=
    isFinite_of_sourceIso B S hS j.symm _ _ hw2 h1
  rw [hq] at h2
  have h3 : Space.IsFinite B S hS ((yoneda.map i ≫ q ≫ d.hom) ≫ d.inv) :=
    isFinite_postcomp_iso B S hS (yoneda.map i ≫ q ≫ d.hom) d.symm h2
  have heq : (yoneda.map i ≫ q ≫ d.hom) ≫ d.inv = yoneda.map i ≫ q := by
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rwa [heq] at h3

end Site

/-! ### The source and the target on the open subscheme -/

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left) {X : Over S}
  (hX : C.Contains X.left) (p : X ⟶ G.objects) (U' : AlgebraicSpaces C S hS)
  (g : U' ⟶ (G.realization C hS hU hR hP).objects)
  (e : yoneda.obj (schemeSiteObject C hS hX) ≅ U'.obj)
  (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hX hU p))
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
  (A : Subfunctor
    (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP) g).obj)
  (hAo : Space.IsOpenSubspace C S hS A)

/-- The inclusion of the open subscheme `Stacks.Groupoids.GroupoidScheme.arrowOpens` of the site
is an open immersion of schemes. -/
private theorem isOpenImmersion_toScheme_map_openSubHom_arrowOpens :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme C S hS).map (BigFppfOver.openSubHom C S hS
        (schemeSiteObject C hS hRA)
        (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo))) :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
    (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo).ι)

include he hAo in
/-- The image of the Yoneda image of the inclusion of the open subscheme
`Stacks.Groupoids.GroupoidScheme.arrowOpens` is the inverse image of the open subspace along
the comparison isomorphism. -/
private theorem range_yoneda_map_openSubHom_arrowOpens :
    Subfunctor.range (yoneda.map (BigFppfOver.openSubHom C S hS (schemeSiteObject C hS hRA)
        (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo))) =
      A.preimage (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom := by
  refine (range_yoneda_map_eq_subspaceOfOpens C S hS _
    (isOpenImmersion_toScheme_map_openSubHom_arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA
      A hAo) _
    (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo).range_ι).trans ?_
  exact subspaceOfOpens_opensOfOpenSubspace C S hS (schemeSiteObject C hS hRA)
    (A.preimage (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom)
    (isOpenSubspace_arrowsPreimage G C hS hU hR hP hX p U' g e he hA hB hRA A hAo)

include he hAo in
/-- **A projection of the restriction of the groupoid scheme is finite on the open subscheme
cut out by an open subspace on which the corresponding projection of the restricted realization
is finite.**  This is the common content of
`Stacks.Groupoids.GroupoidScheme.isFinite_arrowOpens_source` and
`isFinite_arrowOpens_target`; the hypothesis `hsp` is the de-realization of the projection. -/
private theorem isFinite_arrowOpens_comp (f : AlgebraicGeometry.restrictionArrows G p ⟶ X)
    (sp : (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP) g).obj ⟶
      U'.obj)
    (hsp : (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom ≫ sp =
      yoneda.map (schemeSiteMap C hS hRA hX f) ≫ e.hom)
    (hfin : Space.IsFinite C S hS (A.ι ≫ sp)) :
    AlgebraicGeometry.IsFinite
      ((arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo).ι ≫ f.left) := by
  have hcore := isFinite_yoneda_map_of_range_eq_preimage C S hS
    (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA) A sp
    (BigFppfOver.openSubHom C S hS (schemeSiteObject C hS hRA)
      (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo))
    (yoneda.map (schemeSiteMap C hS hRA hX f)) e hsp
    (isOpenImmersion_toScheme_map_openSubHom_arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA
      A hAo)
    (range_yoneda_map_openSubHom_arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo)
    hfin
  rw [← yoneda.map_comp] at hcore
  have hfinal := finite_of_isFinite_yoneda_map C S hS _ hcore
  have hopen := toScheme_map_openSubHom C S hS (schemeSiteObject C hS hRA)
    (arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo)
  rw [Functor.map_comp, hopen, toScheme_map_schemeSiteMap_eq] at hfinal
  exact hfinal

include he hAo in
/-- **The source of the restriction of the groupoid scheme is finite on the open subscheme cut
out by an open subspace on which the source of the restricted realization is finite.** -/
theorem isFinite_arrowOpens_source
    (hfin : Space.IsFinite C S hS
      (A.ι ≫ (GroupoidInAlgebraicSpaces.restrictionSource
        (G.realization C hS hU hR hP) g).hom)) :
    AlgebraicGeometry.IsFinite
      ((arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo).ι ≫
        (AlgebraicGeometry.restrictionSource G p).left) :=
  isFinite_arrowOpens_comp G C hS hU hR hP hX p U' g e he hA hB hRA A hAo
    (AlgebraicGeometry.restrictionSource G p) _
    (restrictionArrowsIsoOfIso_hom_comp_source G C hS hU hR hP hX p U' g e he hA hB hRA) hfin

include he hAo in
/-- **The target of the restriction of the groupoid scheme is finite on the open subscheme cut
out by an open subspace on which the target of the restricted realization is finite.** -/
theorem isFinite_arrowOpens_target
    (hfin : Space.IsFinite C S hS
      (A.ι ≫ (GroupoidInAlgebraicSpaces.restrictionTarget
        (G.realization C hS hU hR hP) g).hom)) :
    AlgebraicGeometry.IsFinite
      ((arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo).ι ≫
        (AlgebraicGeometry.restrictionTarget G p).left) :=
  isFinite_arrowOpens_comp G C hS hU hR hP hX p U' g e he hA hB hRA A hAo
    (AlgebraicGeometry.restrictionTarget G p) _
    (restrictionArrowsIsoOfIso_hom_comp_target G C hS hU hR hP hX p U' g e he hA hB hRA) hfin

end Stacks.Groupoids.GroupoidScheme

end
