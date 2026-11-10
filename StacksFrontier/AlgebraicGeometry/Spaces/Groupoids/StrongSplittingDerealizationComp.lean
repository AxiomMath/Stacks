module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable

/-!
# The open cut out by a splitting is closed under composition

Let `G` be a groupoid scheme over `S` whose object, arrow and composable-pair schemes a big
fppf site contains, let `p : X ⟶ U` be a morphism to its object scheme, and let `R'` realize the
restriction of the realization of `G` along `p`.  The arrows of an open finite subgroupoid of
`R'` cut out an open subscheme of the arrow scheme of the restriction of `G` itself, and that
open subscheme contains the composite of any composable pair of its points.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.splittingArrowHom`: a morphism from the composable pairs of
  the restriction of `G` to its arrow scheme, read as a morphism to the arrow space of a
  realization of the restriction of the realization of `G`.

## Main results

* `Stacks.Groupoids.GroupoidScheme.mem_arrows_of_forall_mem_splittingOpens`: a section of the
  arrow scheme of the restriction all of whose points lie in the open cut out by a splitting is
  a section of the arrows of that splitting.
* `Stacks.Groupoids.GroupoidScheme.splittingArrowHom_compose_eq`: the composite, in the realized
  restriction, of a composable pair of arrows of the restriction is their composite in the
  restriction of the groupoid scheme.
* `Stacks.Groupoids.GroupoidScheme.mem_splittingOpens_restrictionComposition`: the composite of a
  composable pair of arrows of the restriction, both of which lie in the open cut out by a
  splitting, lies in that open.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

noncomputable section

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
  (hCP : C.Contains (restrictionComposablePairs G p).left)
  (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
    (realizationMap G C hS hU hR hP hX p))
  (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid Rs.groupoid)

/-! ### Sections of the open cut out by a splitting -/

/-- A section of the arrow scheme of the restriction all of whose points lie in the open cut out
by a splitting lands in the arrows of that splitting. -/
theorem mem_arrows_of_forall_mem_splittingOpens {V : BigFppfOver C S hS}
    (a : V ⟶ schemeSiteObject C hS hRA)
    (ha : ∀ v, (BigFppfOver.toScheme C S hS).map a v ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) :
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom.app (Opposite.op V) a ∈
      P.arrows.obj (Opposite.op V) := by
  have hy : yonedaEquiv.symm
      (a : (yoneda.obj (schemeSiteObject C hS hRA)).obj (Opposite.op V)) = yoneda.map a := by
    refine yonedaEquiv.injective ?_
    rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
  have hmem : a ∈ (subspaceOfOpens C S hS (schemeSiteObject C hS hRA)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)).obj (Opposite.op V) := by
    refine (mem_openSubspaceOfPoints_iff C S hS
      (F := yoneda.obj (schemeSiteObject C hS hRA)) _ (X := Opposite.op V) a).2
      (Set.range_subset_iff.2 fun w => ?_)
    rw [Set.mem_preimage, hy, pointsToScheme_pointsMap_yoneda]
    exact ha _
  have heq : subspaceOfOpens C S hS (schemeSiteObject C hS hRA)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) =
      splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P :=
    subspaceOfOpens_opensOfOpenSubspace C S hS (schemeSiteObject C hS hRA)
      (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P)
      (isOpenSubspace_splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P)
  have hmem' : a ∈
      (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P).obj (Opposite.op V) :=
    heq ▸ hmem
  exact hmem'

/-! ### Arrows of the restriction, read in the realized restriction -/

/-- A morphism from the composable pairs of the restriction of a groupoid scheme to its arrow
scheme, read as a morphism to the arrow space of a realization of the restriction of the
realization. -/
def splittingArrowHom
    (f : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p) :
    yoneda.obj (schemeSiteObject C hS hCP) ⟶ Rs.groupoid.arrows.obj :=
  yoneda.map (schemeSiteMap C hS hCP hRA f) ≫
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom

/-- The source of such an arrow is the source of the morphism it comes from. -/
theorem splittingArrowHom_comp_source
    (f : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p) :
    splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs f ≫ Rs.groupoid.source.hom =
      yoneda.map (schemeSiteMap C hS hCP hX (f ≫ AlgebraicGeometry.restrictionSource G p)) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm := by
  change (yoneda.map (schemeSiteMap C hS hCP hRA f) ≫
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) ≫
      Rs.groupoid.source.hom = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => yoneda.map (schemeSiteMap C hS hCP hRA f) ≫ k)
    (restrictionArrowsSpaceIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA Rs)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg
    (fun k => k ≫ eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) ?_
  rw [← yoneda.map_comp, ← schemeSiteMap_comp]

/-- The target of such an arrow is the target of the morphism it comes from. -/
theorem splittingArrowHom_comp_target
    (f : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p) :
    splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs f ≫ Rs.groupoid.target.hom =
      yoneda.map (schemeSiteMap C hS hCP hX (f ≫ AlgebraicGeometry.restrictionTarget G p)) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm := by
  change (yoneda.map (schemeSiteMap C hS hCP hRA f) ≫
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) ≫
      Rs.groupoid.target.hom = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => yoneda.map (schemeSiteMap C hS hCP hRA f) ≫ k)
    (restrictionArrowsSpaceIso_hom_comp_target G C hS hU hR hP hX p hA hB hRA Rs)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg
    (fun k => k ≫ eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) ?_
  rw [← yoneda.map_comp, ← schemeSiteMap_comp]

/-- The ambient arrow underlying such an arrow is the underlying arrow of `G`. -/
theorem splittingArrowHom_comp_mapArrows
    (f : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p) :
    splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs f ≫
        Rs.hom.toGroupoidHom.mapArrows =
      yoneda.map (schemeSiteMap C hS hCP hR
        (f ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)) := by
  change (yoneda.map (schemeSiteMap C hS hCP hRA f) ≫
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) ≫
      Rs.hom.toGroupoidHom.mapArrows = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => yoneda.map (schemeSiteMap C hS hCP hRA f) ≫ k)
    (restrictionArrowsSpaceIso_hom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA Rs)).trans ?_
  exact (yoneda.map_comp (schemeSiteMap C hS hCP hRA f)
      (schemeSiteMap C hS hRA hR (AlgebraicGeometry.restrictionArrowsToArrows G p))).symm.trans
    (congrArg yoneda.map (schemeSiteMap_comp C hS hCP hRA hR f
      (AlgebraicGeometry.restrictionArrowsToArrows G p))).symm

/-! ### The composite of a composable pair -/

/-- The two projections of a composable pair of arrows of the restriction are composable in the
realized restriction. -/
theorem splittingArrowHom_composable (T : (BigFppfOver C S hS)ᵒᵖ)
    (y : (yoneda.obj (schemeSiteObject C hS hCP)).obj T) :
    Rs.groupoid.source.hom.app T
        ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
          (composablePairsFst G p)).app T y) =
      Rs.groupoid.target.hom.app T
        ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
          (composablePairsSnd G p)).app T y) := by
  have hsrc := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingArrowHom_comp_source G C hS hU hR hP hX p hA hB hRA hCP Rs
      (composablePairsFst G p)) T)
  have htgt := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingArrowHom_comp_target G C hS hU hR hP hX p hA hB hRA hCP Rs
      (composablePairsSnd G p)) T)
  refine hsrc.trans (Eq.trans ?_ htgt.symm)
  exact congrArg (fun k : restrictionComposablePairs G p ⟶ X =>
    (yoneda.map (schemeSiteMap C hS hCP hX k) ≫
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm).app T y)
    pullback.condition

/-- The composite in `G` of the two underlying arrows of a composable pair of arrows of a
restriction, read as a composite of generalized arrows. -/
theorem restrictionAmbientComp_eq_compose
    (w : (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.source =
      (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target) :
    G.compose (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
        (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) w =
      restrictionAmbientComp G p :=
  rfl

/-- **The composite of a composable pair of arrows of the restriction.**  Composing, in the
realized restriction, the two projections of a composable pair of arrows of the restriction of a
groupoid scheme gives the composite of the restriction at that pair. -/
theorem splittingArrowHom_compose_eq (T : (BigFppfOver C S hS)ᵒᵖ)
    (y : (yoneda.obj (schemeSiteObject C hS hCP)).obj T) :
    Rs.groupoid.toGroupoidInFunctors.compose T
        ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
          (composablePairsFst G p)).app T y)
        ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
          (composablePairsSnd G p)).app T y)
        (splittingArrowHom_composable G C hS hU hR hP hX p hA hB hRA hCP Rs T y) =
      (splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (restrictionComposition G p)).app T y := by
  have hfsrc := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingArrowHom_comp_source G C hS hU hR hP hX p hA hB hRA hCP Rs
      (composablePairsFst G p)) T)
  have hftgt := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingArrowHom_comp_target G C hS hU hR hP hX p hA hB hRA hCP Rs
      (composablePairsFst G p)) T)
  have hssrc := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingArrowHom_comp_source G C hS hU hR hP hX p hA hB hRA hCP Rs
      (composablePairsSnd G p)) T)
  have hcsrc := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingArrowHom_comp_source G C hS hU hR hP hX p hA hB hRA hCP Rs
      (restrictionComposition G p)) T)
  have hctgt := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingArrowHom_comp_target G C hS hU hR hP hX p hA hB hRA hCP Rs
      (restrictionComposition G p)) T)
  refine GroupoidInAlgebraicSpaces.restriction_arrow_ext (G.realization C hS hU hR hP) Rs T
    (Rs.groupoid.source.hom.app T
      ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsSnd G p)).app T y))
    (Rs.groupoid.target.hom.app T
      ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsFst G p)).app T y))
    _ _ ?_ ?_ ?_ ?_ ?_
  · exact Deformation.GroupoidInFunctors.compose_source Rs.groupoid.toGroupoidInFunctors T _ _ _
      ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsSnd G p)).app T y)
      ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsFst G p)).app T y)
      rfl rfl
      (splittingArrowHom_composable G C hS hU hR hP hX p hA hB hRA hCP Rs T y) rfl
  · exact Deformation.GroupoidInFunctors.compose_target Rs.groupoid.toGroupoidInFunctors T _ _ _
      ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsSnd G p)).app T y)
      ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsFst G p)).app T y)
      rfl rfl
      (splittingArrowHom_composable G C hS hU hR hP hX p hA hB hRA hCP Rs T y) rfl
  · refine hcsrc.trans (Eq.trans ?_ hssrc.symm)
    exact congrArg (fun k : restrictionComposablePairs G p ⟶ X =>
      (yoneda.map (schemeSiteMap C hS hCP hX k) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm).app T y)
      (restrictionComposition_comp_source G p)
  · refine hctgt.trans (Eq.trans ?_ hftgt.symm)
    exact congrArg (fun k : restrictionComposablePairs G p ⟶ X =>
      (yoneda.map (schemeSiteMap C hS hCP hX k) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm).app T y)
      (restrictionComposition_comp_target G p)
  · have hfarr := congrArg (fun k => k y) (NatTrans.congr_app
      (splittingArrowHom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsFst G p)) T)
    have hsarr := congrArg (fun k => k y) (NatTrans.congr_app
      (splittingArrowHom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA hCP Rs
        (composablePairsSnd G p)) T)
    have hcarr := congrArg (fun k => k y) (NatTrans.congr_app
      (splittingArrowHom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA hCP Rs
        (restrictionComposition G p)) T)
    have hf : yonedaSchemePointEquiv C hS hR T (Rs.hom.toGroupoidHom.mapArrows.app T
          ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
            (composablePairsFst G p)).app T y)) =
        yonedaSchemePointEquiv C hS hCP T y ≫
          (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) :=
      (congrArg (yonedaSchemePointEquiv C hS hR T) hfarr).trans
        (yonedaSchemePointEquiv_map C hS hCP hR
          (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) T y)
    have hs : yonedaSchemePointEquiv C hS hR T (Rs.hom.toGroupoidHom.mapArrows.app T
          ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
            (composablePairsSnd G p)).app T y)) =
        yonedaSchemePointEquiv C hS hCP T y ≫
          (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) :=
      (congrArg (yonedaSchemePointEquiv C hS hR T) hsarr).trans
        (yonedaSchemePointEquiv_map C hS hCP hR
          (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) T y)
    have hc : yonedaSchemePointEquiv C hS hR T (Rs.hom.toGroupoidHom.mapArrows.app T
          ((splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
            (restrictionComposition G p)).app T y)) =
        yonedaSchemePointEquiv C hS hCP T y ≫ restrictionAmbientComp G p :=
      (congrArg (yonedaSchemePointEquiv C hS hR T) hcarr).trans
        ((yonedaSchemePointEquiv_map C hS hCP hR
          (restrictionComposition G p ≫
            AlgebraicGeometry.restrictionArrowsToArrows G p) T y).trans
          (congrArg (fun k => yonedaSchemePointEquiv C hS hCP T y ≫ k)
            (restrictionComposition_comp_arrowsToArrows G p)))
    have w₀ : (composablePairsFst G p ≫
          AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.source =
        (composablePairsSnd G p ≫
          AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target := by
      rw [Category.assoc, Category.assoc,
        ← AlgebraicGeometry.GroupoidScheme.restriction_condition,
        AlgebraicGeometry.GroupoidScheme.restriction_condition',
        ← Category.assoc, ← Category.assoc, pullback.condition]
    have w₁ : (yonedaSchemePointEquiv C hS hCP T y ≫
          (composablePairsFst G p ≫
            AlgebraicGeometry.restrictionArrowsToArrows G p)) ≫ G.source =
        (yonedaSchemePointEquiv C hS hCP T y ≫
          (composablePairsSnd G p ≫
            AlgebraicGeometry.restrictionArrowsToArrows G p)) ≫ G.target :=
      (Category.assoc (yonedaSchemePointEquiv C hS hCP T y)
          (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
          G.source).trans
        ((congrArg (fun m => yonedaSchemePointEquiv C hS hCP T y ≫ m) w₀).trans
          (Category.assoc (yonedaSchemePointEquiv C hS hCP T y)
            (composablePairsSnd G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
            G.target).symm)
    refine Eq.trans (Rs.hom.toGroupoidHom.map_comp T _ _
      (splittingArrowHom_composable G C hS hU hR hP hX p hA hB hRA hCP Rs T y)).symm ?_
    refine (yonedaSchemePointEquiv C hS hR T).injective ?_
    refine (realizationComp_app G C hS hU hR hP T _ (by rw [hf, hs]; exact w₁)).trans ?_
    refine (AlgebraicGeometry.groupoidCompose_arrow_eq _ _ _ _ _ w₁ hf hs).trans ?_
    refine (AlgebraicGeometry.groupoidCompose_precomp G
      (yonedaSchemePointEquiv C hS hCP T y) _ _ w₀ w₁).trans ?_
    exact Eq.trans (congrArg (fun k => yonedaSchemePointEquiv C hS hCP T y ≫ k)
      (restrictionAmbientComp_eq_compose G p w₀)) hc.symm

/-! ### The open cut out by a splitting is closed under composition -/

include hCP in
/-- **The open cut out by a splitting is closed under composition.**  If both projections of a
composable pair of arrows of the restriction of a groupoid scheme lie in the open cut out by a
splitting, so does their composite. -/
theorem mem_splittingOpens_restrictionComposition (z : (restrictionComposablePairs G p).left)
    (h₁ : (composablePairsFst G p).left.base z ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)
    (h₂ : (composablePairsSnd G p).left.base z ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) :
    (restrictionComposition G p).left.base z ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := by
  obtain ⟨q, hq⟩ := exists_fieldValuedPoint_schemePoint_eq C S hS
    (schemeSiteObject C hS hCP) z
  have hsub : Subsingleton ((BigFppfOver.toScheme C S hS).obj q.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
  have hpt : ∀ (f : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p)
      (v : (BigFppfOver.toScheme C S hS).obj q.siteObject),
      (BigFppfOver.toScheme C S hS).map
          ((yoneda.map (schemeSiteMap C hS hCP hRA f)).app (Opposite.op q.siteObject) q.value) v =
        f.left.base z := by
    intro f v
    have hval : (yoneda.map (schemeSiteMap C hS hCP hRA f)).app
        (Opposite.op q.siteObject) q.value = q.value ≫ schemeSiteMap C hS hCP hRA f := rfl
    rw [hval, Functor.map_comp, toScheme_map_schemeSiteMap_eq]
    refine congrArg (fun t : (restrictionComposablePairs G p).left => f.left.base t) ?_
    refine Eq.trans ?_ hq
    exact congrArg (fun t => (BigFppfOver.toScheme C S hS).map q.value t)
      (@Subsingleton.elim _ hsub v (IsLocalRing.closedPoint q.carrier))
  have hmem : ∀ (f : restrictionComposablePairs G p ⟶ AlgebraicGeometry.restrictionArrows G p),
      f.left.base z ∈ splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P →
      (splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs f).app
          (Opposite.op q.siteObject) q.value ∈
        P.arrows.obj (Opposite.op q.siteObject) := by
    intro f hf
    refine mem_arrows_of_forall_mem_splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P
      ((yoneda.map (schemeSiteMap C hS hCP hRA f)).app (Opposite.op q.siteObject) q.value)
      (fun v => ?_)
    rw [hpt f v]
    exact hf
  have hcomp : (splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
      (restrictionComposition G p)).app (Opposite.op q.siteObject) q.value ∈
      P.arrows.obj (Opposite.op q.siteObject) := by
    have hc := P.comp_restricts (Opposite.op q.siteObject)
      ⟨(⟨(splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
            (composablePairsFst G p)).app (Opposite.op q.siteObject) q.value,
          hmem (composablePairsFst G p) h₁⟩,
        ⟨(splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
            (composablePairsSnd G p)).app (Opposite.op q.siteObject) q.value,
          hmem (composablePairsSnd G p) h₂⟩),
        splittingArrowHom_composable G C hS hU hR hP hX p hA hB hRA hCP Rs
          (Opposite.op q.siteObject) q.value⟩
    refine (hc.trans (splittingArrowHom_compose_eq G C hS hU hR hP hX p hA hB hRA hCP Rs
      (Opposite.op q.siteObject) q.value)) ▸ ?_
    exact (P.comp.app (Opposite.op q.siteObject) _).2
  have hrz : pointsToScheme C S hS (schemeSiteObject C hS hRA)
      (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hCP))
        (yoneda.map (schemeSiteMap C hS hCP hRA (restrictionComposition G p)))
        (q.class C S hS (yoneda.obj (schemeSiteObject C hS hCP)))) =
      (restrictionComposition G p).left.base z := by
    rw [pointsToScheme_pointsMap_yoneda, toScheme_map_schemeSiteMap_eq]
    exact congrArg (fun t : (restrictionComposablePairs G p).left =>
      (restrictionComposition G p).left.base t) hq
  refine (mem_splittingOpens_iff_of_eq G C hS hU hR hP hX p hA hB hRA Rs P hrz).2 ?_
  have hsplit : splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
      (restrictionComposition G p) =
      yoneda.map (schemeSiteMap C hS hCP hRA (restrictionComposition G p)) ≫
        (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom := rfl
  have hmove : pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
      (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hCP))
        (yoneda.map (schemeSiteMap C hS hCP hRA (restrictionComposition G p)))
        (q.class C S hS (yoneda.obj (schemeSiteObject C hS hCP)))) =
      pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hCP))
        (splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
          (restrictionComposition G p))
        (q.class C S hS (yoneda.obj (schemeSiteObject C hS hCP))) := by
    rw [hsplit, pointsMap_comp]
    rfl
  rw [hmove]
  exact ⟨Space.FieldValuedPoint.class C S hS P.arrows.toFunctor
    { carrier := q.carrier, field := q.field, contained := q.contained, toBase := q.toBase,
      value := ⟨(splittingArrowHom G C hS hU hR hP hX p hA hB hRA hCP Rs
        (restrictionComposition G p)).app (Opposite.op q.siteObject) q.value, hcomp⟩ }, rfl⟩

end Stacks.Groupoids.GroupoidScheme

end

end
