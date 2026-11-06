module

public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantOpenSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# The open subscheme cut out by a splitting of a restricted realization

Let `G` be a groupoid scheme over `S` whose object, arrow and composable-pair schemes a big
fppf site contains, let `p : X ⟶ U` be a morphism to its object scheme, and let `R'` realize the
restriction of the realization of `G` along `p`.  An open finite subgroupoid of `R'` is an open
subspace of its arrow space; since that arrow space is the space represented by the arrow scheme
`AlgebraicGeometry.restrictionArrows G p` of the restriction of `G` itself, the open subspace is
an open subscheme of that arrow scheme.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.restrictionArrowsSpaceIso`: the identification of the space
  represented by the arrow scheme of the restriction of `G` with the arrow space of a
  realization of the restriction of the realization of `G`.
* `Stacks.Groupoids.GroupoidScheme.splittingOpens`: the open of the arrow scheme of the
  restriction of `G` cut out by the arrows of an open finite subgroupoid.

## Main results

* `Stacks.Groupoids.GroupoidScheme.realization_identity_eq`: the identity arrow of the pointwise
  groupoid of a realization at a generalized point is the identity arrow of the groupoid scheme
  there.  The pointwise groupoid of a realization is chosen by `Classical.choice`, so its
  identity arrow is opaque and has to be recognised by idempotence.
* `Stacks.Groupoids.GroupoidScheme.mem_splittingOpens_iff`: a point of the arrow scheme of the
  restriction lies in that open exactly when the corresponding point of the arrow space lies in
  the arrows of the subgroupoid.
* `Stacks.Groupoids.GroupoidScheme.mem_splittingOpens_restrictionIdentity`: the identity arrow of
  the restriction of the groupoid scheme lies in that open, at every point.

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

/-! ### The identity arrow of a realization -/

/-- The composite of the identity arrow at a generalized point of a groupoid scheme with itself
is that identity arrow. -/
theorem compose_identity_self {T : Over S} (q : T ⟶ G.objects)
    (w : (q ≫ G.identity) ≫ G.source = (q ≫ G.identity) ≫ G.target) :
    G.compose (q ≫ G.identity) (q ≫ G.identity) w = q ≫ G.identity := by
  have hfix : (q ≫ G.identity) ≫ G.target ≫ G.identity = q ≫ G.identity := by
    rw [← Category.assoc, Category.assoc q G.identity G.target, G.target_identity,
      Category.comp_id]
  have hts : (G.target ≫ G.identity) ≫ G.source = G.target :=
    (Category.assoc G.target G.identity G.source).trans
      ((congrArg (fun k => G.target ≫ k) G.source_identity).trans (Category.comp_id G.target))
  have hli := G.left_identity T (q ≫ G.identity)
    ((Category.assoc (q ≫ G.identity) (G.target ≫ G.identity) G.source).trans
      (congrArg (fun k => (q ≫ G.identity) ≫ k) hts))
  rw [GroupoidScheme.compose]
  refine Eq.trans ?_ hli
  refine congrArg (fun k => k ≫ G.comp) (pullback.hom_ext ?_ ?_)
  · exact (pullback.lift_fst _ _ _).trans ((pullback.lift_fst _ _ _).trans hfix).symm
  · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- **The identity arrow of a realization.**  A generalized arrow of the realization of a
groupoid scheme whose generalized point is the identity arrow at a generalized point of the
object scheme is the identity arrow of the pointwise groupoid there.

The pointwise groupoid of a realization is produced by `Classical.choice`, so its identity arrow
is opaque; it is recognised instead by having equal source and target and being idempotent, which
is `Deformation.GroupoidInFunctors.identity_eq_of_idempotent`. -/
theorem realization_identity_eq (T : (BigFppfOver C S hS)ᵒᵖ)
    (y : (G.realization C hS hU hR hP).toGroupoidInFunctors.Evaluation T)
    (a : (G.realization C hS hU hR hP).arrows.obj.obj T)
    (hpt : yonedaSchemePointEquiv C hS hR T a =
      yonedaSchemePointEquiv C hS hU T y ≫ G.identity) :
    (G.realization C hS hU hR hP).toGroupoidInFunctors.identity T y = a := by
  have hs : (G.realization C hS hU hR hP).toGroupoidInFunctors.source.app T a = y := by
    refine (yonedaSchemePointEquiv C hS hU T).injective ?_
    refine (yonedaSchemePointEquiv_map C hS hR hU G.source T a).trans ?_
    rw [hpt, Category.assoc, G.source_identity, Category.comp_id]
  have ht : (G.realization C hS hU hR hP).toGroupoidInFunctors.target.app T a = y := by
    refine (yonedaSchemePointEquiv C hS hU T).injective ?_
    refine (yonedaSchemePointEquiv_map C hS hR hU G.target T a).trans ?_
    rw [hpt, Category.assoc, G.target_identity, Category.comp_id]
  refine Deformation.GroupoidInFunctors.identity_eq_of_idempotent
    (G.realization C hS hU hR hP).toGroupoidInFunctors T y a hs ht ?_
  refine (yonedaSchemePointEquiv C hS hR T).injective ?_
  refine (realizationComp_app G C hS hU hR hP T ⟨(a, a), hs.trans ht.symm⟩
    (by rw [hpt, Category.assoc, Category.assoc, G.source_identity, G.target_identity])).trans ?_
  refine Eq.trans (AlgebraicGeometry.groupoidCompose_arrow_eq
    (yonedaSchemePointEquiv C hS hR T a) (yonedaSchemePointEquiv C hS hU T y ≫ G.identity)
    (yonedaSchemePointEquiv C hS hR T a) (yonedaSchemePointEquiv C hS hU T y ≫ G.identity)
    _ (by rw [Category.assoc, Category.assoc, G.source_identity, G.target_identity])
    hpt hpt) ?_
  exact (compose_identity_self G (yonedaSchemePointEquiv C hS hU T y) _).trans hpt.symm

/-! ### The arrow space of a realized restriction -/

/-- Transporting the codomain of an isomorphism along an equality.  Stated with every object a
variable, so that the equality may be given between two presentations of the codomain which are
definitionally but not syntactically equal. -/
def isoTransEqToHom {D : Type*} [Category D] {A B K : D} (i : A ≅ B) (h : B = K) : A ≅ K :=
  i ≪≫ eqToIso h

/-- The underlying presheaf of a transport along an equality of algebraic spaces is the transport
along the corresponding equality of presheaves. -/
theorem hom_eqToHom {A B : AlgebraicSpaces C S hS} (h : A = B) :
    (eqToHom h).hom = eqToHom (congrArg (fun a : AlgebraicSpaces C S hS => a.obj) h) := by
  subst h
  rfl

/-- The arrow space of a realization of a restriction is the presheaf represented by the arrow
scheme of the restriction. -/
theorem restrictionArrowsObj_eq
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).obj = Rs.groupoid.arrows.obj :=
  (congrArg (fun a : AlgebraicSpaces C S hS => a.obj) Rs.arrows_eq).symm

/-- The space represented by the arrow scheme of the restriction of a groupoid scheme is the
arrow space of a realization of the restriction of its realization. -/
def restrictionArrowsSpaceIso
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    yoneda.obj (schemeSiteObject C hS hRA) ≅ Rs.groupoid.arrows.obj :=
  isoTransEqToHom (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA)
    (restrictionArrowsObj_eq G C hS hU hR hP hX p Rs)

/-- The identification of arrow spaces is the realization isomorphism followed by the transport
along the equality of arrow presheaves. -/
theorem restrictionArrowsSpaceIso_hom
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom =
      (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫
        eqToHom (restrictionArrowsObj_eq G C hS hU hR hP hX p Rs) :=
  rfl

/-- The object space of a realization of a restriction is the presheaf represented by the scheme
being restricted to. -/
theorem restrictionObjectsObj_eq
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    Rs.groupoid.objects.obj = yoneda.obj (schemeSiteObject C hS hX) :=
  congrArg (fun a : AlgebraicSpaces C S hS => a.obj) Rs.objects_eq

/-- Composing the identification of arrow spaces with a morphism transported along the equality of
arrow presheaves is the realization isomorphism followed by that morphism. -/
theorem restrictionArrowsSpaceIso_hom_comp_eqToHom_symm_comp
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) {Z}
    (F : (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)).obj ⟶ Z) {g}
    (hF : (restrictionArrowsRealizationIso G C hS hU hR hX p hA hB hRA).hom ≫ F = g) :
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
      (eqToHom (restrictionArrowsObj_eq G C hS hU hR hP hX p Rs).symm ≫ F) = g := by
  rw [restrictionArrowsSpaceIso_hom, Category.assoc]
  erw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact hF

/-- The identification carries the morphism to the ambient arrow space to the Yoneda image of the
projection of arrow schemes. -/
theorem restrictionArrowsSpaceIso_hom_comp_mapArrows
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        Rs.hom.toGroupoidHom.mapArrows =
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p)) := by
  have harr : Rs.hom.toGroupoidHom.mapArrows =
      eqToHom (restrictionArrowsObj_eq G C hS hU hR hP hX p Rs).symm ≫
        (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
          (realizationMap G C hS hU hR hP hX p)).hom := by
    refine Rs.mapArrows_eq.trans ?_
    show (eqToHom Rs.arrows_eq).hom ≫
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom = _
    rw [hom_eqToHom]
  rw [harr]
  exact restrictionArrowsSpaceIso_hom_comp_eqToHom_symm_comp G C hS hU hR hP hX p hA hB hRA Rs _
    (restrictionArrowsRealizationIso_hom_comp_arrowsToArrows G C hS hU hR hP hX p hA hB hRA)

/-- The identification carries the source to the Yoneda image of the source of the restriction of
the groupoid scheme. -/
theorem restrictionArrowsSpaceIso_hom_comp_source
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        Rs.groupoid.source.hom =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm := by
  have hsrc : Rs.groupoid.source.hom =
      eqToHom (restrictionArrowsObj_eq G C hS hU hR hP hX p Rs).symm ≫
        ((GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
            (realizationMap G C hS hU hR hP hX p)).hom ≫
          eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) := by
    refine (congrArg (fun f : Rs.groupoid.arrows ⟶ Rs.groupoid.objects => f.hom)
      Rs.source_eq).trans ?_
    show (eqToHom Rs.arrows_eq).hom ≫
      (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom ≫
        (eqToHom Rs.objects_eq.symm).hom = _
    rw [hom_eqToHom, hom_eqToHom]
  rw [hsrc]
  refine restrictionArrowsSpaceIso_hom_comp_eqToHom_symm_comp G C hS hU hR hP hX p hA hB hRA Rs _
    ?_
  erw [← Category.assoc, restrictionArrowsRealizationIso_hom_comp_source]

/-- The identification carries the target to the Yoneda image of the target of the restriction of
the groupoid scheme. -/
theorem restrictionArrowsSpaceIso_hom_comp_target
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        Rs.groupoid.target.hom =
      yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p)) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm := by
  have htgt : Rs.groupoid.target.hom =
      eqToHom (restrictionArrowsObj_eq G C hS hU hR hP hX p Rs).symm ≫
        ((GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
            (realizationMap G C hS hU hR hP hX p)).hom ≫
          eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) := by
    refine (congrArg (fun f : Rs.groupoid.arrows ⟶ Rs.groupoid.objects => f.hom)
      Rs.target_eq).trans ?_
    show (eqToHom Rs.arrows_eq).hom ≫
      (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hX p)).hom ≫
        (eqToHom Rs.objects_eq.symm).hom = _
    rw [hom_eqToHom, hom_eqToHom]
  rw [htgt]
  refine restrictionArrowsSpaceIso_hom_comp_eqToHom_symm_comp G C hS hU hR hP hX p hA hB hRA Rs _
    ?_
  erw [← Category.assoc, restrictionArrowsRealizationIso_hom_comp_target]

/-- The object identification carries the morphism to the ambient object space to the Yoneda
image of the restricting morphism. -/
theorem restrictionObjectsObj_eq_symm_comp_mapObjects
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p)) :
    eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm ≫
        Rs.hom.toGroupoidHom.mapObjects =
      yoneda.map (schemeSiteMap C hS hX hU p) := by
  have hcancel : eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm ≫
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs) =
      𝟙 (yoneda.obj (schemeSiteObject C hS hX)) := by
    rw [eqToHom_trans, eqToHom_refl]
  have hobj : Rs.hom.toGroupoidHom.mapObjects =
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs) ≫
        yoneda.map (schemeSiteMap C hS hX hU p) := by
    refine Rs.mapObjects_eq.trans ?_
    show (eqToHom Rs.objects_eq).hom ≫ yoneda.map (schemeSiteMap C hS hX hU p) = _
    rw [hom_eqToHom]
  rw [hobj]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ yoneda.map (schemeSiteMap C hS hX hU p)) hcancel).trans ?_
  exact Category.id_comp _

variable (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
    (realizationMap G C hS hU hR hP hX p))
  (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid Rs.groupoid)

/-- The arrows of an open finite subgroupoid of a realized restriction, read as an open subspace
of the space represented by the arrow scheme of the restriction of the groupoid scheme. -/
def splittingSubfunctor : Subfunctor (yoneda.obj (schemeSiteObject C hS hRA)) :=
  P.arrows.preimage (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom

/-- The subfunctor cut out by an open finite subgroupoid is an open subspace. -/
theorem isOpenSubspace_splittingSubfunctor :
    IsOpenSubspace C S hS (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P) :=
  isOpenSubspace_preimage C S hS _ _ Rs.groupoid.arrows.2
    (isAlgebraicSpace_yoneda C S hS _) P.arrows_open

/-- **The open of the arrow scheme cut out by a splitting.** -/
def splittingOpens : (AlgebraicGeometry.restrictionArrows G p).left.Opens :=
  opensOfOpenSubspace C S hS (schemeSiteObject C hS hRA)
    (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P)
    (isOpenSubspace_splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P)

/-- **Membership in the open cut out by a splitting.**  A point of the arrow scheme of the
restriction lies in that open exactly when the corresponding point of the arrow space lies in the
arrows of the subgroupoid. -/
theorem mem_splittingOpens_iff
    (x : Space.points C S hS (yoneda.obj (schemeSiteObject C hS hRA))) :
    pointsToScheme C S hS (schemeSiteObject C hS hRA) x ∈
        splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P ↔
      pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom x ∈
        Set.range (pointsMap C S hS P.arrows.toFunctor P.arrows.ι) :=
  (mem_opensOfOpenSubspace C hS (schemeSiteObject C hS hRA)
      (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P)
      (isOpenSubspace_splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P) x).trans
    (mem_pointsRange_preimage_iff C S hS
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom P.arrows x)

/-- Transporting a point of a scheme of the site to a point of the space it represents and back
again returns the point. -/
theorem pointsToScheme_pointsEquivScheme_symm (V : BigFppfOver C S hS)
    (r : (BigFppfOver.toScheme C S hS).obj V) :
    pointsToScheme C S hS V ((pointsEquivScheme C S hS V).symm r) = r :=
  (pointsEquivScheme C S hS V).apply_symm_apply r

/-- `Stacks.Groupoids.GroupoidScheme.mem_splittingOpens_iff` read at a point of the arrow scheme
presented as the scheme point of a point of the arrow space. -/
theorem mem_splittingOpens_iff_of_eq
    {x : Space.points C S hS (yoneda.obj (schemeSiteObject C hS hRA))}
    {r : (AlgebraicGeometry.restrictionArrows G p).left}
    (hr : pointsToScheme C S hS (schemeSiteObject C hS hRA) x = r) :
    r ∈ splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P ↔
      pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom x ∈
        Set.range (pointsMap C S hS P.arrows.toFunctor P.arrows.ι) := by
  subst hr
  exact mem_splittingOpens_iff G C hS hU hR hP hX p hA hB hRA Rs P x


/-! ### The identity arrow of the restriction lies in the splitting -/

/-- Regarding the identity morphism of a scheme over `S` in the site gives the identity. -/
theorem schemeSiteMap_id {Y : Over S} (hY : C.Contains Y.left) :
    schemeSiteMap C hS hY hY (𝟙 Y) = 𝟙 (schemeSiteObject C hS hY) := by
  apply Over.OverMorphism.ext
  rfl

/-- The identity arrow of the restriction of a groupoid scheme, read as a morphism to the arrow
space of a realization of the restriction of its realization. -/
def splittingIdentityHom : yoneda.obj (schemeSiteObject C hS hX) ⟶ Rs.groupoid.arrows.obj :=
  yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)) ≫
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom

/-- The de-realized identity arrow followed by a structure map of the realized restriction is the
point itself, once the corresponding structure map of the restriction of the groupoid scheme
retracts the identity arrow. -/
private theorem splittingIdentityHom_comp_eq_eqToHom
    (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hX p))
    (f : (AlgebraicGeometry.restrictionArrows G p) ⟶ X) (hf : restrictionIdentity G p ≫ f = 𝟙 X)
    (k : Rs.groupoid.arrows.obj ⟶ Rs.groupoid.objects.obj)
    (hk : (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫ k =
      yoneda.map (schemeSiteMap C hS hRA hX f) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) :
    splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs ≫ k =
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm := by
  have hid : yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)) ≫
      yoneda.map (schemeSiteMap C hS hRA hX f) = 𝟙 (yoneda.obj (schemeSiteObject C hS hX)) := by
    rw [← yoneda.map_comp, ← schemeSiteMap_comp, hf, schemeSiteMap_id, yoneda.map_id]
  rw [splittingIdentityHom, Category.assoc, hk, ← Category.assoc, hid, Category.id_comp]

/-- The source of the de-realized identity arrow is the point itself. -/
theorem splittingIdentityHom_comp_source :
    splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs ≫ Rs.groupoid.source.hom =
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm :=
  splittingIdentityHom_comp_eq_eqToHom G C hS hU hR hP hX p hA hB hRA Rs _
    (restrictionIdentity_comp_source G p) _
    (restrictionArrowsSpaceIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA Rs)

/-- The target of the de-realized identity arrow is the point itself. -/
theorem splittingIdentityHom_comp_target :
    splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs ≫ Rs.groupoid.target.hom =
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm :=
  splittingIdentityHom_comp_eq_eqToHom G C hS hU hR hP hX p hA hB hRA Rs _
    (restrictionIdentity_comp_target G p) _
    (restrictionArrowsSpaceIso_hom_comp_target G C hS hU hR hP hX p hA hB hRA Rs)

/-- The ambient arrow underlying the de-realized identity arrow is the identity arrow of the
groupoid scheme at the image of the point. -/
theorem splittingIdentityHom_comp_mapArrows :
    splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs ≫ Rs.hom.toGroupoidHom.mapArrows =
      yoneda.map (schemeSiteMap C hS hX hR (p ≫ G.identity)) := by
  have hcomp : yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)) ≫
      yoneda.map (schemeSiteMap C hS hRA hR
        (AlgebraicGeometry.restrictionArrowsToArrows G p)) =
      yoneda.map (schemeSiteMap C hS hX hR (p ≫ G.identity)) := by
    rw [← yoneda.map_comp, ← schemeSiteMap_comp, restrictionIdentity_comp_arrowsToArrows]
  show (yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)) ≫
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) ≫
      Rs.hom.toGroupoidHom.mapArrows = _
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun k =>
    yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)) ≫ k)
    (restrictionArrowsSpaceIso_hom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA Rs)).trans hcomp

/-- **The de-realized identity arrow is the identity arrow of the realized restriction.** -/
theorem splittingIdentityHom_app_eq (T : (BigFppfOver C S hS)ᵒᵖ)
    (y : (yoneda.obj (schemeSiteObject C hS hX)).obj T) :
    Rs.groupoid.toGroupoidInFunctors.identity T
        ((eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm).app T y) =
      (splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs).app T y := by
  have hsrc := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingIdentityHom_comp_source G C hS hU hR hP hX p hA hB hRA Rs) T)
  have htgt := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingIdentityHom_comp_target G C hS hU hR hP hX p hA hB hRA Rs) T)
  have harr := congrArg (fun k => k y) (NatTrans.congr_app
    (splittingIdentityHom_comp_mapArrows G C hS hU hR hP hX p hA hB hRA Rs) T)
  have hobj := congrArg (fun k => k y) (NatTrans.congr_app
    (restrictionObjectsObj_eq_symm_comp_mapObjects G C hS hU hR hP hX p Rs) T)
  refine GroupoidInAlgebraicSpaces.restriction_identity_eq (G.realization C hS hU hR hP) Rs T
    ((eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm).app T y)
    ((splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs).app T y) hsrc htgt ?_
  refine Eq.symm (realization_identity_eq G C hS hU hR hP T _ _ ?_)
  exact (congrArg (yonedaSchemePointEquiv C hS hR T) harr).trans
    ((yonedaSchemePointEquiv_map C hS hX hR (p ≫ G.identity) T y).trans
      ((Category.assoc (yonedaSchemePointEquiv C hS hX T y) p G.identity).symm.trans
        (congrArg (fun k => k ≫ G.identity)
          (((congrArg (yonedaSchemePointEquiv C hS hU T) hobj).trans
            (yonedaSchemePointEquiv_map C hS hX hU p T y)).symm))))

/-- The point of the arrow space carried by the de-realized identity arrow is the identity arrow
at the point of the object space. -/
theorem pointsMap_splittingIdentityHom
    (w : Space.points C S hS (yoneda.obj (schemeSiteObject C hS hX))) :
    pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hX))
        (splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs) w =
      GroupoidInAlgebraicSpaces.identityOnPoints Rs.groupoid
        (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hX))
          (eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) w) := by
  induction w using Quot.ind with | _ q =>
  refine congrArg (fun v => Space.FieldValuedPoint.class C S hS Rs.groupoid.arrows.obj
    { carrier := q.carrier, field := q.field, contained := q.contained, toBase := q.toBase,
      value := v }) ?_
  exact (splittingIdentityHom_app_eq G C hS hU hR hP hX p hA hB hRA Rs
    (Opposite.op q.siteObject) q.value).symm

/-- **The identity arrow of the restriction lies in the open cut out by a splitting.** -/
theorem mem_splittingOpens_restrictionIdentity (z : X.left) :
    (restrictionIdentity G p).left.base z ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := by
  have hrz : pointsToScheme C S hS (schemeSiteObject C hS hRA)
      (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hX))
        (yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)))
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hX)).symm z)) =
      (restrictionIdentity G p).left.base z := by
    have hz : pointsToScheme C S hS (schemeSiteObject C hS hX)
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hX)).symm z) = z :=
      pointsToScheme_pointsEquivScheme_symm C hS (schemeSiteObject C hS hX) z
    rw [pointsToScheme_pointsMap_yoneda, toScheme_map_schemeSiteMap_eq]
    exact congrArg (fun t : X.left => (restrictionIdentity G p).left.base t) hz
  refine (mem_splittingOpens_iff_of_eq G C hS hU hR hP hX p hA hB hRA Rs P hrz).2 ?_
  have hsplit : splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs =
      yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)) ≫
        (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom := rfl
  have hcomp : pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
      (pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hX))
        (yoneda.map (schemeSiteMap C hS hX hRA (restrictionIdentity G p)))
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hX)).symm z)) =
      pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hX))
        (splittingIdentityHom G C hS hU hR hP hX p hA hB hRA Rs)
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hX)).symm z) := by
    rw [hsplit, pointsMap_comp]
    rfl
  rw [hcomp, pointsMap_splittingIdentityHom]
  exact GroupoidInAlgebraicSpaces.contains_identityOnPoints_of_openFiniteSubgroupoid
    Rs.groupoid P _

end Stacks.Groupoids.GroupoidScheme

end

end
